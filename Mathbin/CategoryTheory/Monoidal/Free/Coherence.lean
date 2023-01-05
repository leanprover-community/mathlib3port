/-
Copyright (c) 2021 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel

! This file was ported from Lean 3 source module category_theory.monoidal.free.coherence
! leanprover-community/mathlib commit 6d0adfa76594f304b4650d098273d4366edeb61b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Monoidal.Free.Basic
import Mathbin.CategoryTheory.Groupoid
import Mathbin.CategoryTheory.DiscreteCategory

/-!
# The monoidal coherence theorem

In this file, we prove the monoidal coherence theorem, stated in the following form: the free
monoidal category over any type `C` is thin.

We follow a proof described by Ilya Beylin and Peter Dybjer, which has been previously formalized
in the proof assistant ALF. The idea is to declare a normal form (with regard to association and
adding units) on objects of the free monoidal category and consider the discrete subcategory of
objects that are in normal form. A normalization procedure is then just a functor
`full_normalize : free_monoidal_category C ⥤ discrete (normal_monoidal_object C)`, where
functoriality says that two objects which are related by associators and unitors have the
same normal form. Another desirable property of a normalization procedure is that an object is
isomorphic (i.e., related via associators and unitors) to its normal form. In the case of the
specific normalization procedure we use we not only get these isomorphismns, but also that they
assemble into a natural isomorphism `𝟭 (free_monoidal_category C) ≅ full_normalize ⋙ inclusion`.
But this means that any two parallel morphisms in the free monoidal category factor through a
discrete category in the same way, so they must be equal, and hence the free monoidal category
is thin.

## References

* [Ilya Beylin and Peter Dybjer, Extracting a proof of coherence for monoidal categories from a
   proof of normalization for monoids][beylin1996]

-/


universe u

namespace CategoryTheory

open MonoidalCategory

namespace FreeMonoidalCategory

variable {C : Type u}

section

variable (C)

/-- We say an object in the free monoidal category is in normal form if it is of the form
    `(((𝟙_ C) ⊗ X₁) ⊗ X₂) ⊗ ⋯`. -/
@[nolint has_nonempty_instance]
inductive NormalMonoidalObject : Type u
  | Unit : normal_monoidal_object
  | tensor : normal_monoidal_object → C → normal_monoidal_object
#align
  category_theory.free_monoidal_category.normal_monoidal_object CategoryTheory.FreeMonoidalCategory.NormalMonoidalObject

end

-- mathport name: exprF
local notation "F" => FreeMonoidalCategory

-- mathport name: exprN
local notation "N" => discrete ∘ normal_monoidal_object

-- mathport name: «expr ⟶ᵐ »
local infixr:10 " ⟶ᵐ " => Hom

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment "/--" "Auxiliary definition for `inclusion`. -/")]
      [(Term.attributes "@[" [(Term.attrInstance (Term.attrKind []) (Attr.simp "simp" [] []))] "]")]
      []
      []
      []
      [])
     (Command.def
      "def"
      (Command.declId `inclusionObj [])
      (Command.optDeclSig
       []
       [(Term.typeSpec
         ":"
         (Term.arrow
          (Term.app `NormalMonoidalObject [`C])
          "→"
          (Term.app
           (CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termF "F")
           [`C])))])
      (Command.declValEqns
       (Term.matchAltsWhereDecls
        (Term.matchAlts
         [(Term.matchAlt "|" [[`normal_monoidal_object.unit]] "=>" `unit)
          (Term.matchAlt
           "|"
           [[(Term.app `normal_monoidal_object.tensor [`n `a])]]
           "=>"
           (Term.app `tensor [(Term.app `inclusion_obj [`n]) (Term.app `of [`a])]))])
        []))
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValEqns', expected 'Lean.Parser.Command.declValSimple'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `tensor [(Term.app `inclusion_obj [`n]) (Term.app `of [`a])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `of [`a])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `of
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `of [`a]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `inclusion_obj [`n])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `inclusion_obj
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `inclusion_obj [`n]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `tensor
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `normal_monoidal_object.tensor [`n `a])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `normal_monoidal_object.tensor
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      `unit
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `normal_monoidal_object.unit
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.arrow
       (Term.app `NormalMonoidalObject [`C])
       "→"
       (Term.app
        (CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termF "F")
        [`C]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termF "F")
       [`C])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `C
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termF "F")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termF', expected 'CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termF._@.CategoryTheory.Monoidal.Free.Coherence._hyg.10'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/-- Auxiliary definition for `inclusion`. -/ @[ simp ]
  def
    inclusionObj
    : NormalMonoidalObject C → F C
    | normal_monoidal_object.unit => unit
      | normal_monoidal_object.tensor n a => tensor inclusion_obj n of a
#align
  category_theory.free_monoidal_category.inclusion_obj CategoryTheory.FreeMonoidalCategory.inclusionObj

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "The discrete subcategory of objects in normal form includes into the free monoidal category. -/")]
      [(Term.attributes "@[" [(Term.attrInstance (Term.attrKind []) (Attr.simp "simp" [] []))] "]")]
      []
      []
      []
      [])
     (Command.def
      "def"
      (Command.declId `inclusion [])
      (Command.optDeclSig
       []
       [(Term.typeSpec
         ":"
         (CategoryTheory.CategoryTheory.Functor.Basic.«term_⥤_»
          (Term.app
           (CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termN "N")
           [`C])
          " ⥤ "
          (Term.app
           (CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termF "F")
           [`C])))])
      (Command.declValSimple ":=" (Term.app `Discrete.functor [`inclusionObj]) [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Discrete.functor [`inclusionObj])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `inclusionObj
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Discrete.functor
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (CategoryTheory.CategoryTheory.Functor.Basic.«term_⥤_»
       (Term.app
        (CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termN "N")
        [`C])
       " ⥤ "
       (Term.app
        (CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termF "F")
        [`C]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termF "F")
       [`C])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `C
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termF "F")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termF', expected 'CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termF._@.CategoryTheory.Monoidal.Free.Coherence._hyg.10'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/-- The discrete subcategory of objects in normal form includes into the free monoidal category. -/
    @[ simp ]
  def inclusion : N C ⥤ F C := Discrete.functor inclusionObj
#align
  category_theory.free_monoidal_category.inclusion CategoryTheory.FreeMonoidalCategory.inclusion

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment "/--" "Auxiliary definition for `normalize`. -/")]
      [(Term.attributes "@[" [(Term.attrInstance (Term.attrKind []) (Attr.simp "simp" [] []))] "]")]
      []
      []
      []
      [])
     (Command.def
      "def"
      (Command.declId `normalizeObj [])
      (Command.optDeclSig
       []
       [(Term.typeSpec
         ":"
         (Term.arrow
          (Term.app
           (CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termF "F")
           [`C])
          "→"
          (Term.arrow
           (Term.app `NormalMonoidalObject [`C])
           "→"
           (Term.app
            (CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termN "N")
            [`C]))))])
      (Command.declValEqns
       (Term.matchAltsWhereDecls
        (Term.matchAlts
         [(Term.matchAlt "|" [[`Unit "," `n]] "=>" (Term.anonymousCtor "⟨" [`n] "⟩"))
          (Term.matchAlt
           "|"
           [[(Term.app `of [`X]) "," `n]]
           "=>"
           (Term.anonymousCtor "⟨" [(Term.app `NormalMonoidalObject.tensor [`n `X])] "⟩"))
          (Term.matchAlt
           "|"
           [[(Term.app `tensor [`X `Y]) "," `n]]
           "=>"
           (Term.app `normalize_obj [`Y (Term.proj (Term.app `normalize_obj [`X `n]) "." `as)]))])
        []))
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValEqns', expected 'Lean.Parser.Command.declValSimple'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `normalize_obj [`Y (Term.proj (Term.app `normalize_obj [`X `n]) "." `as)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.app `normalize_obj [`X `n]) "." `as)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `normalize_obj [`X `n])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `X
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `normalize_obj
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `normalize_obj [`X `n]) ")")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `Y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `normalize_obj
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `tensor [`X `Y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `X
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `tensor
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.anonymousCtor "⟨" [(Term.app `NormalMonoidalObject.tensor [`n `X])] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `NormalMonoidalObject.tensor [`n `X])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `X
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `NormalMonoidalObject.tensor
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `of [`X])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `X
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `of
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.anonymousCtor "⟨" [`n] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Unit
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.arrow
       (Term.app
        (CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termF "F")
        [`C])
       "→"
       (Term.arrow
        (Term.app `NormalMonoidalObject [`C])
        "→"
        (Term.app
         (CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termN "N")
         [`C])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.arrow
       (Term.app `NormalMonoidalObject [`C])
       "→"
       (Term.app
        (CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termN "N")
        [`C]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termN "N")
       [`C])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `C
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termN "N")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termN', expected 'CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termN._@.CategoryTheory.Monoidal.Free.Coherence._hyg.357'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/-- Auxiliary definition for `normalize`. -/ @[ simp ]
  def
    normalizeObj
    : F C → NormalMonoidalObject C → N C
    | Unit , n => ⟨ n ⟩
      | of X , n => ⟨ NormalMonoidalObject.tensor n X ⟩
      | tensor X Y , n => normalize_obj Y normalize_obj X n . as
#align
  category_theory.free_monoidal_category.normalize_obj CategoryTheory.FreeMonoidalCategory.normalizeObj

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      []
      [(Term.attributes "@[" [(Term.attrInstance (Term.attrKind []) (Attr.simp "simp" [] []))] "]")]
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `normalize_obj_unitor [])
      (Command.declSig
       [(Term.explicitBinder "(" [`n] [":" (Term.app `NormalMonoidalObject [`C])] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app
          `normalizeObj
          [(Term.app
            (CategoryTheory.CategoryTheory.Monoidal.Category.«term𝟙_» "𝟙_")
            [(Term.app
              (CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termF "F")
              [`C])])
           `n])
         "="
         (Term.anonymousCtor "⟨" [`n] "⟩"))))
      (Command.declValSimple ":=" `rfl [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rfl
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app
        `normalizeObj
        [(Term.app
          (CategoryTheory.CategoryTheory.Monoidal.Category.«term𝟙_» "𝟙_")
          [(Term.app
            (CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termF "F")
            [`C])])
         `n])
       "="
       (Term.anonymousCtor "⟨" [`n] "⟩"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [`n] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app
       `normalizeObj
       [(Term.app
         (CategoryTheory.CategoryTheory.Monoidal.Category.«term𝟙_» "𝟙_")
         [(Term.app
           (CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termF "F")
           [`C])])
        `n])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       (CategoryTheory.CategoryTheory.Monoidal.Category.«term𝟙_» "𝟙_")
       [(Term.app
         (CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termF "F")
         [`C])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termF "F")
       [`C])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `C
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termF "F")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termF', expected 'CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termF._@.CategoryTheory.Monoidal.Free.Coherence._hyg.10'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ simp ]
  theorem normalize_obj_unitor ( n : NormalMonoidalObject C ) : normalizeObj 𝟙_ F C n = ⟨ n ⟩ := rfl
#align
  category_theory.free_monoidal_category.normalize_obj_unitor CategoryTheory.FreeMonoidalCategory.normalize_obj_unitor

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      []
      [(Term.attributes "@[" [(Term.attrInstance (Term.attrKind []) (Attr.simp "simp" [] []))] "]")]
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `normalize_obj_tensor [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`X `Y]
         [":"
          (Term.app
           (CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termF "F")
           [`C])]
         []
         ")")
        (Term.explicitBinder "(" [`n] [":" (Term.app `NormalMonoidalObject [`C])] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app
          `normalizeObj
          [(CategoryTheory.CategoryTheory.Monoidal.Category.tensor_iso `X " ⊗ " `Y) `n])
         "="
         (Term.app `normalizeObj [`Y (Term.proj (Term.app `normalizeObj [`X `n]) "." `as)]))))
      (Command.declValSimple ":=" `rfl [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rfl
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app
        `normalizeObj
        [(CategoryTheory.CategoryTheory.Monoidal.Category.tensor_iso `X " ⊗ " `Y) `n])
       "="
       (Term.app `normalizeObj [`Y (Term.proj (Term.app `normalizeObj [`X `n]) "." `as)]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `normalizeObj [`Y (Term.proj (Term.app `normalizeObj [`X `n]) "." `as)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.app `normalizeObj [`X `n]) "." `as)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `normalizeObj [`X `n])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `X
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `normalizeObj
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `normalizeObj [`X `n]) ")")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `Y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `normalizeObj
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app
       `normalizeObj
       [(CategoryTheory.CategoryTheory.Monoidal.Category.tensor_iso `X " ⊗ " `Y) `n])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.CategoryTheory.Monoidal.Category.tensor_iso', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.CategoryTheory.Monoidal.Category.tensor_iso', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (CategoryTheory.CategoryTheory.Monoidal.Category.tensor_iso `X " ⊗ " `Y)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Y
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `X
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 70, (some 70, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (CategoryTheory.CategoryTheory.Monoidal.Category.tensor_iso `X " ⊗ " `Y)
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `normalizeObj
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `NormalMonoidalObject [`C])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `C
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `NormalMonoidalObject
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termF "F")
       [`C])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `C
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termF "F")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termF', expected 'CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termF._@.CategoryTheory.Monoidal.Free.Coherence._hyg.10'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ simp ]
  theorem
    normalize_obj_tensor
    ( X Y : F C ) ( n : NormalMonoidalObject C )
      : normalizeObj X ⊗ Y n = normalizeObj Y normalizeObj X n . as
    := rfl
#align
  category_theory.free_monoidal_category.normalize_obj_tensor CategoryTheory.FreeMonoidalCategory.normalize_obj_tensor

section

open Hom

attribute [local tidy] tactic.discrete_cases

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "Auxiliary definition for `normalize`. Here we prove that objects that are related by\n    associators and unitors map to the same normal form. -/")]
      [(Term.attributes "@[" [(Term.attrInstance (Term.attrKind []) (Attr.simp "simp" [] []))] "]")]
      []
      []
      []
      [])
     (Command.def
      "def"
      (Command.declId `normalizeMapAux [])
      (Command.optDeclSig
       []
       [(Term.typeSpec
         ":"
         (Term.forall
          "∀"
          [(Term.implicitBinder
            "{"
            [`X `Y]
            [":"
             (Term.app
              (CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termF "F")
              [`C])]
            "}")]
          []
          ","
          (Term.arrow
           (CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.«term_⟶ᵐ_»
            `X
            " ⟶ᵐ "
            `Y)
           "→"
           (Combinatorics.Quiver.Basic.«term_⟶_»
            (Term.typeAscription
             "("
             (Term.app `Discrete.functor [(Term.app `normalizeObj [`X])])
             ":"
             [(CategoryTheory.CategoryTheory.Functor.Basic.«term_⥤_»
               (Term.hole "_")
               " ⥤ "
               (Term.app
                (CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termN
                 "N")
                [`C]))]
             ")")
            " ⟶ "
            (Term.app `Discrete.functor [(Term.app `normalizeObj [`Y])])))))])
      (Command.declValEqns
       (Term.matchAltsWhereDecls
        (Term.matchAlts
         [(Term.matchAlt
           "|"
           [[(Term.hole "_") "," (Term.hole "_") "," (Term.app `id [(Term.hole "_")])]]
           "=>"
           (Term.app (CategoryTheory.CategoryTheory.Category.Basic.«term𝟙» "𝟙") [(Term.hole "_")]))
          (Term.matchAlt
           "|"
           [[(Term.hole "_")
             ","
             (Term.hole "_")
             ","
             (Term.app `α_hom [(Term.hole "_") (Term.hole "_") (Term.hole "_")])]]
           "=>"
           (Term.anonymousCtor
            "⟨"
            [(Term.fun
              "fun"
              (Term.basicFun
               [`X]
               []
               "=>"
               (Term.app
                (CategoryTheory.CategoryTheory.Category.Basic.«term𝟙» "𝟙")
                [(Term.hole "_")])))
             ","
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Std.Tactic.rintro
                  "rintro"
                  [(Std.Tactic.RCases.rintroPat.one
                    (Std.Tactic.RCases.rcasesPat.tuple
                     "⟨"
                     [(Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `X)])
                       [])]
                     "⟩"))
                   (Std.Tactic.RCases.rintroPat.one
                    (Std.Tactic.RCases.rcasesPat.tuple
                     "⟨"
                     [(Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `Y)])
                       [])]
                     "⟩"))
                   (Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `f))]
                  [])
                 []
                 (Tactic.simp "simp" [] [] [] [] [])])))]
            "⟩"))
          (Term.matchAlt
           "|"
           [[(Term.hole "_")
             ","
             (Term.hole "_")
             ","
             (Term.app `α_inv [(Term.hole "_") (Term.hole "_") (Term.hole "_")])]]
           "=>"
           (Term.anonymousCtor
            "⟨"
            [(Term.fun
              "fun"
              (Term.basicFun
               [`X]
               []
               "=>"
               (Term.app
                (CategoryTheory.CategoryTheory.Category.Basic.«term𝟙» "𝟙")
                [(Term.hole "_")])))
             ","
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Std.Tactic.rintro
                  "rintro"
                  [(Std.Tactic.RCases.rintroPat.one
                    (Std.Tactic.RCases.rcasesPat.tuple
                     "⟨"
                     [(Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `X)])
                       [])]
                     "⟩"))
                   (Std.Tactic.RCases.rintroPat.one
                    (Std.Tactic.RCases.rcasesPat.tuple
                     "⟨"
                     [(Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `Y)])
                       [])]
                     "⟩"))
                   (Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `f))]
                  [])
                 []
                 (Tactic.simp "simp" [] [] [] [] [])])))]
            "⟩"))
          (Term.matchAlt
           "|"
           [[(Term.hole "_") "," (Term.hole "_") "," (Term.app `l_hom [(Term.hole "_")])]]
           "=>"
           (Term.anonymousCtor
            "⟨"
            [(Term.fun
              "fun"
              (Term.basicFun
               [`X]
               []
               "=>"
               (Term.app
                (CategoryTheory.CategoryTheory.Category.Basic.«term𝟙» "𝟙")
                [(Term.hole "_")])))
             ","
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Std.Tactic.rintro
                  "rintro"
                  [(Std.Tactic.RCases.rintroPat.one
                    (Std.Tactic.RCases.rcasesPat.tuple
                     "⟨"
                     [(Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `X)])
                       [])]
                     "⟩"))
                   (Std.Tactic.RCases.rintroPat.one
                    (Std.Tactic.RCases.rcasesPat.tuple
                     "⟨"
                     [(Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `Y)])
                       [])]
                     "⟩"))
                   (Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `f))]
                  [])
                 []
                 (Tactic.simp "simp" [] [] [] [] [])])))]
            "⟩"))
          (Term.matchAlt
           "|"
           [[(Term.hole "_") "," (Term.hole "_") "," (Term.app `l_inv [(Term.hole "_")])]]
           "=>"
           (Term.anonymousCtor
            "⟨"
            [(Term.fun
              "fun"
              (Term.basicFun
               [`X]
               []
               "=>"
               (Term.app
                (CategoryTheory.CategoryTheory.Category.Basic.«term𝟙» "𝟙")
                [(Term.hole "_")])))
             ","
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Std.Tactic.rintro
                  "rintro"
                  [(Std.Tactic.RCases.rintroPat.one
                    (Std.Tactic.RCases.rcasesPat.tuple
                     "⟨"
                     [(Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `X)])
                       [])]
                     "⟩"))
                   (Std.Tactic.RCases.rintroPat.one
                    (Std.Tactic.RCases.rcasesPat.tuple
                     "⟨"
                     [(Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `Y)])
                       [])]
                     "⟩"))
                   (Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `f))]
                  [])
                 []
                 (Tactic.simp "simp" [] [] [] [] [])])))]
            "⟩"))
          (Term.matchAlt
           "|"
           [[(Term.hole "_") "," (Term.hole "_") "," (Term.app `ρ_hom [(Term.hole "_")])]]
           "=>"
           (Term.anonymousCtor
            "⟨"
            [(Term.fun
              "fun"
              (Term.basicFun
               [(Term.anonymousCtor "⟨" [`X] "⟩")]
               []
               "=>"
               (Term.anonymousCtor
                "⟨"
                [(Term.anonymousCtor
                  "⟨"
                  [(Term.byTactic
                    "by"
                    (Tactic.tacticSeq
                     (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])])))]
                  "⟩")]
                "⟩")))
             ","
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Std.Tactic.rintro
                  "rintro"
                  [(Std.Tactic.RCases.rintroPat.one
                    (Std.Tactic.RCases.rcasesPat.tuple
                     "⟨"
                     [(Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `X)])
                       [])]
                     "⟩"))
                   (Std.Tactic.RCases.rintroPat.one
                    (Std.Tactic.RCases.rcasesPat.tuple
                     "⟨"
                     [(Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `Y)])
                       [])]
                     "⟩"))
                   (Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `f))]
                  [])
                 []
                 (Tactic.simp "simp" [] [] [] [] [])])))]
            "⟩"))
          (Term.matchAlt
           "|"
           [[(Term.hole "_") "," (Term.hole "_") "," (Term.app `ρ_inv [(Term.hole "_")])]]
           "=>"
           (Term.anonymousCtor
            "⟨"
            [(Term.fun
              "fun"
              (Term.basicFun
               [(Term.anonymousCtor "⟨" [`X] "⟩")]
               []
               "=>"
               (Term.anonymousCtor
                "⟨"
                [(Term.anonymousCtor
                  "⟨"
                  [(Term.byTactic
                    "by"
                    (Tactic.tacticSeq
                     (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])])))]
                  "⟩")]
                "⟩")))
             ","
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Std.Tactic.rintro
                  "rintro"
                  [(Std.Tactic.RCases.rintroPat.one
                    (Std.Tactic.RCases.rcasesPat.tuple
                     "⟨"
                     [(Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `X)])
                       [])]
                     "⟩"))
                   (Std.Tactic.RCases.rintroPat.one
                    (Std.Tactic.RCases.rcasesPat.tuple
                     "⟨"
                     [(Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `Y)])
                       [])]
                     "⟩"))
                   (Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `f))]
                  [])
                 []
                 (Tactic.simp "simp" [] [] [] [] [])])))]
            "⟩"))
          (Term.matchAlt
           "|"
           [[`X "," `Y "," (Term.app (Term.explicit "@" `comp) [(Term.hole "_") `U `V `W `f `g])]]
           "=>"
           (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
            (Term.app `normalize_map_aux [`f])
            " ≫ "
            (Term.app `normalize_map_aux [`g])))
          (Term.matchAlt
           "|"
           [[`X
             ","
             `Y
             ","
             (Term.app (Term.explicit "@" `hom.tensor) [(Term.hole "_") `T `U `V `W `f `g])]]
           "=>"
           (Term.anonymousCtor
            "⟨"
            [(Term.fun
              "fun"
              (Term.basicFun
               [`X]
               []
               "=>"
               (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                (Term.app
                 (Term.proj (Term.app `normalize_map_aux [`g]) "." `app)
                 [(Term.app `normalizeObj [`T (Term.proj `X "." `as)])])
                " ≫ "
                (Term.app
                 (Term.proj
                  (Term.typeAscription
                   "("
                   (Term.app `Discrete.functor [(Term.app `normalizeObj [`W])])
                   ":"
                   [(CategoryTheory.CategoryTheory.Functor.Basic.«term_⥤_»
                     (Term.hole "_")
                     " ⥤ "
                     (Term.app
                      (CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termN
                       "N")
                      [`C]))]
                   ")")
                  "."
                  `map)
                 [(Term.app (Term.proj (Term.app `normalize_map_aux [`f]) "." `app) [`X])]))))
             ","
             (Term.byTactic
              "by"
              (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tidy "tidy" [])])))]
            "⟩"))])
        []))
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValEqns', expected 'Lean.Parser.Command.declValSimple'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.fun
         "fun"
         (Term.basicFun
          [`X]
          []
          "=>"
          (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
           (Term.app
            (Term.proj (Term.app `normalize_map_aux [`g]) "." `app)
            [(Term.app `normalizeObj [`T (Term.proj `X "." `as)])])
           " ≫ "
           (Term.app
            (Term.proj
             (Term.typeAscription
              "("
              (Term.app `Discrete.functor [(Term.app `normalizeObj [`W])])
              ":"
              [(CategoryTheory.CategoryTheory.Functor.Basic.«term_⥤_»
                (Term.hole "_")
                " ⥤ "
                (Term.app
                 (CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termN
                  "N")
                 [`C]))]
              ")")
             "."
             `map)
            [(Term.app (Term.proj (Term.app `normalize_map_aux [`f]) "." `app) [`X])]))))
        ","
        (Term.byTactic
         "by"
         (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tidy "tidy" [])])))]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tidy "tidy" [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tidy "tidy" [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`X]
        []
        "=>"
        (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
         (Term.app
          (Term.proj (Term.app `normalize_map_aux [`g]) "." `app)
          [(Term.app `normalizeObj [`T (Term.proj `X "." `as)])])
         " ≫ "
         (Term.app
          (Term.proj
           (Term.typeAscription
            "("
            (Term.app `Discrete.functor [(Term.app `normalizeObj [`W])])
            ":"
            [(CategoryTheory.CategoryTheory.Functor.Basic.«term_⥤_»
              (Term.hole "_")
              " ⥤ "
              (Term.app
               (CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termN
                "N")
               [`C]))]
            ")")
           "."
           `map)
          [(Term.app (Term.proj (Term.app `normalize_map_aux [`f]) "." `app) [`X])]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
       (Term.app
        (Term.proj (Term.app `normalize_map_aux [`g]) "." `app)
        [(Term.app `normalizeObj [`T (Term.proj `X "." `as)])])
       " ≫ "
       (Term.app
        (Term.proj
         (Term.typeAscription
          "("
          (Term.app `Discrete.functor [(Term.app `normalizeObj [`W])])
          ":"
          [(CategoryTheory.CategoryTheory.Functor.Basic.«term_⥤_»
            (Term.hole "_")
            " ⥤ "
            (Term.app
             (CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termN "N")
             [`C]))]
          ")")
         "."
         `map)
        [(Term.app (Term.proj (Term.app `normalize_map_aux [`f]) "." `app) [`X])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (Term.typeAscription
         "("
         (Term.app `Discrete.functor [(Term.app `normalizeObj [`W])])
         ":"
         [(CategoryTheory.CategoryTheory.Functor.Basic.«term_⥤_»
           (Term.hole "_")
           " ⥤ "
           (Term.app
            (CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termN "N")
            [`C]))]
         ")")
        "."
        `map)
       [(Term.app (Term.proj (Term.app `normalize_map_aux [`f]) "." `app) [`X])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj (Term.app `normalize_map_aux [`f]) "." `app) [`X])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `X
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app `normalize_map_aux [`f]) "." `app)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `normalize_map_aux [`f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `normalize_map_aux
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `normalize_map_aux [`f]) ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.proj (Term.paren "(" (Term.app `normalize_map_aux [`f]) ")") "." `app) [`X])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (Term.typeAscription
        "("
        (Term.app `Discrete.functor [(Term.app `normalizeObj [`W])])
        ":"
        [(CategoryTheory.CategoryTheory.Functor.Basic.«term_⥤_»
          (Term.hole "_")
          " ⥤ "
          (Term.app
           (CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termN "N")
           [`C]))]
        ")")
       "."
       `map)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.typeAscription
       "("
       (Term.app `Discrete.functor [(Term.app `normalizeObj [`W])])
       ":"
       [(CategoryTheory.CategoryTheory.Functor.Basic.«term_⥤_»
         (Term.hole "_")
         " ⥤ "
         (Term.app
          (CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termN "N")
          [`C]))]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (CategoryTheory.CategoryTheory.Functor.Basic.«term_⥤_»
       (Term.hole "_")
       " ⥤ "
       (Term.app
        (CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termN "N")
        [`C]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termN "N")
       [`C])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `C
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termN "N")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termN', expected 'CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termN._@.CategoryTheory.Monoidal.Free.Coherence._hyg.357'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValEqns', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
      Auxiliary definition for `normalize`. Here we prove that objects that are related by
          associators and unitors map to the same normal form. -/
    @[ simp ]
  def
    normalizeMapAux
    :
      ∀
        { X Y : F C }
        ,
        X ⟶ᵐ Y → ( Discrete.functor normalizeObj X : _ ⥤ N C ) ⟶ Discrete.functor normalizeObj Y
    | _ , _ , id _ => 𝟙 _
      | _ , _ , α_hom _ _ _ => ⟨ fun X => 𝟙 _ , by rintro ⟨ X ⟩ ⟨ Y ⟩ f simp ⟩
      | _ , _ , α_inv _ _ _ => ⟨ fun X => 𝟙 _ , by rintro ⟨ X ⟩ ⟨ Y ⟩ f simp ⟩
      | _ , _ , l_hom _ => ⟨ fun X => 𝟙 _ , by rintro ⟨ X ⟩ ⟨ Y ⟩ f simp ⟩
      | _ , _ , l_inv _ => ⟨ fun X => 𝟙 _ , by rintro ⟨ X ⟩ ⟨ Y ⟩ f simp ⟩
      | _ , _ , ρ_hom _ => ⟨ fun ⟨ X ⟩ => ⟨ ⟨ by simp ⟩ ⟩ , by rintro ⟨ X ⟩ ⟨ Y ⟩ f simp ⟩
      | _ , _ , ρ_inv _ => ⟨ fun ⟨ X ⟩ => ⟨ ⟨ by simp ⟩ ⟩ , by rintro ⟨ X ⟩ ⟨ Y ⟩ f simp ⟩
      | X , Y , @ comp _ U V W f g => normalize_map_aux f ≫ normalize_map_aux g
      |
        X , Y , @ hom.tensor _ T U V W f g
        =>
        ⟨
          fun
              X
                =>
                normalize_map_aux g . app normalizeObj T X . as
                  ≫
                  ( Discrete.functor normalizeObj W : _ ⥤ N C ) . map normalize_map_aux f . app X
            ,
            by tidy
          ⟩
#align
  category_theory.free_monoidal_category.normalize_map_aux CategoryTheory.FreeMonoidalCategory.normalizeMapAux

end

section

variable (C)

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "Our normalization procedure works by first defining a functor `F C ⥤ (N C ⥤ N C)` (which turns\n    out to be very easy), and then obtain a functor `F C ⥤ N C` by plugging in the normal object\n    `𝟙_ C`. -/")]
      [(Term.attributes "@[" [(Term.attrInstance (Term.attrKind []) (Attr.simp "simp" [] []))] "]")]
      []
      []
      []
      [])
     (Command.def
      "def"
      (Command.declId `normalize [])
      (Command.optDeclSig
       []
       [(Term.typeSpec
         ":"
         (CategoryTheory.CategoryTheory.Functor.Basic.«term_⥤_»
          (Term.app
           (CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termF "F")
           [`C])
          " ⥤ "
          (CategoryTheory.CategoryTheory.Functor.Basic.«term_⥤_»
           (Term.app
            (CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termN "N")
            [`C])
           " ⥤ "
           (Term.app
            (CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termN "N")
            [`C]))))])
      (Command.whereStructInst
       "where"
       [(Command.whereStructField
         (Term.letDecl
          (Term.letIdDecl
           `obj
           [`X]
           []
           ":="
           (Term.app `Discrete.functor [(Term.app `normalizeObj [`X])]))))
        []
        (Command.whereStructField
         (Term.letDecl
          (Term.letIdDecl
           `map
           [`X `Y]
           []
           ":="
           (Term.app
            `Quotient.lift
            [`normalizeMapAux
             (Term.byTactic
              "by"
              (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tidy "tidy" [])])))]))))]
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.whereStructInst', expected 'Lean.Parser.Command.declValSimple'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.whereStructInst', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Quotient.lift
       [`normalizeMapAux
        (Term.byTactic
         "by"
         (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tidy "tidy" [])])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tidy "tidy" [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tidy "tidy" [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0,
     tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tidy "tidy" [])])))
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `normalizeMapAux
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Quotient.lift
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Discrete.functor [(Term.app `normalizeObj [`X])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `normalizeObj [`X])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `X
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `normalizeObj
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `normalizeObj [`X]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Discrete.functor
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (CategoryTheory.CategoryTheory.Functor.Basic.«term_⥤_»
       (Term.app
        (CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termF "F")
        [`C])
       " ⥤ "
       (CategoryTheory.CategoryTheory.Functor.Basic.«term_⥤_»
        (Term.app
         (CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termN "N")
         [`C])
        " ⥤ "
        (Term.app
         (CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termN "N")
         [`C])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (CategoryTheory.CategoryTheory.Functor.Basic.«term_⥤_»
       (Term.app
        (CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termN "N")
        [`C])
       " ⥤ "
       (Term.app
        (CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termN "N")
        [`C]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termN "N")
       [`C])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `C
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termN "N")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termN', expected 'CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termN._@.CategoryTheory.Monoidal.Free.Coherence._hyg.357'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
      Our normalization procedure works by first defining a functor `F C ⥤ (N C ⥤ N C)` (which turns
          out to be very easy), and then obtain a functor `F C ⥤ N C` by plugging in the normal object
          `𝟙_ C`. -/
    @[ simp ]
  def
    normalize
    : F C ⥤ N C ⥤ N C
    where obj X := Discrete.functor normalizeObj X map X Y := Quotient.lift normalizeMapAux by tidy
#align
  category_theory.free_monoidal_category.normalize CategoryTheory.FreeMonoidalCategory.normalize

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "A variant of the normalization functor where we consider the result as an object in the free\n    monoidal category (rather than an object of the discrete subcategory of objects in normal\n    form). -/")]
      [(Term.attributes "@[" [(Term.attrInstance (Term.attrKind []) (Attr.simp "simp" [] []))] "]")]
      []
      []
      []
      [])
     (Command.def
      "def"
      (Command.declId `normalize' [])
      (Command.optDeclSig
       []
       [(Term.typeSpec
         ":"
         (CategoryTheory.CategoryTheory.Functor.Basic.«term_⥤_»
          (Term.app
           (CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termF "F")
           [`C])
          " ⥤ "
          (CategoryTheory.CategoryTheory.Functor.Basic.«term_⥤_»
           (Term.app
            (CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termN "N")
            [`C])
           " ⥤ "
           (Term.app
            (CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termF "F")
            [`C]))))])
      (Command.declValSimple
       ":="
       (CategoryTheory.Functor.CategoryTheory.Functor.Basic.«term_⋙_»
        (Term.app `normalize [`C])
        " ⋙ "
        (Term.app
         (Term.proj
          (Term.app `whiskeringRight [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
          "."
          `obj)
         [`inclusion]))
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (CategoryTheory.Functor.CategoryTheory.Functor.Basic.«term_⋙_»
       (Term.app `normalize [`C])
       " ⋙ "
       (Term.app
        (Term.proj
         (Term.app `whiskeringRight [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
         "."
         `obj)
        [`inclusion]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (Term.app `whiskeringRight [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
        "."
        `obj)
       [`inclusion])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `inclusion
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (Term.app `whiskeringRight [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
       "."
       `obj)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `whiskeringRight [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
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
      `whiskeringRight
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `whiskeringRight [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Term.app `normalize [`C])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `C
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `normalize
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1022, (some 1023, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (CategoryTheory.CategoryTheory.Functor.Basic.«term_⥤_»
       (Term.app
        (CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termF "F")
        [`C])
       " ⥤ "
       (CategoryTheory.CategoryTheory.Functor.Basic.«term_⥤_»
        (Term.app
         (CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termN "N")
         [`C])
        " ⥤ "
        (Term.app
         (CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termF "F")
         [`C])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (CategoryTheory.CategoryTheory.Functor.Basic.«term_⥤_»
       (Term.app
        (CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termN "N")
        [`C])
       " ⥤ "
       (Term.app
        (CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termF "F")
        [`C]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termF "F")
       [`C])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `C
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termF "F")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termF', expected 'CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termF._@.CategoryTheory.Monoidal.Free.Coherence._hyg.10'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
      A variant of the normalization functor where we consider the result as an object in the free
          monoidal category (rather than an object of the discrete subcategory of objects in normal
          form). -/
    @[ simp ]
  def normalize' : F C ⥤ N C ⥤ F C := normalize C ⋙ whiskeringRight _ _ _ . obj inclusion
#align
  category_theory.free_monoidal_category.normalize' CategoryTheory.FreeMonoidalCategory.normalize'

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "The normalization functor for the free monoidal category over `C`. -/")]
      []
      []
      []
      []
      [])
     (Command.def
      "def"
      (Command.declId `fullNormalize [])
      (Command.optDeclSig
       []
       [(Term.typeSpec
         ":"
         (CategoryTheory.CategoryTheory.Functor.Basic.«term_⥤_»
          (Term.app
           (CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termF "F")
           [`C])
          " ⥤ "
          (Term.app
           (CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termN "N")
           [`C])))])
      (Command.whereStructInst
       "where"
       [(Command.whereStructField
         (Term.letDecl
          (Term.letIdDecl
           `obj
           [`X]
           []
           ":="
           (Term.app
            (Term.proj (Term.app (Term.proj (Term.app `normalize [`C]) "." `obj) [`X]) "." `obj)
            [(Term.anonymousCtor "⟨" [`NormalMonoidalObject.unit] "⟩")]))))
        []
        (Command.whereStructField
         (Term.letDecl
          (Term.letIdDecl
           `map
           [`X `Y `f]
           []
           ":="
           (Term.app
            (Term.proj (Term.app (Term.proj (Term.app `normalize [`C]) "." `map) [`f]) "." `app)
            [(Term.anonymousCtor "⟨" [`NormalMonoidalObject.unit] "⟩")]))))]
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.whereStructInst', expected 'Lean.Parser.Command.declValSimple'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.whereStructInst', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj (Term.app (Term.proj (Term.app `normalize [`C]) "." `map) [`f]) "." `app)
       [(Term.anonymousCtor "⟨" [`NormalMonoidalObject.unit] "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [`NormalMonoidalObject.unit] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `NormalMonoidalObject.unit
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app (Term.proj (Term.app `normalize [`C]) "." `map) [`f]) "." `app)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app (Term.proj (Term.app `normalize [`C]) "." `map) [`f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app `normalize [`C]) "." `map)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `normalize [`C])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `C
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `normalize
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `normalize [`C]) ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.proj (Term.paren "(" (Term.app `normalize [`C]) ")") "." `map) [`f])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj (Term.app (Term.proj (Term.app `normalize [`C]) "." `obj) [`X]) "." `obj)
       [(Term.anonymousCtor "⟨" [`NormalMonoidalObject.unit] "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [`NormalMonoidalObject.unit] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `NormalMonoidalObject.unit
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app (Term.proj (Term.app `normalize [`C]) "." `obj) [`X]) "." `obj)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app (Term.proj (Term.app `normalize [`C]) "." `obj) [`X])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `X
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app `normalize [`C]) "." `obj)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `normalize [`C])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `C
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `normalize
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `normalize [`C]) ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.proj (Term.paren "(" (Term.app `normalize [`C]) ")") "." `obj) [`X])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (CategoryTheory.CategoryTheory.Functor.Basic.«term_⥤_»
       (Term.app
        (CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termF "F")
        [`C])
       " ⥤ "
       (Term.app
        (CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termN "N")
        [`C]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termN "N")
       [`C])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `C
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termN "N")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termN', expected 'CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termN._@.CategoryTheory.Monoidal.Free.Coherence._hyg.357'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/-- The normalization functor for the free monoidal category over `C`. -/
  def
    fullNormalize
    : F C ⥤ N C
    where
      obj X := normalize C . obj X . obj ⟨ NormalMonoidalObject.unit ⟩
        map X Y f := normalize C . map f . app ⟨ NormalMonoidalObject.unit ⟩
#align
  category_theory.free_monoidal_category.full_normalize CategoryTheory.FreeMonoidalCategory.fullNormalize

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "Given an object `X` of the free monoidal category and an object `n` in normal form, taking\n    the tensor product `n ⊗ X` in the free monoidal category is functorial in both `X` and `n`. -/")]
      [(Term.attributes "@[" [(Term.attrInstance (Term.attrKind []) (Attr.simp "simp" [] []))] "]")]
      []
      []
      []
      [])
     (Command.def
      "def"
      (Command.declId `tensorFunc [])
      (Command.optDeclSig
       []
       [(Term.typeSpec
         ":"
         (CategoryTheory.CategoryTheory.Functor.Basic.«term_⥤_»
          (Term.app
           (CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termF "F")
           [`C])
          " ⥤ "
          (CategoryTheory.CategoryTheory.Functor.Basic.«term_⥤_»
           (Term.app
            (CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termN "N")
            [`C])
           " ⥤ "
           (Term.app
            (CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termF "F")
            [`C]))))])
      (Command.whereStructInst
       "where"
       [(Command.whereStructField
         (Term.letDecl
          (Term.letIdDecl
           `obj
           [`X]
           []
           ":="
           (Term.app
            `Discrete.functor
            [(Term.fun
              "fun"
              (Term.basicFun
               [`n]
               []
               "=>"
               (CategoryTheory.CategoryTheory.Monoidal.Category.tensor_iso
                (Term.app (Term.proj `inclusion "." `obj) [(Term.anonymousCtor "⟨" [`n] "⟩")])
                " ⊗ "
                `X)))]))))
        []
        (Command.whereStructField
         (Term.letDecl
          (Term.letIdDecl
           `map
           [`X `Y `f]
           []
           ":="
           (Term.anonymousCtor
            "⟨"
            [(Term.fun
              "fun"
              (Term.basicFun
               [`n]
               []
               "=>"
               (CategoryTheory.CategoryTheory.Monoidal.Category.tensor_iso
                (Term.app
                 (CategoryTheory.CategoryTheory.Category.Basic.«term𝟙» "𝟙")
                 [(Term.hole "_")])
                " ⊗ "
                `f)))
             ","
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Std.Tactic.rintro
                  "rintro"
                  [(Std.Tactic.RCases.rintroPat.one
                    (Std.Tactic.RCases.rcasesPat.tuple
                     "⟨"
                     [(Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `X)])
                       [])]
                     "⟩"))
                   (Std.Tactic.RCases.rintroPat.one
                    (Std.Tactic.RCases.rcasesPat.tuple
                     "⟨"
                     [(Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `Y)])
                       [])]
                     "⟩"))]
                  [])
                 []
                 (Tactic.tidy "tidy" [])])))]
            "⟩"))))]
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.whereStructInst', expected 'Lean.Parser.Command.declValSimple'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.whereStructInst', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.fun
         "fun"
         (Term.basicFun
          [`n]
          []
          "=>"
          (CategoryTheory.CategoryTheory.Monoidal.Category.tensor_iso
           (Term.app (CategoryTheory.CategoryTheory.Category.Basic.«term𝟙» "𝟙") [(Term.hole "_")])
           " ⊗ "
           `f)))
        ","
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Std.Tactic.rintro
             "rintro"
             [(Std.Tactic.RCases.rintroPat.one
               (Std.Tactic.RCases.rcasesPat.tuple
                "⟨"
                [(Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `X)])
                  [])]
                "⟩"))
              (Std.Tactic.RCases.rintroPat.one
               (Std.Tactic.RCases.rcasesPat.tuple
                "⟨"
                [(Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `Y)])
                  [])]
                "⟩"))]
             [])
            []
            (Tactic.tidy "tidy" [])])))]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Std.Tactic.rintro
           "rintro"
           [(Std.Tactic.RCases.rintroPat.one
             (Std.Tactic.RCases.rcasesPat.tuple
              "⟨"
              [(Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `X)])
                [])]
              "⟩"))
            (Std.Tactic.RCases.rintroPat.one
             (Std.Tactic.RCases.rcasesPat.tuple
              "⟨"
              [(Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `Y)])
                [])]
              "⟩"))]
           [])
          []
          (Tactic.tidy "tidy" [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tidy "tidy" [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.rintro
       "rintro"
       [(Std.Tactic.RCases.rintroPat.one
         (Std.Tactic.RCases.rcasesPat.tuple
          "⟨"
          [(Std.Tactic.RCases.rcasesPatLo
            (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `X)])
            [])]
          "⟩"))
        (Std.Tactic.RCases.rintroPat.one
         (Std.Tactic.RCases.rcasesPat.tuple
          "⟨"
          [(Std.Tactic.RCases.rcasesPatLo
            (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `Y)])
            [])]
          "⟩"))]
       [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`n]
        []
        "=>"
        (CategoryTheory.CategoryTheory.Monoidal.Category.tensor_iso
         (Term.app (CategoryTheory.CategoryTheory.Category.Basic.«term𝟙» "𝟙") [(Term.hole "_")])
         " ⊗ "
         `f)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (CategoryTheory.CategoryTheory.Monoidal.Category.tensor_iso
       (Term.app (CategoryTheory.CategoryTheory.Category.Basic.«term𝟙» "𝟙") [(Term.hole "_")])
       " ⊗ "
       `f)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (Term.app (CategoryTheory.CategoryTheory.Category.Basic.«term𝟙» "𝟙") [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (CategoryTheory.CategoryTheory.Category.Basic.«term𝟙» "𝟙")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1022, (some 1023, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 70, (some 70, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Discrete.functor
       [(Term.fun
         "fun"
         (Term.basicFun
          [`n]
          []
          "=>"
          (CategoryTheory.CategoryTheory.Monoidal.Category.tensor_iso
           (Term.app (Term.proj `inclusion "." `obj) [(Term.anonymousCtor "⟨" [`n] "⟩")])
           " ⊗ "
           `X)))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`n]
        []
        "=>"
        (CategoryTheory.CategoryTheory.Monoidal.Category.tensor_iso
         (Term.app (Term.proj `inclusion "." `obj) [(Term.anonymousCtor "⟨" [`n] "⟩")])
         " ⊗ "
         `X)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (CategoryTheory.CategoryTheory.Monoidal.Category.tensor_iso
       (Term.app (Term.proj `inclusion "." `obj) [(Term.anonymousCtor "⟨" [`n] "⟩")])
       " ⊗ "
       `X)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `X
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (Term.app (Term.proj `inclusion "." `obj) [(Term.anonymousCtor "⟨" [`n] "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [`n] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `inclusion "." `obj)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `inclusion
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1022, (some 1023, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 70, (some 70, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Discrete.functor
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (CategoryTheory.CategoryTheory.Functor.Basic.«term_⥤_»
       (Term.app
        (CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termF "F")
        [`C])
       " ⥤ "
       (CategoryTheory.CategoryTheory.Functor.Basic.«term_⥤_»
        (Term.app
         (CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termN "N")
         [`C])
        " ⥤ "
        (Term.app
         (CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termF "F")
         [`C])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (CategoryTheory.CategoryTheory.Functor.Basic.«term_⥤_»
       (Term.app
        (CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termN "N")
        [`C])
       " ⥤ "
       (Term.app
        (CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termF "F")
        [`C]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termF "F")
       [`C])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `C
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termF "F")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termF', expected 'CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termF._@.CategoryTheory.Monoidal.Free.Coherence._hyg.10'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
      Given an object `X` of the free monoidal category and an object `n` in normal form, taking
          the tensor product `n ⊗ X` in the free monoidal category is functorial in both `X` and `n`. -/
    @[ simp ]
  def
    tensorFunc
    : F C ⥤ N C ⥤ F C
    where
      obj X := Discrete.functor fun n => inclusion . obj ⟨ n ⟩ ⊗ X
        map X Y f := ⟨ fun n => 𝟙 _ ⊗ f , by rintro ⟨ X ⟩ ⟨ Y ⟩ tidy ⟩
#align
  category_theory.free_monoidal_category.tensor_func CategoryTheory.FreeMonoidalCategory.tensorFunc

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `tensor_func_map_app [])
      (Command.declSig
       [(Term.implicitBinder
         "{"
         [`X `Y]
         [":"
          (Term.app
           (CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termF "F")
           [`C])]
         "}")
        (Term.explicitBinder
         "("
         [`f]
         [":" (Combinatorics.Quiver.Basic.«term_⟶_» `X " ⟶ " `Y)]
         []
         ")")
        (Term.explicitBinder "(" [`n] [] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app
          (Term.proj (Term.app (Term.proj (Term.app `tensorFunc [`C]) "." `map) [`f]) "." `app)
          [`n])
         "="
         (CategoryTheory.CategoryTheory.Monoidal.Category.tensor_iso
          (Term.app (CategoryTheory.CategoryTheory.Category.Basic.«term𝟙» "𝟙") [(Term.hole "_")])
          " ⊗ "
          `f))))
      (Command.declValSimple ":=" `rfl [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rfl
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app
        (Term.proj (Term.app (Term.proj (Term.app `tensorFunc [`C]) "." `map) [`f]) "." `app)
        [`n])
       "="
       (CategoryTheory.CategoryTheory.Monoidal.Category.tensor_iso
        (Term.app (CategoryTheory.CategoryTheory.Category.Basic.«term𝟙» "𝟙") [(Term.hole "_")])
        " ⊗ "
        `f))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (CategoryTheory.CategoryTheory.Monoidal.Category.tensor_iso
       (Term.app (CategoryTheory.CategoryTheory.Category.Basic.«term𝟙» "𝟙") [(Term.hole "_")])
       " ⊗ "
       `f)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (Term.app (CategoryTheory.CategoryTheory.Category.Basic.«term𝟙» "𝟙") [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (CategoryTheory.CategoryTheory.Category.Basic.«term𝟙» "𝟙")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1022, (some 1023, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 70, (some 70, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app
       (Term.proj (Term.app (Term.proj (Term.app `tensorFunc [`C]) "." `map) [`f]) "." `app)
       [`n])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app (Term.proj (Term.app `tensorFunc [`C]) "." `map) [`f]) "." `app)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app (Term.proj (Term.app `tensorFunc [`C]) "." `map) [`f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app `tensorFunc [`C]) "." `map)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `tensorFunc [`C])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `C
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `tensorFunc
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `tensorFunc [`C]) ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.proj (Term.paren "(" (Term.app `tensorFunc [`C]) ")") "." `map) [`f])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Combinatorics.Quiver.Basic.«term_⟶_» `X " ⟶ " `Y)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Y
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      `X
[PrettyPrinter.parenthesize] ...precedences are 11 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 10, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.implicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.implicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.implicitBinder', expected 'Lean.Parser.Term.explicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.implicitBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termF "F")
       [`C])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `C
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termF "F")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termF', expected 'CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termF._@.CategoryTheory.Monoidal.Free.Coherence._hyg.10'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.implicitBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  tensor_func_map_app
  { X Y : F C } ( f : X ⟶ Y ) ( n ) : tensorFunc C . map f . app n = 𝟙 _ ⊗ f
  := rfl
#align
  category_theory.free_monoidal_category.tensor_func_map_app CategoryTheory.FreeMonoidalCategory.tensor_func_map_app

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `tensor_func_obj_map [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`Z]
         [":"
          (Term.app
           (CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termF "F")
           [`C])]
         []
         ")")
        (Term.implicitBinder
         "{"
         [`n `n']
         [":"
          (Term.app
           (CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termN "N")
           [`C])]
         "}")
        (Term.explicitBinder
         "("
         [`f]
         [":" (Combinatorics.Quiver.Basic.«term_⟶_» `n " ⟶ " `n')]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app
          (Term.proj (Term.app (Term.proj (Term.app `tensorFunc [`C]) "." `obj) [`Z]) "." `map)
          [`f])
         "="
         (CategoryTheory.CategoryTheory.Monoidal.Category.tensor_iso
          (Term.app (Term.proj `inclusion "." `map) [`f])
          " ⊗ "
          (Term.app (CategoryTheory.CategoryTheory.Category.Basic.«term𝟙» "𝟙") [`Z])))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.cases "cases" [(Tactic.casesTarget [] `n)] [] [])
           []
           (Tactic.cases "cases" [(Tactic.casesTarget [] `n')] [] [])
           []
           (Tactic.tidy "tidy" [])])))
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
         [(Tactic.cases "cases" [(Tactic.casesTarget [] `n)] [] [])
          []
          (Tactic.cases "cases" [(Tactic.casesTarget [] `n')] [] [])
          []
          (Tactic.tidy "tidy" [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tidy "tidy" [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.cases "cases" [(Tactic.casesTarget [] `n')] [] [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.cases "cases" [(Tactic.casesTarget [] `n)] [] [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app
        (Term.proj (Term.app (Term.proj (Term.app `tensorFunc [`C]) "." `obj) [`Z]) "." `map)
        [`f])
       "="
       (CategoryTheory.CategoryTheory.Monoidal.Category.tensor_iso
        (Term.app (Term.proj `inclusion "." `map) [`f])
        " ⊗ "
        (Term.app (CategoryTheory.CategoryTheory.Category.Basic.«term𝟙» "𝟙") [`Z])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (CategoryTheory.CategoryTheory.Monoidal.Category.tensor_iso
       (Term.app (Term.proj `inclusion "." `map) [`f])
       " ⊗ "
       (Term.app (CategoryTheory.CategoryTheory.Category.Basic.«term𝟙» "𝟙") [`Z]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (CategoryTheory.CategoryTheory.Category.Basic.«term𝟙» "𝟙") [`Z])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Z
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (CategoryTheory.CategoryTheory.Category.Basic.«term𝟙» "𝟙")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (Term.app (Term.proj `inclusion "." `map) [`f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `inclusion "." `map)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `inclusion
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1022, (some 1023, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 70, (some 70, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app
       (Term.proj (Term.app (Term.proj (Term.app `tensorFunc [`C]) "." `obj) [`Z]) "." `map)
       [`f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app (Term.proj (Term.app `tensorFunc [`C]) "." `obj) [`Z]) "." `map)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app (Term.proj (Term.app `tensorFunc [`C]) "." `obj) [`Z])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Z
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app `tensorFunc [`C]) "." `obj)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `tensorFunc [`C])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `C
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `tensorFunc
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `tensorFunc [`C]) ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.proj (Term.paren "(" (Term.app `tensorFunc [`C]) ")") "." `obj) [`Z])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Combinatorics.Quiver.Basic.«term_⟶_» `n " ⟶ " `n')
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n'
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      `n
[PrettyPrinter.parenthesize] ...precedences are 11 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 10, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.implicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.implicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.implicitBinder', expected 'Lean.Parser.Term.explicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.implicitBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termN "N")
       [`C])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `C
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termN "N")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termN', expected 'CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termN._@.CategoryTheory.Monoidal.Free.Coherence._hyg.357'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.implicitBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  tensor_func_obj_map
  ( Z : F C ) { n n' : N C } ( f : n ⟶ n' ) : tensorFunc C . obj Z . map f = inclusion . map f ⊗ 𝟙 Z
  := by cases n cases n' tidy
#align
  category_theory.free_monoidal_category.tensor_func_obj_map CategoryTheory.FreeMonoidalCategory.tensor_func_obj_map

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "Auxiliary definition for `normalize_iso`. Here we construct the isomorphism between\n    `n ⊗ X` and `normalize X n`. -/")]
      [(Term.attributes "@[" [(Term.attrInstance (Term.attrKind []) (Attr.simp "simp" [] []))] "]")]
      []
      []
      []
      [])
     (Command.def
      "def"
      (Command.declId `normalizeIsoApp [])
      (Command.optDeclSig
       []
       [(Term.typeSpec
         ":"
         (Term.forall
          "∀"
          [(Term.explicitBinder
            "("
            [`X]
            [":"
             (Term.app
              (CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termF "F")
              [`C])]
            []
            ")")
           (Term.explicitBinder
            "("
            [`n]
            [":"
             (Term.app
              (CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termN "N")
              [`C])]
            []
            ")")]
          []
          ","
          (CategoryTheory.CategoryTheory.Isomorphism.«term_≅_»
           (Term.app
            (Term.proj (Term.app (Term.proj (Term.app `tensorFunc [`C]) "." `obj) [`X]) "." `obj)
            [`n])
           " ≅ "
           (Term.app
            (Term.proj (Term.app (Term.proj (Term.app `normalize' [`C]) "." `obj) [`X]) "." `obj)
            [`n]))))])
      (Command.declValEqns
       (Term.matchAltsWhereDecls
        (Term.matchAlts
         [(Term.matchAlt
           "|"
           [[(Term.app `of [`X]) "," `n]]
           "=>"
           (Term.app `Iso.refl [(Term.hole "_")]))
          (Term.matchAlt
           "|"
           [[`Unit "," `n]]
           "=>"
           (Term.app
            (CategoryTheory.CategoryTheory.Monoidal.Category.termρ_ "ρ_")
            [(Term.hole "_")]))
          (Term.matchAlt
           "|"
           [[(Term.app `tensor [`X `Y]) "," `n]]
           "=>"
           (CategoryTheory.Iso.CategoryTheory.Isomorphism.«term_≪≫_»
            (Term.proj
             (Term.app
              (CategoryTheory.CategoryTheory.Monoidal.Category.termα_ "α_")
              [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
             "."
             `symm)
            " ≪≫ "
            (CategoryTheory.Iso.CategoryTheory.Isomorphism.«term_≪≫_»
             (Term.app
              `tensorIso
              [(Term.app `normalize_iso_app [`X `n]) (Term.app `Iso.refl [(Term.hole "_")])])
             " ≪≫ "
             (Term.app `normalize_iso_app [(Term.hole "_") (Term.hole "_")]))))])
        []))
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValEqns', expected 'Lean.Parser.Command.declValSimple'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (CategoryTheory.Iso.CategoryTheory.Isomorphism.«term_≪≫_»
       (Term.proj
        (Term.app
         (CategoryTheory.CategoryTheory.Monoidal.Category.termα_ "α_")
         [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
        "."
        `symm)
       " ≪≫ "
       (CategoryTheory.Iso.CategoryTheory.Isomorphism.«term_≪≫_»
        (Term.app
         `tensorIso
         [(Term.app `normalize_iso_app [`X `n]) (Term.app `Iso.refl [(Term.hole "_")])])
        " ≪≫ "
        (Term.app `normalize_iso_app [(Term.hole "_") (Term.hole "_")])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (CategoryTheory.Iso.CategoryTheory.Isomorphism.«term_≪≫_»
       (Term.app
        `tensorIso
        [(Term.app `normalize_iso_app [`X `n]) (Term.app `Iso.refl [(Term.hole "_")])])
       " ≪≫ "
       (Term.app `normalize_iso_app [(Term.hole "_") (Term.hole "_")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `normalize_iso_app [(Term.hole "_") (Term.hole "_")])
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
      `normalize_iso_app
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Term.app
       `tensorIso
       [(Term.app `normalize_iso_app [`X `n]) (Term.app `Iso.refl [(Term.hole "_")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Iso.refl [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Iso.refl
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `Iso.refl [(Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `normalize_iso_app [`X `n])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `X
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `normalize_iso_app
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `normalize_iso_app [`X `n])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `tensorIso
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1022, (some 1023, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Term.proj
       (Term.app
        (CategoryTheory.CategoryTheory.Monoidal.Category.termα_ "α_")
        [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
       "."
       `symm)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       (CategoryTheory.CategoryTheory.Monoidal.Category.termα_ "α_")
       [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
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
      (CategoryTheory.CategoryTheory.Monoidal.Category.termα_ "α_")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      (CategoryTheory.CategoryTheory.Monoidal.Category.termα_ "α_")
      [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `tensor [`X `Y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `X
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `tensor
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app (CategoryTheory.CategoryTheory.Monoidal.Category.termρ_ "ρ_") [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (CategoryTheory.CategoryTheory.Monoidal.Category.termρ_ "ρ_")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Unit
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app `Iso.refl [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Iso.refl
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `of [`X])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `X
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `of
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.forall
       "∀"
       [(Term.explicitBinder
         "("
         [`X]
         [":"
          (Term.app
           (CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termF "F")
           [`C])]
         []
         ")")
        (Term.explicitBinder
         "("
         [`n]
         [":"
          (Term.app
           (CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termN "N")
           [`C])]
         []
         ")")]
       []
       ","
       (CategoryTheory.CategoryTheory.Isomorphism.«term_≅_»
        (Term.app
         (Term.proj (Term.app (Term.proj (Term.app `tensorFunc [`C]) "." `obj) [`X]) "." `obj)
         [`n])
        " ≅ "
        (Term.app
         (Term.proj (Term.app (Term.proj (Term.app `normalize' [`C]) "." `obj) [`X]) "." `obj)
         [`n])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (CategoryTheory.CategoryTheory.Isomorphism.«term_≅_»
       (Term.app
        (Term.proj (Term.app (Term.proj (Term.app `tensorFunc [`C]) "." `obj) [`X]) "." `obj)
        [`n])
       " ≅ "
       (Term.app
        (Term.proj (Term.app (Term.proj (Term.app `normalize' [`C]) "." `obj) [`X]) "." `obj)
        [`n]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj (Term.app (Term.proj (Term.app `normalize' [`C]) "." `obj) [`X]) "." `obj)
       [`n])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app (Term.proj (Term.app `normalize' [`C]) "." `obj) [`X]) "." `obj)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app (Term.proj (Term.app `normalize' [`C]) "." `obj) [`X])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `X
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app `normalize' [`C]) "." `obj)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `normalize' [`C])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `C
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `normalize'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `normalize' [`C]) ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.proj (Term.paren "(" (Term.app `normalize' [`C]) ")") "." `obj) [`X])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      (Term.app
       (Term.proj (Term.app (Term.proj (Term.app `tensorFunc [`C]) "." `obj) [`X]) "." `obj)
       [`n])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app (Term.proj (Term.app `tensorFunc [`C]) "." `obj) [`X]) "." `obj)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app (Term.proj (Term.app `tensorFunc [`C]) "." `obj) [`X])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `X
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app `tensorFunc [`C]) "." `obj)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `tensorFunc [`C])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `C
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `tensorFunc
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `tensorFunc [`C]) ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.proj (Term.paren "(" (Term.app `tensorFunc [`C]) ")") "." `obj) [`X])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 11 >? 1022, (some 1023, term) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 10, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termN "N")
       [`C])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `C
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termN "N")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termN', expected 'CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termN._@.CategoryTheory.Monoidal.Free.Coherence._hyg.357'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
      Auxiliary definition for `normalize_iso`. Here we construct the isomorphism between
          `n ⊗ X` and `normalize X n`. -/
    @[ simp ]
  def
    normalizeIsoApp
    : ∀ ( X : F C ) ( n : N C ) , tensorFunc C . obj X . obj n ≅ normalize' C . obj X . obj n
    | of X , n => Iso.refl _
      | Unit , n => ρ_ _
      |
        tensor X Y , n
        =>
        α_ _ _ _ . symm ≪≫ tensorIso normalize_iso_app X n Iso.refl _ ≪≫ normalize_iso_app _ _
#align
  category_theory.free_monoidal_category.normalize_iso_app CategoryTheory.FreeMonoidalCategory.normalizeIsoApp

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      []
      [(Term.attributes "@[" [(Term.attrInstance (Term.attrKind []) (Attr.simp "simp" [] []))] "]")]
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `normalize_iso_app_tensor [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`X `Y]
         [":"
          (Term.app
           (CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termF "F")
           [`C])]
         []
         ")")
        (Term.explicitBinder
         "("
         [`n]
         [":"
          (Term.app
           (CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termN "N")
           [`C])]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app
          `normalizeIsoApp
          [`C (CategoryTheory.CategoryTheory.Monoidal.Category.tensor_iso `X " ⊗ " `Y) `n])
         "="
         (CategoryTheory.Iso.CategoryTheory.Isomorphism.«term_≪≫_»
          (Term.proj
           (Term.app
            (CategoryTheory.CategoryTheory.Monoidal.Category.termα_ "α_")
            [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
           "."
           `symm)
          " ≪≫ "
          (CategoryTheory.Iso.CategoryTheory.Isomorphism.«term_≪≫_»
           (Term.app
            `tensorIso
            [(Term.app `normalizeIsoApp [`C `X `n]) (Term.app `Iso.refl [(Term.hole "_")])])
           " ≪≫ "
           (Term.app `normalizeIsoApp [(Term.hole "_") (Term.hole "_") (Term.hole "_")]))))))
      (Command.declValSimple ":=" `rfl [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rfl
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app
        `normalizeIsoApp
        [`C (CategoryTheory.CategoryTheory.Monoidal.Category.tensor_iso `X " ⊗ " `Y) `n])
       "="
       (CategoryTheory.Iso.CategoryTheory.Isomorphism.«term_≪≫_»
        (Term.proj
         (Term.app
          (CategoryTheory.CategoryTheory.Monoidal.Category.termα_ "α_")
          [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
         "."
         `symm)
        " ≪≫ "
        (CategoryTheory.Iso.CategoryTheory.Isomorphism.«term_≪≫_»
         (Term.app
          `tensorIso
          [(Term.app `normalizeIsoApp [`C `X `n]) (Term.app `Iso.refl [(Term.hole "_")])])
         " ≪≫ "
         (Term.app `normalizeIsoApp [(Term.hole "_") (Term.hole "_") (Term.hole "_")]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (CategoryTheory.Iso.CategoryTheory.Isomorphism.«term_≪≫_»
       (Term.proj
        (Term.app
         (CategoryTheory.CategoryTheory.Monoidal.Category.termα_ "α_")
         [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
        "."
        `symm)
       " ≪≫ "
       (CategoryTheory.Iso.CategoryTheory.Isomorphism.«term_≪≫_»
        (Term.app
         `tensorIso
         [(Term.app `normalizeIsoApp [`C `X `n]) (Term.app `Iso.refl [(Term.hole "_")])])
        " ≪≫ "
        (Term.app `normalizeIsoApp [(Term.hole "_") (Term.hole "_") (Term.hole "_")])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (CategoryTheory.Iso.CategoryTheory.Isomorphism.«term_≪≫_»
       (Term.app
        `tensorIso
        [(Term.app `normalizeIsoApp [`C `X `n]) (Term.app `Iso.refl [(Term.hole "_")])])
       " ≪≫ "
       (Term.app `normalizeIsoApp [(Term.hole "_") (Term.hole "_") (Term.hole "_")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `normalizeIsoApp [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
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
      `normalizeIsoApp
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Term.app
       `tensorIso
       [(Term.app `normalizeIsoApp [`C `X `n]) (Term.app `Iso.refl [(Term.hole "_")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Iso.refl [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Iso.refl
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `Iso.refl [(Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `normalizeIsoApp [`C `X `n])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `X
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `C
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `normalizeIsoApp
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `normalizeIsoApp [`C `X `n])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `tensorIso
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1022, (some 1023, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Term.proj
       (Term.app
        (CategoryTheory.CategoryTheory.Monoidal.Category.termα_ "α_")
        [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
       "."
       `symm)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       (CategoryTheory.CategoryTheory.Monoidal.Category.termα_ "α_")
       [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
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
      (CategoryTheory.CategoryTheory.Monoidal.Category.termα_ "α_")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      (CategoryTheory.CategoryTheory.Monoidal.Category.termα_ "α_")
      [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app
       `normalizeIsoApp
       [`C (CategoryTheory.CategoryTheory.Monoidal.Category.tensor_iso `X " ⊗ " `Y) `n])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.CategoryTheory.Monoidal.Category.tensor_iso', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.CategoryTheory.Monoidal.Category.tensor_iso', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (CategoryTheory.CategoryTheory.Monoidal.Category.tensor_iso `X " ⊗ " `Y)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Y
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `X
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 70, (some 70, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (CategoryTheory.CategoryTheory.Monoidal.Category.tensor_iso `X " ⊗ " `Y)
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `C
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `normalizeIsoApp
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termN "N")
       [`C])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `C
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termN "N")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termN', expected 'CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termN._@.CategoryTheory.Monoidal.Free.Coherence._hyg.357'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ simp ]
  theorem
    normalize_iso_app_tensor
    ( X Y : F C ) ( n : N C )
      :
        normalizeIsoApp C X ⊗ Y n
          =
          α_ _ _ _ . symm ≪≫ tensorIso normalizeIsoApp C X n Iso.refl _ ≪≫ normalizeIsoApp _ _ _
    := rfl
#align
  category_theory.free_monoidal_category.normalize_iso_app_tensor CategoryTheory.FreeMonoidalCategory.normalize_iso_app_tensor

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      []
      [(Term.attributes "@[" [(Term.attrInstance (Term.attrKind []) (Attr.simp "simp" [] []))] "]")]
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `normalize_iso_app_unitor [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`n]
         [":"
          (Term.app
           (CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termN "N")
           [`C])]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app
          `normalizeIsoApp
          [`C
           (Term.app
            (CategoryTheory.CategoryTheory.Monoidal.Category.«term𝟙_» "𝟙_")
            [(Term.app
              (CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termF "F")
              [`C])])
           `n])
         "="
         (Term.app
          (CategoryTheory.CategoryTheory.Monoidal.Category.termρ_ "ρ_")
          [(Term.hole "_")]))))
      (Command.declValSimple ":=" `rfl [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rfl
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app
        `normalizeIsoApp
        [`C
         (Term.app
          (CategoryTheory.CategoryTheory.Monoidal.Category.«term𝟙_» "𝟙_")
          [(Term.app
            (CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termF "F")
            [`C])])
         `n])
       "="
       (Term.app (CategoryTheory.CategoryTheory.Monoidal.Category.termρ_ "ρ_") [(Term.hole "_")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (CategoryTheory.CategoryTheory.Monoidal.Category.termρ_ "ρ_") [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (CategoryTheory.CategoryTheory.Monoidal.Category.termρ_ "ρ_")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app
       `normalizeIsoApp
       [`C
        (Term.app
         (CategoryTheory.CategoryTheory.Monoidal.Category.«term𝟙_» "𝟙_")
         [(Term.app
           (CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termF "F")
           [`C])])
        `n])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       (CategoryTheory.CategoryTheory.Monoidal.Category.«term𝟙_» "𝟙_")
       [(Term.app
         (CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termF "F")
         [`C])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termF "F")
       [`C])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `C
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termF "F")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termF', expected 'CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termF._@.CategoryTheory.Monoidal.Free.Coherence._hyg.10'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ simp ] theorem normalize_iso_app_unitor ( n : N C ) : normalizeIsoApp C 𝟙_ F C n = ρ_ _ := rfl
#align
  category_theory.free_monoidal_category.normalize_iso_app_unitor CategoryTheory.FreeMonoidalCategory.normalize_iso_app_unitor

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment "/--" "Auxiliary definition for `normalize_iso`. -/")]
      [(Term.attributes "@[" [(Term.attrInstance (Term.attrKind []) (Attr.simp "simp" [] []))] "]")]
      []
      []
      []
      [])
     (Command.def
      "def"
      (Command.declId `normalizeIsoAux [])
      (Command.optDeclSig
       [(Term.explicitBinder
         "("
         [`X]
         [":"
          (Term.app
           (CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termF "F")
           [`C])]
         []
         ")")]
       [(Term.typeSpec
         ":"
         (CategoryTheory.CategoryTheory.Isomorphism.«term_≅_»
          (Term.app (Term.proj (Term.app `tensorFunc [`C]) "." `obj) [`X])
          " ≅ "
          (Term.app (Term.proj (Term.app `normalize' [`C]) "." `obj) [`X])))])
      (Command.declValSimple
       ":="
       (Term.app
        `NatIso.ofComponents
        [(Term.app `normalizeIsoApp [`C `X])
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Std.Tactic.rintro
              "rintro"
              [(Std.Tactic.RCases.rintroPat.one
                (Std.Tactic.RCases.rcasesPat.tuple
                 "⟨"
                 [(Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `X)])
                   [])]
                 "⟩"))
               (Std.Tactic.RCases.rintroPat.one
                (Std.Tactic.RCases.rcasesPat.tuple
                 "⟨"
                 [(Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `Y)])
                   [])]
                 "⟩"))]
              [])
             []
             (Tactic.tidy "tidy" [])])))])
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `NatIso.ofComponents
       [(Term.app `normalizeIsoApp [`C `X])
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Std.Tactic.rintro
             "rintro"
             [(Std.Tactic.RCases.rintroPat.one
               (Std.Tactic.RCases.rcasesPat.tuple
                "⟨"
                [(Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `X)])
                  [])]
                "⟩"))
              (Std.Tactic.RCases.rintroPat.one
               (Std.Tactic.RCases.rcasesPat.tuple
                "⟨"
                [(Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `Y)])
                  [])]
                "⟩"))]
             [])
            []
            (Tactic.tidy "tidy" [])])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Std.Tactic.rintro
           "rintro"
           [(Std.Tactic.RCases.rintroPat.one
             (Std.Tactic.RCases.rcasesPat.tuple
              "⟨"
              [(Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `X)])
                [])]
              "⟩"))
            (Std.Tactic.RCases.rintroPat.one
             (Std.Tactic.RCases.rcasesPat.tuple
              "⟨"
              [(Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `Y)])
                [])]
              "⟩"))]
           [])
          []
          (Tactic.tidy "tidy" [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tidy "tidy" [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.rintro
       "rintro"
       [(Std.Tactic.RCases.rintroPat.one
         (Std.Tactic.RCases.rcasesPat.tuple
          "⟨"
          [(Std.Tactic.RCases.rcasesPatLo
            (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `X)])
            [])]
          "⟩"))
        (Std.Tactic.RCases.rintroPat.one
         (Std.Tactic.RCases.rcasesPat.tuple
          "⟨"
          [(Std.Tactic.RCases.rcasesPatLo
            (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `Y)])
            [])]
          "⟩"))]
       [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0,
     tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(Std.Tactic.rintro
          "rintro"
          [(Std.Tactic.RCases.rintroPat.one
            (Std.Tactic.RCases.rcasesPat.tuple
             "⟨"
             [(Std.Tactic.RCases.rcasesPatLo
               (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `X)])
               [])]
             "⟩"))
           (Std.Tactic.RCases.rintroPat.one
            (Std.Tactic.RCases.rcasesPat.tuple
             "⟨"
             [(Std.Tactic.RCases.rcasesPatLo
               (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `Y)])
               [])]
             "⟩"))]
          [])
         []
         (Tactic.tidy "tidy" [])])))
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `normalizeIsoApp [`C `X])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `X
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `C
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `normalizeIsoApp
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `normalizeIsoApp [`C `X]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `NatIso.ofComponents
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (CategoryTheory.CategoryTheory.Isomorphism.«term_≅_»
       (Term.app (Term.proj (Term.app `tensorFunc [`C]) "." `obj) [`X])
       " ≅ "
       (Term.app (Term.proj (Term.app `normalize' [`C]) "." `obj) [`X]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj (Term.app `normalize' [`C]) "." `obj) [`X])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `X
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app `normalize' [`C]) "." `obj)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `normalize' [`C])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `C
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `normalize'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `normalize' [`C]) ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      (Term.app (Term.proj (Term.app `tensorFunc [`C]) "." `obj) [`X])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `X
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app `tensorFunc [`C]) "." `obj)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `tensorFunc [`C])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `C
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `tensorFunc
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `tensorFunc [`C]) ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 11 >? 1022, (some 1023, term) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 10,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termF "F")
       [`C])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `C
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termF "F")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termF', expected 'CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termF._@.CategoryTheory.Monoidal.Free.Coherence._hyg.10'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/-- Auxiliary definition for `normalize_iso`. -/ @[ simp ]
  def
    normalizeIsoAux
    ( X : F C ) : tensorFunc C . obj X ≅ normalize' C . obj X
    := NatIso.ofComponents normalizeIsoApp C X by rintro ⟨ X ⟩ ⟨ Y ⟩ tidy
#align
  category_theory.free_monoidal_category.normalize_iso_aux CategoryTheory.FreeMonoidalCategory.normalizeIsoAux

section

variable {D : Type u} [Category.{u} D] {I : Type u} (f : I → D) (X : Discrete I)

-- TODO: move to discrete_category.lean, decide whether this should be a global simp lemma
@[simp]
theorem discrete_functor_obj_eq_as : (Discrete.functor f).obj X = f X.as :=
  rfl
#align
  category_theory.free_monoidal_category.discrete_functor_obj_eq_as CategoryTheory.FreeMonoidalCategory.discrete_functor_obj_eq_as

-- TODO: move to discrete_category.lean, decide whether this should be a global simp lemma
@[simp]
theorem discrete_functor_map_eq_id (g : X ⟶ X) : (Discrete.functor f).map g = 𝟙 _ := by tidy
#align
  category_theory.free_monoidal_category.discrete_functor_map_eq_id CategoryTheory.FreeMonoidalCategory.discrete_functor_map_eq_id

end

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "The isomorphism between `n ⊗ X` and `normalize X n` is natural (in both `X` and `n`, but\n    naturality in `n` is trivial and was \"proved\" in `normalize_iso_aux`). This is the real heart\n    of our proof of the coherence theorem. -/")]
      []
      []
      []
      []
      [])
     (Command.def
      "def"
      (Command.declId `normalizeIso [])
      (Command.optDeclSig
       []
       [(Term.typeSpec
         ":"
         (CategoryTheory.CategoryTheory.Isomorphism.«term_≅_»
          (Term.app `tensorFunc [`C])
          " ≅ "
          (Term.app `normalize' [`C])))])
      (Command.declValSimple
       ":="
       (Term.app
        `NatIso.ofComponents
        [(Term.app `normalizeIsoAux [`C])
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Std.Tactic.rintro
              "rintro"
              [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `X))
               (Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `Y))
               (Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `f))]
              [])
             []
             (Tactic.apply "apply" (Term.app `Quotient.induction_on [`f]))
             []
             (Tactic.intro "intro" [`f])
             []
             (Std.Tactic.Ext.«tacticExt___:_»
              "ext"
              [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `n))]
              [])
             []
             (Tactic.induction "induction" [`f] [] ["generalizing" [`n]] [])
             []
             (tactic__
              (cdotTk (patternIgnore (token.«· » "·")))
              [(Tactic.simp
                "simp"
                []
                []
                ["only"]
                ["["
                 [(Tactic.simpLemma [] [] `mk_id)
                  ","
                  (Tactic.simpLemma [] [] `Functor.map_id)
                  ","
                  (Tactic.simpLemma [] [] `category.id_comp)
                  ","
                  (Tactic.simpLemma [] [] `category.comp_id)]
                 "]"]
                [])])
             []
             (tactic__
              (cdotTk (patternIgnore (token.«· » "·")))
              [(Tactic.dsimp "dsimp" [] [] [] [] [])
               []
               (Tactic.simp
                "simp"
                []
                []
                ["only"]
                ["["
                 [(Tactic.simpLemma [] [] `id_tensor_associator_inv_naturality_assoc)
                  ","
                  (Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `pentagon_inv_assoc)
                  ","
                  (Tactic.simpLemma [] [] `tensor_hom_inv_id_assoc)
                  ","
                  (Tactic.simpLemma [] [] `tensor_id)
                  ","
                  (Tactic.simpLemma [] [] `category.id_comp)
                  ","
                  (Tactic.simpLemma [] [] `discrete.functor_map_id)
                  ","
                  (Tactic.simpLemma [] [] `comp_tensor_id)
                  ","
                  (Tactic.simpLemma [] [] `iso.cancel_iso_inv_left)
                  ","
                  (Tactic.simpLemma [] [] `category.assoc)]
                 "]"]
                [])
               []
               (Tactic.dsimp "dsimp" [] [] [] [] [])
               []
               (Tactic.simp
                "simp"
                []
                []
                ["only"]
                ["[" [(Tactic.simpLemma [] [] `category.comp_id)] "]"]
                [])])
             []
             (tactic__
              (cdotTk (patternIgnore (token.«· » "·")))
              [(Tactic.dsimp "dsimp" [] [] [] [] [])
               []
               (Tactic.simp
                "simp"
                []
                []
                ["only"]
                ["["
                 [(Tactic.simpLemma [] [] `discrete.functor_map_id)
                  ","
                  (Tactic.simpLemma [] [] `comp_tensor_id)
                  ","
                  (Tactic.simpLemma [] [] `category.assoc)
                  ","
                  (Tactic.simpLemma [] [] `pentagon_inv_assoc)
                  ","
                  (Tactic.simpLemma
                   []
                   [(patternIgnore (token.«← » "←"))]
                   `associator_inv_naturality_assoc)
                  ","
                  (Tactic.simpLemma [] [] `tensor_id)
                  ","
                  (Tactic.simpLemma [] [] `iso.cancel_iso_inv_left)]
                 "]"]
                [])
               []
               (Tactic.dsimp "dsimp" [] [] [] [] [])
               []
               (Tactic.simp
                "simp"
                []
                []
                ["only"]
                ["[" [(Tactic.simpLemma [] [] `category.comp_id)] "]"]
                [])])
             []
             (tactic__
              (cdotTk (patternIgnore (token.«· » "·")))
              [(Tactic.dsimp "dsimp" [] [] [] [] [])
               []
               (Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `triangle_assoc_comp_right_assoc)] "]")
                [])
               []
               (Tactic.simp
                "simp"
                []
                []
                ["only"]
                ["["
                 [(Tactic.simpLemma [] [] `discrete.functor_map_id)
                  ","
                  (Tactic.simpLemma [] [] `category.assoc)]
                 "]"]
                [])
               []
               (Tactic.cases "cases" [(Tactic.casesTarget [] `n)] [] [])
               []
               (Tactic.dsimp "dsimp" [] [] [] [] [])
               []
               (Tactic.simp
                "simp"
                []
                []
                ["only"]
                ["[" [(Tactic.simpLemma [] [] `category.comp_id)] "]"]
                [])])
             []
             (tactic__
              (cdotTk (patternIgnore (token.«· » "·")))
              [(Tactic.dsimp "dsimp" [] [] [] [] [])
               []
               (Tactic.simp
                "simp"
                []
                []
                ["only"]
                ["["
                 [(Tactic.simpLemma [] [] `triangle_assoc_comp_left_inv_assoc)
                  ","
                  (Tactic.simpLemma [] [] `inv_hom_id_tensor_assoc)
                  ","
                  (Tactic.simpLemma [] [] `tensor_id)
                  ","
                  (Tactic.simpLemma [] [] `category.id_comp)
                  ","
                  (Tactic.simpLemma [] [] `discrete.functor_map_id)]
                 "]"]
                [])
               []
               (Tactic.dsimp "dsimp" [] [] [] [] [])
               []
               (Tactic.simp
                "simp"
                []
                []
                ["only"]
                ["[" [(Tactic.simpLemma [] [] `category.comp_id)] "]"]
                [])
               []
               (Tactic.cases "cases" [(Tactic.casesTarget [] `n)] [] [])
               []
               (Tactic.simp "simp" [] [] [] [] [])])
             []
             (tactic__
              (cdotTk (patternIgnore (token.«· » "·")))
              [(Tactic.dsimp "dsimp" [] [] [] [] [])
               []
               (Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule
                   [(patternIgnore (token.«← » "←"))]
                   (Term.app
                    (Term.proj (Term.app `iso.inv_comp_eq [(Term.hole "_")]) "." (fieldIdx "2"))
                    [(Term.app `right_unitor_tensor [(Term.hole "_") (Term.hole "_")])]))
                  ","
                  (Tactic.rwRule [] `category.assoc)
                  ","
                  (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `right_unitor_naturality)]
                 "]")
                [])
               []
               (Tactic.simp
                "simp"
                []
                []
                ["only"]
                ["["
                 [(Tactic.simpLemma [] [] `iso.cancel_iso_inv_left)
                  ","
                  (Tactic.simpLemma [] [] `category.assoc)]
                 "]"]
                [])
               []
               (Tactic.congr "congr" [(num "1")])
               []
               (convert
                "convert"
                []
                (Term.proj (Term.app `category.comp_id [(Term.hole "_")]) "." `symm)
                [])
               []
               (convert
                "convert"
                []
                (Term.app
                 `discrete_functor_map_eq_id
                 [`inclusion_obj (Term.hole "_") (Term.hole "_")])
                [])
               []
               (Std.Tactic.Ext.«tacticExt___:_» "ext" [] [])
               []
               (Tactic.tacticRfl "rfl")])
             []
             (tactic__
              (cdotTk (patternIgnore (token.«· » "·")))
              [(Tactic.dsimp "dsimp" [] [] [] [] [])
               []
               (Tactic.simp
                "simp"
                []
                []
                ["only"]
                ["["
                 [(Tactic.simpLemma
                   []
                   [(patternIgnore (token.«← » "←"))]
                   (Term.app
                    (Term.proj (Term.app `iso.eq_comp_inv [(Term.hole "_")]) "." (fieldIdx "1"))
                    [(Term.app `right_unitor_tensor_inv [(Term.hole "_") (Term.hole "_")])]))
                  ","
                  (Tactic.simpLemma [] [] `right_unitor_conjugation)
                  ","
                  (Tactic.simpLemma [] [] `category.assoc)
                  ","
                  (Tactic.simpLemma [] [] `iso.hom_inv_id)
                  ","
                  (Tactic.simpLemma [] [] `iso.hom_inv_id_assoc)
                  ","
                  (Tactic.simpLemma [] [] `iso.inv_hom_id)
                  ","
                  (Tactic.simpLemma [] [] `iso.inv_hom_id_assoc)]
                 "]"]
                [])
               []
               (Tactic.congr "congr" [])
               []
               (convert
                "convert"
                []
                (Term.proj
                 (Term.app
                  `discrete_functor_map_eq_id
                  [`inclusion_obj (Term.hole "_") (Term.hole "_")])
                 "."
                 `symm)
                [])
               []
               (Std.Tactic.Ext.«tacticExt___:_» "ext" [] [])
               []
               (Tactic.tacticRfl "rfl")])
             []
             (tactic__
              (cdotTk (patternIgnore (token.«· » "·")))
              [(Tactic.dsimp
                "dsimp"
                []
                []
                []
                []
                [(Tactic.location "at" (Tactic.locationWildcard "*"))])
               []
               (Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule [] `id_tensor_comp)
                  ","
                  (Tactic.rwRule [] `category.assoc)
                  ","
                  (Tactic.rwRule
                   []
                   (Term.app `f_ih_g [(Quotient.Init.Data.Quot.«term⟦_⟧» "⟦" `f_g "⟧")]))
                  ","
                  (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `category.assoc)
                  ","
                  (Tactic.rwRule
                   []
                   (Term.app `f_ih_f [(Quotient.Init.Data.Quot.«term⟦_⟧» "⟦" `f_f "⟧")]))
                  ","
                  (Tactic.rwRule [] `category.assoc)
                  ","
                  (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `functor.map_comp)]
                 "]")
                [])
               []
               (Tactic.congr "congr" [(num "2")])])
             []
             (tactic__
              (cdotTk (patternIgnore (token.«· » "·")))
              [(Tactic.dsimp
                "dsimp"
                []
                []
                []
                []
                [(Tactic.location "at" (Tactic.locationWildcard "*"))])
               []
               (Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `associator_inv_naturality_assoc)] "]")
                [])
               []
               (Tactic.sliceLHS
                "slice_lhs"
                (num "2")
                (num "3")
                "=>"
                (Tactic.Conv.convSeq
                 (Tactic.Conv.convSeq1Indented
                  [(Tactic.Conv.convRw__
                    "rw"
                    []
                    (Tactic.rwRuleSeq
                     "["
                     [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `tensor_comp)
                      ","
                      (Tactic.rwRule
                       []
                       (Term.app `f_ih_f [(Quotient.Init.Data.Quot.«term⟦_⟧» "⟦" `f_f "⟧")]))]
                     "]"))])))
               []
               (Mathlib.Tactic.Conv.convLHS
                "conv_lhs"
                []
                []
                "=>"
                (Tactic.Conv.convSeq
                 (Tactic.Conv.convSeq1Indented
                  [(Tactic.Conv.convRw__
                    "rw"
                    []
                    (Tactic.rwRuleSeq
                     "["
                     [(Tactic.rwRule
                       [(patternIgnore (token.«← » "←"))]
                       (Term.app
                        (Term.explicit "@" `category.id_comp)
                        [(Term.app
                          (CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termF
                           "F")
                          [`C])
                         (Term.hole "_")
                         (Term.hole "_")
                         (Term.hole "_")
                         (Quotient.Init.Data.Quot.«term⟦_⟧» "⟦" `f_g "⟧")]))]
                     "]"))])))
               []
               (Tactic.simp
                "simp"
                []
                []
                ["only"]
                ["["
                 [(Tactic.simpLemma [] [] `category.comp_id)
                  ","
                  (Tactic.simpLemma [] [] `tensor_comp)
                  ","
                  (Tactic.simpLemma [] [] `category.assoc)]
                 "]"]
                [])
               []
               (Tactic.congr "congr" [(num "2")])
               []
               (Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `mk_tensor)
                  ","
                  (Tactic.rwRule [] `Quotient.lift_mk)]
                 "]")
                [])
               []
               (Tactic.dsimp "dsimp" [] [] [] [] [])
               []
               (Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule [] `functor.map_comp)
                  ","
                  (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `category.assoc)
                  ","
                  (Tactic.rwRule
                   [(patternIgnore (token.«← » "←"))]
                   (Term.app `f_ih_g [(Quotient.Init.Data.Quot.«term⟦_⟧» "⟦" `f_g "⟧")]))
                  ","
                  (Tactic.rwRule
                   [(patternIgnore (token.«← » "←"))]
                   (Term.app
                    (Term.explicit "@" `category.comp_id)
                    [(Term.app
                      (CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termF
                       "F")
                      [`C])
                     (Term.hole "_")
                     (Term.hole "_")
                     (Term.hole "_")
                     (Quotient.Init.Data.Quot.«term⟦_⟧» "⟦" `f_g "⟧")]))
                  ","
                  (Tactic.rwRule
                   [(patternIgnore (token.«← » "←"))]
                   (Term.app
                    `category.id_comp
                    [(Term.app
                      (Term.proj (Term.app `discrete.functor [`inclusion_obj]) "." `map)
                      [(Term.hole "_")])]))
                  ","
                  (Tactic.rwRule [] `tensor_comp)]
                 "]")
                [])
               []
               (Tactic.dsimp "dsimp" [] [] [] [] [])
               []
               (Tactic.simp
                "simp"
                []
                []
                ["only"]
                ["["
                 [(Tactic.simpLemma [] [] `category.assoc)
                  ","
                  (Tactic.simpLemma [] [] `category.comp_id)]
                 "]"]
                [])
               []
               (Tactic.congr "congr" [(num "1")])
               []
               (convert
                "convert"
                []
                (Term.app
                 (Term.proj
                  (Term.proj (Term.app `normalize_iso_aux [`C `f_Z]) "." `Hom)
                  "."
                  `naturality)
                 [(Term.app (Term.proj (Term.app `normalize_map_aux [`f_f]) "." `app) [`n])])
                [])
               []
               (Tactic.exact
                "exact"
                (Term.proj
                 (Term.app `tensor_func_obj_map [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
                 "."
                 `symm))])])))])
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `NatIso.ofComponents
       [(Term.app `normalizeIsoAux [`C])
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Std.Tactic.rintro
             "rintro"
             [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `X))
              (Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `Y))
              (Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `f))]
             [])
            []
            (Tactic.apply "apply" (Term.app `Quotient.induction_on [`f]))
            []
            (Tactic.intro "intro" [`f])
            []
            (Std.Tactic.Ext.«tacticExt___:_»
             "ext"
             [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `n))]
             [])
            []
            (Tactic.induction "induction" [`f] [] ["generalizing" [`n]] [])
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(Tactic.simp
               "simp"
               []
               []
               ["only"]
               ["["
                [(Tactic.simpLemma [] [] `mk_id)
                 ","
                 (Tactic.simpLemma [] [] `Functor.map_id)
                 ","
                 (Tactic.simpLemma [] [] `category.id_comp)
                 ","
                 (Tactic.simpLemma [] [] `category.comp_id)]
                "]"]
               [])])
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(Tactic.dsimp "dsimp" [] [] [] [] [])
              []
              (Tactic.simp
               "simp"
               []
               []
               ["only"]
               ["["
                [(Tactic.simpLemma [] [] `id_tensor_associator_inv_naturality_assoc)
                 ","
                 (Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `pentagon_inv_assoc)
                 ","
                 (Tactic.simpLemma [] [] `tensor_hom_inv_id_assoc)
                 ","
                 (Tactic.simpLemma [] [] `tensor_id)
                 ","
                 (Tactic.simpLemma [] [] `category.id_comp)
                 ","
                 (Tactic.simpLemma [] [] `discrete.functor_map_id)
                 ","
                 (Tactic.simpLemma [] [] `comp_tensor_id)
                 ","
                 (Tactic.simpLemma [] [] `iso.cancel_iso_inv_left)
                 ","
                 (Tactic.simpLemma [] [] `category.assoc)]
                "]"]
               [])
              []
              (Tactic.dsimp "dsimp" [] [] [] [] [])
              []
              (Tactic.simp
               "simp"
               []
               []
               ["only"]
               ["[" [(Tactic.simpLemma [] [] `category.comp_id)] "]"]
               [])])
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(Tactic.dsimp "dsimp" [] [] [] [] [])
              []
              (Tactic.simp
               "simp"
               []
               []
               ["only"]
               ["["
                [(Tactic.simpLemma [] [] `discrete.functor_map_id)
                 ","
                 (Tactic.simpLemma [] [] `comp_tensor_id)
                 ","
                 (Tactic.simpLemma [] [] `category.assoc)
                 ","
                 (Tactic.simpLemma [] [] `pentagon_inv_assoc)
                 ","
                 (Tactic.simpLemma
                  []
                  [(patternIgnore (token.«← » "←"))]
                  `associator_inv_naturality_assoc)
                 ","
                 (Tactic.simpLemma [] [] `tensor_id)
                 ","
                 (Tactic.simpLemma [] [] `iso.cancel_iso_inv_left)]
                "]"]
               [])
              []
              (Tactic.dsimp "dsimp" [] [] [] [] [])
              []
              (Tactic.simp
               "simp"
               []
               []
               ["only"]
               ["[" [(Tactic.simpLemma [] [] `category.comp_id)] "]"]
               [])])
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(Tactic.dsimp "dsimp" [] [] [] [] [])
              []
              (Tactic.rwSeq
               "rw"
               []
               (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `triangle_assoc_comp_right_assoc)] "]")
               [])
              []
              (Tactic.simp
               "simp"
               []
               []
               ["only"]
               ["["
                [(Tactic.simpLemma [] [] `discrete.functor_map_id)
                 ","
                 (Tactic.simpLemma [] [] `category.assoc)]
                "]"]
               [])
              []
              (Tactic.cases "cases" [(Tactic.casesTarget [] `n)] [] [])
              []
              (Tactic.dsimp "dsimp" [] [] [] [] [])
              []
              (Tactic.simp
               "simp"
               []
               []
               ["only"]
               ["[" [(Tactic.simpLemma [] [] `category.comp_id)] "]"]
               [])])
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(Tactic.dsimp "dsimp" [] [] [] [] [])
              []
              (Tactic.simp
               "simp"
               []
               []
               ["only"]
               ["["
                [(Tactic.simpLemma [] [] `triangle_assoc_comp_left_inv_assoc)
                 ","
                 (Tactic.simpLemma [] [] `inv_hom_id_tensor_assoc)
                 ","
                 (Tactic.simpLemma [] [] `tensor_id)
                 ","
                 (Tactic.simpLemma [] [] `category.id_comp)
                 ","
                 (Tactic.simpLemma [] [] `discrete.functor_map_id)]
                "]"]
               [])
              []
              (Tactic.dsimp "dsimp" [] [] [] [] [])
              []
              (Tactic.simp
               "simp"
               []
               []
               ["only"]
               ["[" [(Tactic.simpLemma [] [] `category.comp_id)] "]"]
               [])
              []
              (Tactic.cases "cases" [(Tactic.casesTarget [] `n)] [] [])
              []
              (Tactic.simp "simp" [] [] [] [] [])])
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(Tactic.dsimp "dsimp" [] [] [] [] [])
              []
              (Tactic.rwSeq
               "rw"
               []
               (Tactic.rwRuleSeq
                "["
                [(Tactic.rwRule
                  [(patternIgnore (token.«← » "←"))]
                  (Term.app
                   (Term.proj (Term.app `iso.inv_comp_eq [(Term.hole "_")]) "." (fieldIdx "2"))
                   [(Term.app `right_unitor_tensor [(Term.hole "_") (Term.hole "_")])]))
                 ","
                 (Tactic.rwRule [] `category.assoc)
                 ","
                 (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `right_unitor_naturality)]
                "]")
               [])
              []
              (Tactic.simp
               "simp"
               []
               []
               ["only"]
               ["["
                [(Tactic.simpLemma [] [] `iso.cancel_iso_inv_left)
                 ","
                 (Tactic.simpLemma [] [] `category.assoc)]
                "]"]
               [])
              []
              (Tactic.congr "congr" [(num "1")])
              []
              (convert
               "convert"
               []
               (Term.proj (Term.app `category.comp_id [(Term.hole "_")]) "." `symm)
               [])
              []
              (convert
               "convert"
               []
               (Term.app
                `discrete_functor_map_eq_id
                [`inclusion_obj (Term.hole "_") (Term.hole "_")])
               [])
              []
              (Std.Tactic.Ext.«tacticExt___:_» "ext" [] [])
              []
              (Tactic.tacticRfl "rfl")])
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(Tactic.dsimp "dsimp" [] [] [] [] [])
              []
              (Tactic.simp
               "simp"
               []
               []
               ["only"]
               ["["
                [(Tactic.simpLemma
                  []
                  [(patternIgnore (token.«← » "←"))]
                  (Term.app
                   (Term.proj (Term.app `iso.eq_comp_inv [(Term.hole "_")]) "." (fieldIdx "1"))
                   [(Term.app `right_unitor_tensor_inv [(Term.hole "_") (Term.hole "_")])]))
                 ","
                 (Tactic.simpLemma [] [] `right_unitor_conjugation)
                 ","
                 (Tactic.simpLemma [] [] `category.assoc)
                 ","
                 (Tactic.simpLemma [] [] `iso.hom_inv_id)
                 ","
                 (Tactic.simpLemma [] [] `iso.hom_inv_id_assoc)
                 ","
                 (Tactic.simpLemma [] [] `iso.inv_hom_id)
                 ","
                 (Tactic.simpLemma [] [] `iso.inv_hom_id_assoc)]
                "]"]
               [])
              []
              (Tactic.congr "congr" [])
              []
              (convert
               "convert"
               []
               (Term.proj
                (Term.app
                 `discrete_functor_map_eq_id
                 [`inclusion_obj (Term.hole "_") (Term.hole "_")])
                "."
                `symm)
               [])
              []
              (Std.Tactic.Ext.«tacticExt___:_» "ext" [] [])
              []
              (Tactic.tacticRfl "rfl")])
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(Tactic.dsimp
               "dsimp"
               []
               []
               []
               []
               [(Tactic.location "at" (Tactic.locationWildcard "*"))])
              []
              (Tactic.rwSeq
               "rw"
               []
               (Tactic.rwRuleSeq
                "["
                [(Tactic.rwRule [] `id_tensor_comp)
                 ","
                 (Tactic.rwRule [] `category.assoc)
                 ","
                 (Tactic.rwRule
                  []
                  (Term.app `f_ih_g [(Quotient.Init.Data.Quot.«term⟦_⟧» "⟦" `f_g "⟧")]))
                 ","
                 (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `category.assoc)
                 ","
                 (Tactic.rwRule
                  []
                  (Term.app `f_ih_f [(Quotient.Init.Data.Quot.«term⟦_⟧» "⟦" `f_f "⟧")]))
                 ","
                 (Tactic.rwRule [] `category.assoc)
                 ","
                 (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `functor.map_comp)]
                "]")
               [])
              []
              (Tactic.congr "congr" [(num "2")])])
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(Tactic.dsimp
               "dsimp"
               []
               []
               []
               []
               [(Tactic.location "at" (Tactic.locationWildcard "*"))])
              []
              (Tactic.rwSeq
               "rw"
               []
               (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `associator_inv_naturality_assoc)] "]")
               [])
              []
              (Tactic.sliceLHS
               "slice_lhs"
               (num "2")
               (num "3")
               "=>"
               (Tactic.Conv.convSeq
                (Tactic.Conv.convSeq1Indented
                 [(Tactic.Conv.convRw__
                   "rw"
                   []
                   (Tactic.rwRuleSeq
                    "["
                    [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `tensor_comp)
                     ","
                     (Tactic.rwRule
                      []
                      (Term.app `f_ih_f [(Quotient.Init.Data.Quot.«term⟦_⟧» "⟦" `f_f "⟧")]))]
                    "]"))])))
              []
              (Mathlib.Tactic.Conv.convLHS
               "conv_lhs"
               []
               []
               "=>"
               (Tactic.Conv.convSeq
                (Tactic.Conv.convSeq1Indented
                 [(Tactic.Conv.convRw__
                   "rw"
                   []
                   (Tactic.rwRuleSeq
                    "["
                    [(Tactic.rwRule
                      [(patternIgnore (token.«← » "←"))]
                      (Term.app
                       (Term.explicit "@" `category.id_comp)
                       [(Term.app
                         (CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termF
                          "F")
                         [`C])
                        (Term.hole "_")
                        (Term.hole "_")
                        (Term.hole "_")
                        (Quotient.Init.Data.Quot.«term⟦_⟧» "⟦" `f_g "⟧")]))]
                    "]"))])))
              []
              (Tactic.simp
               "simp"
               []
               []
               ["only"]
               ["["
                [(Tactic.simpLemma [] [] `category.comp_id)
                 ","
                 (Tactic.simpLemma [] [] `tensor_comp)
                 ","
                 (Tactic.simpLemma [] [] `category.assoc)]
                "]"]
               [])
              []
              (Tactic.congr "congr" [(num "2")])
              []
              (Tactic.rwSeq
               "rw"
               []
               (Tactic.rwRuleSeq
                "["
                [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `mk_tensor)
                 ","
                 (Tactic.rwRule [] `Quotient.lift_mk)]
                "]")
               [])
              []
              (Tactic.dsimp "dsimp" [] [] [] [] [])
              []
              (Tactic.rwSeq
               "rw"
               []
               (Tactic.rwRuleSeq
                "["
                [(Tactic.rwRule [] `functor.map_comp)
                 ","
                 (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `category.assoc)
                 ","
                 (Tactic.rwRule
                  [(patternIgnore (token.«← » "←"))]
                  (Term.app `f_ih_g [(Quotient.Init.Data.Quot.«term⟦_⟧» "⟦" `f_g "⟧")]))
                 ","
                 (Tactic.rwRule
                  [(patternIgnore (token.«← » "←"))]
                  (Term.app
                   (Term.explicit "@" `category.comp_id)
                   [(Term.app
                     (CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termF
                      "F")
                     [`C])
                    (Term.hole "_")
                    (Term.hole "_")
                    (Term.hole "_")
                    (Quotient.Init.Data.Quot.«term⟦_⟧» "⟦" `f_g "⟧")]))
                 ","
                 (Tactic.rwRule
                  [(patternIgnore (token.«← » "←"))]
                  (Term.app
                   `category.id_comp
                   [(Term.app
                     (Term.proj (Term.app `discrete.functor [`inclusion_obj]) "." `map)
                     [(Term.hole "_")])]))
                 ","
                 (Tactic.rwRule [] `tensor_comp)]
                "]")
               [])
              []
              (Tactic.dsimp "dsimp" [] [] [] [] [])
              []
              (Tactic.simp
               "simp"
               []
               []
               ["only"]
               ["["
                [(Tactic.simpLemma [] [] `category.assoc)
                 ","
                 (Tactic.simpLemma [] [] `category.comp_id)]
                "]"]
               [])
              []
              (Tactic.congr "congr" [(num "1")])
              []
              (convert
               "convert"
               []
               (Term.app
                (Term.proj
                 (Term.proj (Term.app `normalize_iso_aux [`C `f_Z]) "." `Hom)
                 "."
                 `naturality)
                [(Term.app (Term.proj (Term.app `normalize_map_aux [`f_f]) "." `app) [`n])])
               [])
              []
              (Tactic.exact
               "exact"
               (Term.proj
                (Term.app `tensor_func_obj_map [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
                "."
                `symm))])])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Std.Tactic.rintro
           "rintro"
           [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `X))
            (Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `Y))
            (Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `f))]
           [])
          []
          (Tactic.apply "apply" (Term.app `Quotient.induction_on [`f]))
          []
          (Tactic.intro "intro" [`f])
          []
          (Std.Tactic.Ext.«tacticExt___:_»
           "ext"
           [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `n))]
           [])
          []
          (Tactic.induction "induction" [`f] [] ["generalizing" [`n]] [])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.simp
             "simp"
             []
             []
             ["only"]
             ["["
              [(Tactic.simpLemma [] [] `mk_id)
               ","
               (Tactic.simpLemma [] [] `Functor.map_id)
               ","
               (Tactic.simpLemma [] [] `category.id_comp)
               ","
               (Tactic.simpLemma [] [] `category.comp_id)]
              "]"]
             [])])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.dsimp "dsimp" [] [] [] [] [])
            []
            (Tactic.simp
             "simp"
             []
             []
             ["only"]
             ["["
              [(Tactic.simpLemma [] [] `id_tensor_associator_inv_naturality_assoc)
               ","
               (Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `pentagon_inv_assoc)
               ","
               (Tactic.simpLemma [] [] `tensor_hom_inv_id_assoc)
               ","
               (Tactic.simpLemma [] [] `tensor_id)
               ","
               (Tactic.simpLemma [] [] `category.id_comp)
               ","
               (Tactic.simpLemma [] [] `discrete.functor_map_id)
               ","
               (Tactic.simpLemma [] [] `comp_tensor_id)
               ","
               (Tactic.simpLemma [] [] `iso.cancel_iso_inv_left)
               ","
               (Tactic.simpLemma [] [] `category.assoc)]
              "]"]
             [])
            []
            (Tactic.dsimp "dsimp" [] [] [] [] [])
            []
            (Tactic.simp
             "simp"
             []
             []
             ["only"]
             ["[" [(Tactic.simpLemma [] [] `category.comp_id)] "]"]
             [])])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.dsimp "dsimp" [] [] [] [] [])
            []
            (Tactic.simp
             "simp"
             []
             []
             ["only"]
             ["["
              [(Tactic.simpLemma [] [] `discrete.functor_map_id)
               ","
               (Tactic.simpLemma [] [] `comp_tensor_id)
               ","
               (Tactic.simpLemma [] [] `category.assoc)
               ","
               (Tactic.simpLemma [] [] `pentagon_inv_assoc)
               ","
               (Tactic.simpLemma
                []
                [(patternIgnore (token.«← » "←"))]
                `associator_inv_naturality_assoc)
               ","
               (Tactic.simpLemma [] [] `tensor_id)
               ","
               (Tactic.simpLemma [] [] `iso.cancel_iso_inv_left)]
              "]"]
             [])
            []
            (Tactic.dsimp "dsimp" [] [] [] [] [])
            []
            (Tactic.simp
             "simp"
             []
             []
             ["only"]
             ["[" [(Tactic.simpLemma [] [] `category.comp_id)] "]"]
             [])])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.dsimp "dsimp" [] [] [] [] [])
            []
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `triangle_assoc_comp_right_assoc)] "]")
             [])
            []
            (Tactic.simp
             "simp"
             []
             []
             ["only"]
             ["["
              [(Tactic.simpLemma [] [] `discrete.functor_map_id)
               ","
               (Tactic.simpLemma [] [] `category.assoc)]
              "]"]
             [])
            []
            (Tactic.cases "cases" [(Tactic.casesTarget [] `n)] [] [])
            []
            (Tactic.dsimp "dsimp" [] [] [] [] [])
            []
            (Tactic.simp
             "simp"
             []
             []
             ["only"]
             ["[" [(Tactic.simpLemma [] [] `category.comp_id)] "]"]
             [])])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.dsimp "dsimp" [] [] [] [] [])
            []
            (Tactic.simp
             "simp"
             []
             []
             ["only"]
             ["["
              [(Tactic.simpLemma [] [] `triangle_assoc_comp_left_inv_assoc)
               ","
               (Tactic.simpLemma [] [] `inv_hom_id_tensor_assoc)
               ","
               (Tactic.simpLemma [] [] `tensor_id)
               ","
               (Tactic.simpLemma [] [] `category.id_comp)
               ","
               (Tactic.simpLemma [] [] `discrete.functor_map_id)]
              "]"]
             [])
            []
            (Tactic.dsimp "dsimp" [] [] [] [] [])
            []
            (Tactic.simp
             "simp"
             []
             []
             ["only"]
             ["[" [(Tactic.simpLemma [] [] `category.comp_id)] "]"]
             [])
            []
            (Tactic.cases "cases" [(Tactic.casesTarget [] `n)] [] [])
            []
            (Tactic.simp "simp" [] [] [] [] [])])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.dsimp "dsimp" [] [] [] [] [])
            []
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule
                [(patternIgnore (token.«← » "←"))]
                (Term.app
                 (Term.proj (Term.app `iso.inv_comp_eq [(Term.hole "_")]) "." (fieldIdx "2"))
                 [(Term.app `right_unitor_tensor [(Term.hole "_") (Term.hole "_")])]))
               ","
               (Tactic.rwRule [] `category.assoc)
               ","
               (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `right_unitor_naturality)]
              "]")
             [])
            []
            (Tactic.simp
             "simp"
             []
             []
             ["only"]
             ["["
              [(Tactic.simpLemma [] [] `iso.cancel_iso_inv_left)
               ","
               (Tactic.simpLemma [] [] `category.assoc)]
              "]"]
             [])
            []
            (Tactic.congr "congr" [(num "1")])
            []
            (convert
             "convert"
             []
             (Term.proj (Term.app `category.comp_id [(Term.hole "_")]) "." `symm)
             [])
            []
            (convert
             "convert"
             []
             (Term.app `discrete_functor_map_eq_id [`inclusion_obj (Term.hole "_") (Term.hole "_")])
             [])
            []
            (Std.Tactic.Ext.«tacticExt___:_» "ext" [] [])
            []
            (Tactic.tacticRfl "rfl")])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.dsimp "dsimp" [] [] [] [] [])
            []
            (Tactic.simp
             "simp"
             []
             []
             ["only"]
             ["["
              [(Tactic.simpLemma
                []
                [(patternIgnore (token.«← » "←"))]
                (Term.app
                 (Term.proj (Term.app `iso.eq_comp_inv [(Term.hole "_")]) "." (fieldIdx "1"))
                 [(Term.app `right_unitor_tensor_inv [(Term.hole "_") (Term.hole "_")])]))
               ","
               (Tactic.simpLemma [] [] `right_unitor_conjugation)
               ","
               (Tactic.simpLemma [] [] `category.assoc)
               ","
               (Tactic.simpLemma [] [] `iso.hom_inv_id)
               ","
               (Tactic.simpLemma [] [] `iso.hom_inv_id_assoc)
               ","
               (Tactic.simpLemma [] [] `iso.inv_hom_id)
               ","
               (Tactic.simpLemma [] [] `iso.inv_hom_id_assoc)]
              "]"]
             [])
            []
            (Tactic.congr "congr" [])
            []
            (convert
             "convert"
             []
             (Term.proj
              (Term.app
               `discrete_functor_map_eq_id
               [`inclusion_obj (Term.hole "_") (Term.hole "_")])
              "."
              `symm)
             [])
            []
            (Std.Tactic.Ext.«tacticExt___:_» "ext" [] [])
            []
            (Tactic.tacticRfl "rfl")])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.dsimp
             "dsimp"
             []
             []
             []
             []
             [(Tactic.location "at" (Tactic.locationWildcard "*"))])
            []
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] `id_tensor_comp)
               ","
               (Tactic.rwRule [] `category.assoc)
               ","
               (Tactic.rwRule
                []
                (Term.app `f_ih_g [(Quotient.Init.Data.Quot.«term⟦_⟧» "⟦" `f_g "⟧")]))
               ","
               (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `category.assoc)
               ","
               (Tactic.rwRule
                []
                (Term.app `f_ih_f [(Quotient.Init.Data.Quot.«term⟦_⟧» "⟦" `f_f "⟧")]))
               ","
               (Tactic.rwRule [] `category.assoc)
               ","
               (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `functor.map_comp)]
              "]")
             [])
            []
            (Tactic.congr "congr" [(num "2")])])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.dsimp
             "dsimp"
             []
             []
             []
             []
             [(Tactic.location "at" (Tactic.locationWildcard "*"))])
            []
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `associator_inv_naturality_assoc)] "]")
             [])
            []
            (Tactic.sliceLHS
             "slice_lhs"
             (num "2")
             (num "3")
             "=>"
             (Tactic.Conv.convSeq
              (Tactic.Conv.convSeq1Indented
               [(Tactic.Conv.convRw__
                 "rw"
                 []
                 (Tactic.rwRuleSeq
                  "["
                  [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `tensor_comp)
                   ","
                   (Tactic.rwRule
                    []
                    (Term.app `f_ih_f [(Quotient.Init.Data.Quot.«term⟦_⟧» "⟦" `f_f "⟧")]))]
                  "]"))])))
            []
            (Mathlib.Tactic.Conv.convLHS
             "conv_lhs"
             []
             []
             "=>"
             (Tactic.Conv.convSeq
              (Tactic.Conv.convSeq1Indented
               [(Tactic.Conv.convRw__
                 "rw"
                 []
                 (Tactic.rwRuleSeq
                  "["
                  [(Tactic.rwRule
                    [(patternIgnore (token.«← » "←"))]
                    (Term.app
                     (Term.explicit "@" `category.id_comp)
                     [(Term.app
                       (CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termF
                        "F")
                       [`C])
                      (Term.hole "_")
                      (Term.hole "_")
                      (Term.hole "_")
                      (Quotient.Init.Data.Quot.«term⟦_⟧» "⟦" `f_g "⟧")]))]
                  "]"))])))
            []
            (Tactic.simp
             "simp"
             []
             []
             ["only"]
             ["["
              [(Tactic.simpLemma [] [] `category.comp_id)
               ","
               (Tactic.simpLemma [] [] `tensor_comp)
               ","
               (Tactic.simpLemma [] [] `category.assoc)]
              "]"]
             [])
            []
            (Tactic.congr "congr" [(num "2")])
            []
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `mk_tensor)
               ","
               (Tactic.rwRule [] `Quotient.lift_mk)]
              "]")
             [])
            []
            (Tactic.dsimp "dsimp" [] [] [] [] [])
            []
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] `functor.map_comp)
               ","
               (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `category.assoc)
               ","
               (Tactic.rwRule
                [(patternIgnore (token.«← » "←"))]
                (Term.app `f_ih_g [(Quotient.Init.Data.Quot.«term⟦_⟧» "⟦" `f_g "⟧")]))
               ","
               (Tactic.rwRule
                [(patternIgnore (token.«← » "←"))]
                (Term.app
                 (Term.explicit "@" `category.comp_id)
                 [(Term.app
                   (CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termF
                    "F")
                   [`C])
                  (Term.hole "_")
                  (Term.hole "_")
                  (Term.hole "_")
                  (Quotient.Init.Data.Quot.«term⟦_⟧» "⟦" `f_g "⟧")]))
               ","
               (Tactic.rwRule
                [(patternIgnore (token.«← » "←"))]
                (Term.app
                 `category.id_comp
                 [(Term.app
                   (Term.proj (Term.app `discrete.functor [`inclusion_obj]) "." `map)
                   [(Term.hole "_")])]))
               ","
               (Tactic.rwRule [] `tensor_comp)]
              "]")
             [])
            []
            (Tactic.dsimp "dsimp" [] [] [] [] [])
            []
            (Tactic.simp
             "simp"
             []
             []
             ["only"]
             ["["
              [(Tactic.simpLemma [] [] `category.assoc)
               ","
               (Tactic.simpLemma [] [] `category.comp_id)]
              "]"]
             [])
            []
            (Tactic.congr "congr" [(num "1")])
            []
            (convert
             "convert"
             []
             (Term.app
              (Term.proj
               (Term.proj (Term.app `normalize_iso_aux [`C `f_Z]) "." `Hom)
               "."
               `naturality)
              [(Term.app (Term.proj (Term.app `normalize_map_aux [`f_f]) "." `app) [`n])])
             [])
            []
            (Tactic.exact
             "exact"
             (Term.proj
              (Term.app `tensor_func_obj_map [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
              "."
              `symm))])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.dsimp "dsimp" [] [] [] [] [(Tactic.location "at" (Tactic.locationWildcard "*"))])
        []
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `associator_inv_naturality_assoc)] "]")
         [])
        []
        (Tactic.sliceLHS
         "slice_lhs"
         (num "2")
         (num "3")
         "=>"
         (Tactic.Conv.convSeq
          (Tactic.Conv.convSeq1Indented
           [(Tactic.Conv.convRw__
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `tensor_comp)
               ","
               (Tactic.rwRule
                []
                (Term.app `f_ih_f [(Quotient.Init.Data.Quot.«term⟦_⟧» "⟦" `f_f "⟧")]))]
              "]"))])))
        []
        (Mathlib.Tactic.Conv.convLHS
         "conv_lhs"
         []
         []
         "=>"
         (Tactic.Conv.convSeq
          (Tactic.Conv.convSeq1Indented
           [(Tactic.Conv.convRw__
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule
                [(patternIgnore (token.«← » "←"))]
                (Term.app
                 (Term.explicit "@" `category.id_comp)
                 [(Term.app
                   (CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termF
                    "F")
                   [`C])
                  (Term.hole "_")
                  (Term.hole "_")
                  (Term.hole "_")
                  (Quotient.Init.Data.Quot.«term⟦_⟧» "⟦" `f_g "⟧")]))]
              "]"))])))
        []
        (Tactic.simp
         "simp"
         []
         []
         ["only"]
         ["["
          [(Tactic.simpLemma [] [] `category.comp_id)
           ","
           (Tactic.simpLemma [] [] `tensor_comp)
           ","
           (Tactic.simpLemma [] [] `category.assoc)]
          "]"]
         [])
        []
        (Tactic.congr "congr" [(num "2")])
        []
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `mk_tensor)
           ","
           (Tactic.rwRule [] `Quotient.lift_mk)]
          "]")
         [])
        []
        (Tactic.dsimp "dsimp" [] [] [] [] [])
        []
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule [] `functor.map_comp)
           ","
           (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `category.assoc)
           ","
           (Tactic.rwRule
            [(patternIgnore (token.«← » "←"))]
            (Term.app `f_ih_g [(Quotient.Init.Data.Quot.«term⟦_⟧» "⟦" `f_g "⟧")]))
           ","
           (Tactic.rwRule
            [(patternIgnore (token.«← » "←"))]
            (Term.app
             (Term.explicit "@" `category.comp_id)
             [(Term.app
               (CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termF
                "F")
               [`C])
              (Term.hole "_")
              (Term.hole "_")
              (Term.hole "_")
              (Quotient.Init.Data.Quot.«term⟦_⟧» "⟦" `f_g "⟧")]))
           ","
           (Tactic.rwRule
            [(patternIgnore (token.«← » "←"))]
            (Term.app
             `category.id_comp
             [(Term.app
               (Term.proj (Term.app `discrete.functor [`inclusion_obj]) "." `map)
               [(Term.hole "_")])]))
           ","
           (Tactic.rwRule [] `tensor_comp)]
          "]")
         [])
        []
        (Tactic.dsimp "dsimp" [] [] [] [] [])
        []
        (Tactic.simp
         "simp"
         []
         []
         ["only"]
         ["["
          [(Tactic.simpLemma [] [] `category.assoc) "," (Tactic.simpLemma [] [] `category.comp_id)]
          "]"]
         [])
        []
        (Tactic.congr "congr" [(num "1")])
        []
        (convert
         "convert"
         []
         (Term.app
          (Term.proj (Term.proj (Term.app `normalize_iso_aux [`C `f_Z]) "." `Hom) "." `naturality)
          [(Term.app (Term.proj (Term.app `normalize_map_aux [`f_f]) "." `app) [`n])])
         [])
        []
        (Tactic.exact
         "exact"
         (Term.proj
          (Term.app `tensor_func_obj_map [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
          "."
          `symm))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.proj
        (Term.app `tensor_func_obj_map [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
        "."
        `symm))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj
       (Term.app `tensor_func_obj_map [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
       "."
       `symm)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `tensor_func_obj_map [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
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
      `tensor_func_obj_map
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `tensor_func_obj_map [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (convert
       "convert"
       []
       (Term.app
        (Term.proj (Term.proj (Term.app `normalize_iso_aux [`C `f_Z]) "." `Hom) "." `naturality)
        [(Term.app (Term.proj (Term.app `normalize_map_aux [`f_f]) "." `app) [`n])])
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj (Term.proj (Term.app `normalize_iso_aux [`C `f_Z]) "." `Hom) "." `naturality)
       [(Term.app (Term.proj (Term.app `normalize_map_aux [`f_f]) "." `app) [`n])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj (Term.app `normalize_map_aux [`f_f]) "." `app) [`n])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app `normalize_map_aux [`f_f]) "." `app)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `normalize_map_aux [`f_f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f_f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `normalize_map_aux
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `normalize_map_aux [`f_f])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.proj (Term.paren "(" (Term.app `normalize_map_aux [`f_f]) ")") "." `app) [`n])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.proj (Term.app `normalize_iso_aux [`C `f_Z]) "." `Hom) "." `naturality)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj (Term.app `normalize_iso_aux [`C `f_Z]) "." `Hom)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `normalize_iso_aux [`C `f_Z])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f_Z
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `C
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `normalize_iso_aux
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `normalize_iso_aux [`C `f_Z])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.congr "congr" [(num "1")])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["["
        [(Tactic.simpLemma [] [] `category.assoc) "," (Tactic.simpLemma [] [] `category.comp_id)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `category.comp_id
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `category.assoc
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.dsimp "dsimp" [] [] [] [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `functor.map_comp)
         ","
         (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `category.assoc)
         ","
         (Tactic.rwRule
          [(patternIgnore (token.«← » "←"))]
          (Term.app `f_ih_g [(Quotient.Init.Data.Quot.«term⟦_⟧» "⟦" `f_g "⟧")]))
         ","
         (Tactic.rwRule
          [(patternIgnore (token.«← » "←"))]
          (Term.app
           (Term.explicit "@" `category.comp_id)
           [(Term.app
             (CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termF "F")
             [`C])
            (Term.hole "_")
            (Term.hole "_")
            (Term.hole "_")
            (Quotient.Init.Data.Quot.«term⟦_⟧» "⟦" `f_g "⟧")]))
         ","
         (Tactic.rwRule
          [(patternIgnore (token.«← » "←"))]
          (Term.app
           `category.id_comp
           [(Term.app
             (Term.proj (Term.app `discrete.functor [`inclusion_obj]) "." `map)
             [(Term.hole "_")])]))
         ","
         (Tactic.rwRule [] `tensor_comp)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `tensor_comp
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `category.id_comp
       [(Term.app
         (Term.proj (Term.app `discrete.functor [`inclusion_obj]) "." `map)
         [(Term.hole "_")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj (Term.app `discrete.functor [`inclusion_obj]) "." `map)
       [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app `discrete.functor [`inclusion_obj]) "." `map)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `discrete.functor [`inclusion_obj])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `inclusion_obj
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `discrete.functor
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `discrete.functor [`inclusion_obj])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      (Term.proj (Term.paren "(" (Term.app `discrete.functor [`inclusion_obj]) ")") "." `map)
      [(Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `category.id_comp
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.explicit "@" `category.comp_id)
       [(Term.app
         (CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termF "F")
         [`C])
        (Term.hole "_")
        (Term.hole "_")
        (Term.hole "_")
        (Quotient.Init.Data.Quot.«term⟦_⟧» "⟦" `f_g "⟧")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Quotient.Init.Data.Quot.«term⟦_⟧»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Quotient.Init.Data.Quot.«term⟦_⟧»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Quotient.Init.Data.Quot.«term⟦_⟧» "⟦" `f_g "⟧")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f_g
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1023, (none,
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.app
       (CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termF "F")
       [`C])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `C
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termF "F")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termF', expected 'CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termF._@.CategoryTheory.Monoidal.Free.Coherence._hyg.10'
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
    The isomorphism between `n ⊗ X` and `normalize X n` is natural (in both `X` and `n`, but
        naturality in `n` is trivial and was "proved" in `normalize_iso_aux`). This is the real heart
        of our proof of the coherence theorem. -/
  def
    normalizeIso
    : tensorFunc C ≅ normalize' C
    :=
      NatIso.ofComponents
        normalizeIsoAux C
          by
            rintro X Y f
              apply Quotient.induction_on f
              intro f
              ext n
              induction f generalizing n
              · simp only [ mk_id , Functor.map_id , category.id_comp , category.comp_id ]
              ·
                dsimp
                  simp
                    only
                    [
                      id_tensor_associator_inv_naturality_assoc
                        ,
                        ← pentagon_inv_assoc
                        ,
                        tensor_hom_inv_id_assoc
                        ,
                        tensor_id
                        ,
                        category.id_comp
                        ,
                        discrete.functor_map_id
                        ,
                        comp_tensor_id
                        ,
                        iso.cancel_iso_inv_left
                        ,
                        category.assoc
                      ]
                  dsimp
                  simp only [ category.comp_id ]
              ·
                dsimp
                  simp
                    only
                    [
                      discrete.functor_map_id
                        ,
                        comp_tensor_id
                        ,
                        category.assoc
                        ,
                        pentagon_inv_assoc
                        ,
                        ← associator_inv_naturality_assoc
                        ,
                        tensor_id
                        ,
                        iso.cancel_iso_inv_left
                      ]
                  dsimp
                  simp only [ category.comp_id ]
              ·
                dsimp
                  rw [ triangle_assoc_comp_right_assoc ]
                  simp only [ discrete.functor_map_id , category.assoc ]
                  cases n
                  dsimp
                  simp only [ category.comp_id ]
              ·
                dsimp
                  simp
                    only
                    [
                      triangle_assoc_comp_left_inv_assoc
                        ,
                        inv_hom_id_tensor_assoc
                        ,
                        tensor_id
                        ,
                        category.id_comp
                        ,
                        discrete.functor_map_id
                      ]
                  dsimp
                  simp only [ category.comp_id ]
                  cases n
                  simp
              ·
                dsimp
                  rw
                    [
                      ← iso.inv_comp_eq _ . 2 right_unitor_tensor _ _
                        ,
                        category.assoc
                        ,
                        ← right_unitor_naturality
                      ]
                  simp only [ iso.cancel_iso_inv_left , category.assoc ]
                  congr 1
                  convert category.comp_id _ . symm
                  convert discrete_functor_map_eq_id inclusion_obj _ _
                  ext
                  rfl
              ·
                dsimp
                  simp
                    only
                    [
                      ← iso.eq_comp_inv _ . 1 right_unitor_tensor_inv _ _
                        ,
                        right_unitor_conjugation
                        ,
                        category.assoc
                        ,
                        iso.hom_inv_id
                        ,
                        iso.hom_inv_id_assoc
                        ,
                        iso.inv_hom_id
                        ,
                        iso.inv_hom_id_assoc
                      ]
                  congr
                  convert discrete_functor_map_eq_id inclusion_obj _ _ . symm
                  ext
                  rfl
              ·
                dsimp at *
                  rw
                    [
                      id_tensor_comp
                        ,
                        category.assoc
                        ,
                        f_ih_g ⟦ f_g ⟧
                        ,
                        ← category.assoc
                        ,
                        f_ih_f ⟦ f_f ⟧
                        ,
                        category.assoc
                        ,
                        ← functor.map_comp
                      ]
                  congr 2
              ·
                dsimp at *
                  rw [ associator_inv_naturality_assoc ]
                  slice_lhs 2 3 => rw [ ← tensor_comp , f_ih_f ⟦ f_f ⟧ ]
                  conv_lhs => rw [ ← @ category.id_comp F C _ _ _ ⟦ f_g ⟧ ]
                  simp only [ category.comp_id , tensor_comp , category.assoc ]
                  congr 2
                  rw [ ← mk_tensor , Quotient.lift_mk ]
                  dsimp
                  rw
                    [
                      functor.map_comp
                        ,
                        ← category.assoc
                        ,
                        ← f_ih_g ⟦ f_g ⟧
                        ,
                        ← @ category.comp_id F C _ _ _ ⟦ f_g ⟧
                        ,
                        ← category.id_comp discrete.functor inclusion_obj . map _
                        ,
                        tensor_comp
                      ]
                  dsimp
                  simp only [ category.assoc , category.comp_id ]
                  congr 1
                  convert normalize_iso_aux C f_Z . Hom . naturality normalize_map_aux f_f . app n
                  exact tensor_func_obj_map _ _ _ . symm
#align
  category_theory.free_monoidal_category.normalize_iso CategoryTheory.FreeMonoidalCategory.normalizeIso

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "The isomorphism between an object and its normal form is natural. -/")]
      []
      []
      []
      []
      [])
     (Command.def
      "def"
      (Command.declId `fullNormalizeIso [])
      (Command.optDeclSig
       []
       [(Term.typeSpec
         ":"
         (CategoryTheory.CategoryTheory.Isomorphism.«term_≅_»
          (Term.app
           (CategoryTheory.Functor.CategoryTheory.Functor.Basic.«term𝟭» "𝟭")
           [(Term.app
             (CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termF "F")
             [`C])])
          " ≅ "
          (CategoryTheory.Functor.CategoryTheory.Functor.Basic.«term_⋙_»
           (Term.app `fullNormalize [`C])
           " ⋙ "
           `inclusion)))])
      (Command.declValSimple
       ":="
       (Term.app
        `NatIso.ofComponents
        [(Term.fun
          "fun"
          (Term.basicFun
           [`X]
           []
           "=>"
           (CategoryTheory.Iso.CategoryTheory.Isomorphism.«term_≪≫_»
            (Term.proj
             (Term.app (CategoryTheory.CategoryTheory.Monoidal.Category.«termλ_» "λ_") [`X])
             "."
             `symm)
            " ≪≫ "
            (Term.app
             (Term.proj (Term.app (Term.proj (Term.app `normalizeIso [`C]) "." `app) [`X]) "." `app)
             [(Term.anonymousCtor "⟨" [`NormalMonoidalObject.unit] "⟩")]))))
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.intro "intro" [`X `Y `f])
             []
             (Tactic.dsimp "dsimp" [] [] [] [] [])
             []
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [] `left_unitor_inv_naturality_assoc)
                ","
                (Tactic.rwRule [] `category.assoc)
                ","
                (Tactic.rwRule [] `iso.cancel_iso_inv_left)]
               "]")
              [])
             []
             (Tactic.exact
              "exact"
              (Term.app
               `congr_arg
               [(Term.fun
                 "fun"
                 (Term.basicFun
                  [`f]
                  []
                  "=>"
                  (Term.app
                   `nat_trans.app
                   [`f (Term.app `discrete.mk [`normal_monoidal_object.unit])])))
                (Term.app
                 (Term.proj
                  (Term.proj
                   (Term.app (Term.explicitUniv `normalizeIso ".{" [`u] "}") [`C])
                   "."
                   `Hom)
                  "."
                  `naturality)
                 [`f])]))])))])
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `NatIso.ofComponents
       [(Term.fun
         "fun"
         (Term.basicFun
          [`X]
          []
          "=>"
          (CategoryTheory.Iso.CategoryTheory.Isomorphism.«term_≪≫_»
           (Term.proj
            (Term.app (CategoryTheory.CategoryTheory.Monoidal.Category.«termλ_» "λ_") [`X])
            "."
            `symm)
           " ≪≫ "
           (Term.app
            (Term.proj (Term.app (Term.proj (Term.app `normalizeIso [`C]) "." `app) [`X]) "." `app)
            [(Term.anonymousCtor "⟨" [`NormalMonoidalObject.unit] "⟩")]))))
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Tactic.intro "intro" [`X `Y `f])
            []
            (Tactic.dsimp "dsimp" [] [] [] [] [])
            []
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] `left_unitor_inv_naturality_assoc)
               ","
               (Tactic.rwRule [] `category.assoc)
               ","
               (Tactic.rwRule [] `iso.cancel_iso_inv_left)]
              "]")
             [])
            []
            (Tactic.exact
             "exact"
             (Term.app
              `congr_arg
              [(Term.fun
                "fun"
                (Term.basicFun
                 [`f]
                 []
                 "=>"
                 (Term.app
                  `nat_trans.app
                  [`f (Term.app `discrete.mk [`normal_monoidal_object.unit])])))
               (Term.app
                (Term.proj
                 (Term.proj
                  (Term.app (Term.explicitUniv `normalizeIso ".{" [`u] "}") [`C])
                  "."
                  `Hom)
                 "."
                 `naturality)
                [`f])]))])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.intro "intro" [`X `Y `f])
          []
          (Tactic.dsimp "dsimp" [] [] [] [] [])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `left_unitor_inv_naturality_assoc)
             ","
             (Tactic.rwRule [] `category.assoc)
             ","
             (Tactic.rwRule [] `iso.cancel_iso_inv_left)]
            "]")
           [])
          []
          (Tactic.exact
           "exact"
           (Term.app
            `congr_arg
            [(Term.fun
              "fun"
              (Term.basicFun
               [`f]
               []
               "=>"
               (Term.app
                `nat_trans.app
                [`f (Term.app `discrete.mk [`normal_monoidal_object.unit])])))
             (Term.app
              (Term.proj
               (Term.proj (Term.app (Term.explicitUniv `normalizeIso ".{" [`u] "}") [`C]) "." `Hom)
               "."
               `naturality)
              [`f])]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.app
        `congr_arg
        [(Term.fun
          "fun"
          (Term.basicFun
           [`f]
           []
           "=>"
           (Term.app `nat_trans.app [`f (Term.app `discrete.mk [`normal_monoidal_object.unit])])))
         (Term.app
          (Term.proj
           (Term.proj (Term.app (Term.explicitUniv `normalizeIso ".{" [`u] "}") [`C]) "." `Hom)
           "."
           `naturality)
          [`f])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `congr_arg
       [(Term.fun
         "fun"
         (Term.basicFun
          [`f]
          []
          "=>"
          (Term.app `nat_trans.app [`f (Term.app `discrete.mk [`normal_monoidal_object.unit])])))
        (Term.app
         (Term.proj
          (Term.proj (Term.app (Term.explicitUniv `normalizeIso ".{" [`u] "}") [`C]) "." `Hom)
          "."
          `naturality)
         [`f])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (Term.proj (Term.app (Term.explicitUniv `normalizeIso ".{" [`u] "}") [`C]) "." `Hom)
        "."
        `naturality)
       [`f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (Term.proj (Term.app (Term.explicitUniv `normalizeIso ".{" [`u] "}") [`C]) "." `Hom)
       "."
       `naturality)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj (Term.app (Term.explicitUniv `normalizeIso ".{" [`u] "}") [`C]) "." `Hom)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app (Term.explicitUniv `normalizeIso ".{" [`u] "}") [`C])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `C
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.explicitUniv `normalizeIso ".{" [`u] "}")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `u
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `normalizeIso
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.explicitUniv `normalizeIso ".{" [`u] "}") [`C])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      (Term.proj
       (Term.proj
        (Term.paren "(" (Term.app (Term.explicitUniv `normalizeIso ".{" [`u] "}") [`C]) ")")
        "."
        `Hom)
       "."
       `naturality)
      [`f])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.fun
       "fun"
       (Term.basicFun
        [`f]
        []
        "=>"
        (Term.app `nat_trans.app [`f (Term.app `discrete.mk [`normal_monoidal_object.unit])])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `nat_trans.app [`f (Term.app `discrete.mk [`normal_monoidal_object.unit])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `discrete.mk [`normal_monoidal_object.unit])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `normal_monoidal_object.unit
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `discrete.mk
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `discrete.mk [`normal_monoidal_object.unit])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `nat_trans.app
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.fun
      "fun"
      (Term.basicFun
       [`f]
       []
       "=>"
       (Term.app
        `nat_trans.app
        [`f (Term.paren "(" (Term.app `discrete.mk [`normal_monoidal_object.unit]) ")")])))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `congr_arg
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `left_unitor_inv_naturality_assoc)
         ","
         (Tactic.rwRule [] `category.assoc)
         ","
         (Tactic.rwRule [] `iso.cancel_iso_inv_left)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `iso.cancel_iso_inv_left
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `category.assoc
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `left_unitor_inv_naturality_assoc
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.dsimp "dsimp" [] [] [] [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.intro "intro" [`X `Y `f])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `Y
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `X
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0,
     tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(Tactic.intro "intro" [`X `Y `f])
         []
         (Tactic.dsimp "dsimp" [] [] [] [] [])
         []
         (Tactic.rwSeq
          "rw"
          []
          (Tactic.rwRuleSeq
           "["
           [(Tactic.rwRule [] `left_unitor_inv_naturality_assoc)
            ","
            (Tactic.rwRule [] `category.assoc)
            ","
            (Tactic.rwRule [] `iso.cancel_iso_inv_left)]
           "]")
          [])
         []
         (Tactic.exact
          "exact"
          (Term.app
           `congr_arg
           [(Term.paren
             "("
             (Term.fun
              "fun"
              (Term.basicFun
               [`f]
               []
               "=>"
               (Term.app
                `nat_trans.app
                [`f (Term.paren "(" (Term.app `discrete.mk [`normal_monoidal_object.unit]) ")")])))
             ")")
            (Term.paren
             "("
             (Term.app
              (Term.proj
               (Term.proj
                (Term.paren "(" (Term.app (Term.explicitUniv `normalizeIso ".{" [`u] "}") [`C]) ")")
                "."
                `Hom)
               "."
               `naturality)
              [`f])
             ")")]))])))
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.fun
       "fun"
       (Term.basicFun
        [`X]
        []
        "=>"
        (CategoryTheory.Iso.CategoryTheory.Isomorphism.«term_≪≫_»
         (Term.proj
          (Term.app (CategoryTheory.CategoryTheory.Monoidal.Category.«termλ_» "λ_") [`X])
          "."
          `symm)
         " ≪≫ "
         (Term.app
          (Term.proj (Term.app (Term.proj (Term.app `normalizeIso [`C]) "." `app) [`X]) "." `app)
          [(Term.anonymousCtor "⟨" [`NormalMonoidalObject.unit] "⟩")]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (CategoryTheory.Iso.CategoryTheory.Isomorphism.«term_≪≫_»
       (Term.proj
        (Term.app (CategoryTheory.CategoryTheory.Monoidal.Category.«termλ_» "λ_") [`X])
        "."
        `symm)
       " ≪≫ "
       (Term.app
        (Term.proj (Term.app (Term.proj (Term.app `normalizeIso [`C]) "." `app) [`X]) "." `app)
        [(Term.anonymousCtor "⟨" [`NormalMonoidalObject.unit] "⟩")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj (Term.app (Term.proj (Term.app `normalizeIso [`C]) "." `app) [`X]) "." `app)
       [(Term.anonymousCtor "⟨" [`NormalMonoidalObject.unit] "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [`NormalMonoidalObject.unit] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `NormalMonoidalObject.unit
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app (Term.proj (Term.app `normalizeIso [`C]) "." `app) [`X]) "." `app)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app (Term.proj (Term.app `normalizeIso [`C]) "." `app) [`X])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `X
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app `normalizeIso [`C]) "." `app)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `normalizeIso [`C])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `C
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `normalizeIso
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `normalizeIso [`C]) ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.proj (Term.paren "(" (Term.app `normalizeIso [`C]) ")") "." `app) [`X])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Term.proj
       (Term.app (CategoryTheory.CategoryTheory.Monoidal.Category.«termλ_» "λ_") [`X])
       "."
       `symm)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app (CategoryTheory.CategoryTheory.Monoidal.Category.«termλ_» "λ_") [`X])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `X
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (CategoryTheory.CategoryTheory.Monoidal.Category.«termλ_» "λ_")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (CategoryTheory.CategoryTheory.Monoidal.Category.«termλ_» "λ_") [`X])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `X
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.fun
      "fun"
      (Term.basicFun
       [`X]
       []
       "=>"
       (CategoryTheory.Iso.CategoryTheory.Isomorphism.«term_≪≫_»
        (Term.proj
         (Term.paren
          "("
          (Term.app (CategoryTheory.CategoryTheory.Monoidal.Category.«termλ_» "λ_") [`X])
          ")")
         "."
         `symm)
        " ≪≫ "
        (Term.app
         (Term.proj
          (Term.paren
           "("
           (Term.app (Term.proj (Term.paren "(" (Term.app `normalizeIso [`C]) ")") "." `app) [`X])
           ")")
          "."
          `app)
         [(Term.anonymousCtor "⟨" [`NormalMonoidalObject.unit] "⟩")]))))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `NatIso.ofComponents
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (CategoryTheory.CategoryTheory.Isomorphism.«term_≅_»
       (Term.app
        (CategoryTheory.Functor.CategoryTheory.Functor.Basic.«term𝟭» "𝟭")
        [(Term.app
          (CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termF "F")
          [`C])])
       " ≅ "
       (CategoryTheory.Functor.CategoryTheory.Functor.Basic.«term_⋙_»
        (Term.app `fullNormalize [`C])
        " ⋙ "
        `inclusion))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (CategoryTheory.Functor.CategoryTheory.Functor.Basic.«term_⋙_»
       (Term.app `fullNormalize [`C])
       " ⋙ "
       `inclusion)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `inclusion
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Term.app `fullNormalize [`C])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `C
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `fullNormalize
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1022, (some 1023, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      (Term.app
       (CategoryTheory.Functor.CategoryTheory.Functor.Basic.«term𝟭» "𝟭")
       [(Term.app
         (CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termF "F")
         [`C])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termF "F")
       [`C])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `C
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termF "F")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termF', expected 'CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termF._@.CategoryTheory.Monoidal.Free.Coherence._hyg.10'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/-- The isomorphism between an object and its normal form is natural. -/
  def
    fullNormalizeIso
    : 𝟭 F C ≅ fullNormalize C ⋙ inclusion
    :=
      NatIso.ofComponents
        fun X => λ_ X . symm ≪≫ normalizeIso C . app X . app ⟨ NormalMonoidalObject.unit ⟩
          by
            intro X Y f
              dsimp
              rw [ left_unitor_inv_naturality_assoc , category.assoc , iso.cancel_iso_inv_left ]
              exact
                congr_arg
                  fun f => nat_trans.app f discrete.mk normal_monoidal_object.unit
                    normalizeIso .{ u } C . Hom . naturality f
#align
  category_theory.free_monoidal_category.full_normalize_iso CategoryTheory.FreeMonoidalCategory.fullNormalizeIso

end

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment "/--" "The monoidal coherence theorem. -/")]
      []
      []
      []
      []
      [])
     (Command.instance
      (Term.attrKind [])
      "instance"
      []
      [(Command.declId `subsingleton_hom [])]
      (Command.declSig
       []
       (Term.typeSpec
        ":"
        (Term.app
         `Quiver.IsThin
         [(Term.app
           (CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termF "F")
           [`C])])))
      (Command.declValSimple
       ":="
       (Term.fun
        "fun"
        (Term.basicFun
         [(Term.hole "_") (Term.hole "_")]
         []
         "=>"
         (Term.anonymousCtor
          "⟨"
          [(Term.fun
            "fun"
            (Term.basicFun
             [`f `g]
             []
             "=>"
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.tacticHave_
                  "have"
                  (Term.haveDecl
                   (Term.haveIdDecl
                    []
                    [(Term.typeSpec
                      ":"
                      («term_=_»
                       (Term.app (Term.proj (Term.app `fullNormalize [`C]) "." `map) [`f])
                       "="
                       (Term.app (Term.proj (Term.app `fullNormalize [`C]) "." `map) [`g])))]
                    ":="
                    (Term.app `Subsingleton.elim [(Term.hole "_") (Term.hole "_")]))))
                 []
                 (Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule
                     [(patternIgnore (token.«← » "←"))]
                     (Term.app `functor.id_map [`f]))
                    ","
                    (Tactic.rwRule
                     [(patternIgnore (token.«← » "←"))]
                     (Term.app `functor.id_map [`g]))]
                   "]")
                  [])
                 []
                 (Tactic.simp
                  "simp"
                  []
                  []
                  []
                  ["["
                   [(Tactic.simpLemma
                     []
                     [(patternIgnore (token.«← » "←"))]
                     (Term.app
                      `nat_iso.naturality_2
                      [(Term.app (Term.explicitUniv `fullNormalizeIso ".{" [`u] "}") [`C])]))
                    ","
                    (Tactic.simpLemma [] [] `this)]
                   "]"]
                  [])])))))]
          "⟩")))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [(Term.hole "_") (Term.hole "_")]
        []
        "=>"
        (Term.anonymousCtor
         "⟨"
         [(Term.fun
           "fun"
           (Term.basicFun
            [`f `g]
            []
            "=>"
            (Term.byTactic
             "by"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(Tactic.tacticHave_
                 "have"
                 (Term.haveDecl
                  (Term.haveIdDecl
                   []
                   [(Term.typeSpec
                     ":"
                     («term_=_»
                      (Term.app (Term.proj (Term.app `fullNormalize [`C]) "." `map) [`f])
                      "="
                      (Term.app (Term.proj (Term.app `fullNormalize [`C]) "." `map) [`g])))]
                   ":="
                   (Term.app `Subsingleton.elim [(Term.hole "_") (Term.hole "_")]))))
                []
                (Tactic.rwSeq
                 "rw"
                 []
                 (Tactic.rwRuleSeq
                  "["
                  [(Tactic.rwRule
                    [(patternIgnore (token.«← » "←"))]
                    (Term.app `functor.id_map [`f]))
                   ","
                   (Tactic.rwRule
                    [(patternIgnore (token.«← » "←"))]
                    (Term.app `functor.id_map [`g]))]
                  "]")
                 [])
                []
                (Tactic.simp
                 "simp"
                 []
                 []
                 []
                 ["["
                  [(Tactic.simpLemma
                    []
                    [(patternIgnore (token.«← » "←"))]
                    (Term.app
                     `nat_iso.naturality_2
                     [(Term.app (Term.explicitUniv `fullNormalizeIso ".{" [`u] "}") [`C])]))
                   ","
                   (Tactic.simpLemma [] [] `this)]
                  "]"]
                 [])])))))]
         "⟩")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.fun
         "fun"
         (Term.basicFun
          [`f `g]
          []
          "=>"
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(Tactic.tacticHave_
               "have"
               (Term.haveDecl
                (Term.haveIdDecl
                 []
                 [(Term.typeSpec
                   ":"
                   («term_=_»
                    (Term.app (Term.proj (Term.app `fullNormalize [`C]) "." `map) [`f])
                    "="
                    (Term.app (Term.proj (Term.app `fullNormalize [`C]) "." `map) [`g])))]
                 ":="
                 (Term.app `Subsingleton.elim [(Term.hole "_") (Term.hole "_")]))))
              []
              (Tactic.rwSeq
               "rw"
               []
               (Tactic.rwRuleSeq
                "["
                [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] (Term.app `functor.id_map [`f]))
                 ","
                 (Tactic.rwRule [(patternIgnore (token.«← » "←"))] (Term.app `functor.id_map [`g]))]
                "]")
               [])
              []
              (Tactic.simp
               "simp"
               []
               []
               []
               ["["
                [(Tactic.simpLemma
                  []
                  [(patternIgnore (token.«← » "←"))]
                  (Term.app
                   `nat_iso.naturality_2
                   [(Term.app (Term.explicitUniv `fullNormalizeIso ".{" [`u] "}") [`C])]))
                 ","
                 (Tactic.simpLemma [] [] `this)]
                "]"]
               [])])))))]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`f `g]
        []
        "=>"
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               []
               [(Term.typeSpec
                 ":"
                 («term_=_»
                  (Term.app (Term.proj (Term.app `fullNormalize [`C]) "." `map) [`f])
                  "="
                  (Term.app (Term.proj (Term.app `fullNormalize [`C]) "." `map) [`g])))]
               ":="
               (Term.app `Subsingleton.elim [(Term.hole "_") (Term.hole "_")]))))
            []
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] (Term.app `functor.id_map [`f]))
               ","
               (Tactic.rwRule [(patternIgnore (token.«← » "←"))] (Term.app `functor.id_map [`g]))]
              "]")
             [])
            []
            (Tactic.simp
             "simp"
             []
             []
             []
             ["["
              [(Tactic.simpLemma
                []
                [(patternIgnore (token.«← » "←"))]
                (Term.app
                 `nat_iso.naturality_2
                 [(Term.app (Term.explicitUniv `fullNormalizeIso ".{" [`u] "}") [`C])]))
               ","
               (Tactic.simpLemma [] [] `this)]
              "]"]
             [])])))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             []
             [(Term.typeSpec
               ":"
               («term_=_»
                (Term.app (Term.proj (Term.app `fullNormalize [`C]) "." `map) [`f])
                "="
                (Term.app (Term.proj (Term.app `fullNormalize [`C]) "." `map) [`g])))]
             ":="
             (Term.app `Subsingleton.elim [(Term.hole "_") (Term.hole "_")]))))
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] (Term.app `functor.id_map [`f]))
             ","
             (Tactic.rwRule [(patternIgnore (token.«← » "←"))] (Term.app `functor.id_map [`g]))]
            "]")
           [])
          []
          (Tactic.simp
           "simp"
           []
           []
           []
           ["["
            [(Tactic.simpLemma
              []
              [(patternIgnore (token.«← » "←"))]
              (Term.app
               `nat_iso.naturality_2
               [(Term.app (Term.explicitUniv `fullNormalizeIso ".{" [`u] "}") [`C])]))
             ","
             (Tactic.simpLemma [] [] `this)]
            "]"]
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       []
       ["["
        [(Tactic.simpLemma
          []
          [(patternIgnore (token.«← » "←"))]
          (Term.app
           `nat_iso.naturality_2
           [(Term.app (Term.explicitUniv `fullNormalizeIso ".{" [`u] "}") [`C])]))
         ","
         (Tactic.simpLemma [] [] `this)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `this
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `nat_iso.naturality_2
       [(Term.app (Term.explicitUniv `fullNormalizeIso ".{" [`u] "}") [`C])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.explicitUniv `fullNormalizeIso ".{" [`u] "}") [`C])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `C
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.explicitUniv `fullNormalizeIso ".{" [`u] "}")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `u
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `fullNormalizeIso
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.explicitUniv `fullNormalizeIso ".{" [`u] "}") [`C])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `nat_iso.naturality_2
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] (Term.app `functor.id_map [`f]))
         ","
         (Tactic.rwRule [(patternIgnore (token.«← » "←"))] (Term.app `functor.id_map [`g]))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `functor.id_map [`g])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `functor.id_map
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `functor.id_map [`f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `functor.id_map
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         []
         [(Term.typeSpec
           ":"
           («term_=_»
            (Term.app (Term.proj (Term.app `fullNormalize [`C]) "." `map) [`f])
            "="
            (Term.app (Term.proj (Term.app `fullNormalize [`C]) "." `map) [`g])))]
         ":="
         (Term.app `Subsingleton.elim [(Term.hole "_") (Term.hole "_")]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Subsingleton.elim [(Term.hole "_") (Term.hole "_")])
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
      `Subsingleton.elim
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Term.app (Term.proj (Term.app `fullNormalize [`C]) "." `map) [`f])
       "="
       (Term.app (Term.proj (Term.app `fullNormalize [`C]) "." `map) [`g]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj (Term.app `fullNormalize [`C]) "." `map) [`g])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app `fullNormalize [`C]) "." `map)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `fullNormalize [`C])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `C
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `fullNormalize
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `fullNormalize [`C]) ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app (Term.proj (Term.app `fullNormalize [`C]) "." `map) [`f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app `fullNormalize [`C]) "." `map)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `fullNormalize [`C])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `C
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `fullNormalize
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `fullNormalize [`C]) ")")
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
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app
       `Quiver.IsThin
       [(Term.app
         (CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termF "F")
         [`C])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termF "F")
       [`C])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `C
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termF "F")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termF', expected 'CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termF._@.CategoryTheory.Monoidal.Free.Coherence._hyg.10'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/-- The monoidal coherence theorem. -/
  instance
    subsingleton_hom
    : Quiver.IsThin F C
    :=
      fun
        _ _
          =>
          ⟨
            fun
              f g
                =>
                by
                  have : fullNormalize C . map f = fullNormalize C . map g := Subsingleton.elim _ _
                    rw [ ← functor.id_map f , ← functor.id_map g ]
                    simp [ ← nat_iso.naturality_2 fullNormalizeIso .{ u } C , this ]
            ⟩
#align
  category_theory.free_monoidal_category.subsingleton_hom CategoryTheory.FreeMonoidalCategory.subsingleton_hom

section Groupoid

section

open Hom

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "Auxiliary construction for showing that the free monoidal category is a groupoid. Do not use\n    this, use `is_iso.inv` instead. -/")]
      []
      []
      []
      []
      [])
     (Command.def
      "def"
      (Command.declId `inverseAux [])
      (Command.optDeclSig
       []
       [(Term.typeSpec
         ":"
         (Term.forall
          "∀"
          [(Term.implicitBinder
            "{"
            [`X `Y]
            [":"
             (Term.app
              (CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termF "F")
              [`C])]
            "}")]
          []
          ","
          (Term.arrow
           (CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.«term_⟶ᵐ_»
            `X
            " ⟶ᵐ "
            `Y)
           "→"
           (CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.«term_⟶ᵐ_»
            `Y
            " ⟶ᵐ "
            `X))))])
      (Command.declValEqns
       (Term.matchAltsWhereDecls
        (Term.matchAlts
         [(Term.matchAlt
           "|"
           [[(Term.hole "_") "," (Term.hole "_") "," (Term.app `id [`X])]]
           "=>"
           (Term.app `id [`X]))
          (Term.matchAlt
           "|"
           [[(Term.hole "_")
             ","
             (Term.hole "_")
             ","
             (Term.app `α_hom [(Term.hole "_") (Term.hole "_") (Term.hole "_")])]]
           "=>"
           (Term.app `α_inv [(Term.hole "_") (Term.hole "_") (Term.hole "_")]))
          (Term.matchAlt
           "|"
           [[(Term.hole "_")
             ","
             (Term.hole "_")
             ","
             (Term.app `α_inv [(Term.hole "_") (Term.hole "_") (Term.hole "_")])]]
           "=>"
           (Term.app `α_hom [(Term.hole "_") (Term.hole "_") (Term.hole "_")]))
          (Term.matchAlt
           "|"
           [[(Term.hole "_") "," (Term.hole "_") "," (Term.app `ρ_hom [(Term.hole "_")])]]
           "=>"
           (Term.app `ρ_inv [(Term.hole "_")]))
          (Term.matchAlt
           "|"
           [[(Term.hole "_") "," (Term.hole "_") "," (Term.app `ρ_inv [(Term.hole "_")])]]
           "=>"
           (Term.app `ρ_hom [(Term.hole "_")]))
          (Term.matchAlt
           "|"
           [[(Term.hole "_") "," (Term.hole "_") "," (Term.app `l_hom [(Term.hole "_")])]]
           "=>"
           (Term.app `l_inv [(Term.hole "_")]))
          (Term.matchAlt
           "|"
           [[(Term.hole "_") "," (Term.hole "_") "," (Term.app `l_inv [(Term.hole "_")])]]
           "=>"
           (Term.app `l_hom [(Term.hole "_")]))
          (Term.matchAlt
           "|"
           [[(Term.hole "_") "," (Term.hole "_") "," (Term.app `comp [`f `g])]]
           "=>"
           (Term.app
            (Term.proj (Term.app `inverse_aux [`g]) "." `comp)
            [(Term.app `inverse_aux [`f])]))
          (Term.matchAlt
           "|"
           [[(Term.hole "_") "," (Term.hole "_") "," (Term.app `hom.tensor [`f `g])]]
           "=>"
           (Term.app
            (Term.proj (Term.app `inverse_aux [`f]) "." `tensor)
            [(Term.app `inverse_aux [`g])]))])
        []))
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValEqns', expected 'Lean.Parser.Command.declValSimple'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj (Term.app `inverse_aux [`f]) "." `tensor) [(Term.app `inverse_aux [`g])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `inverse_aux [`g])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `inverse_aux
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `inverse_aux [`g]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app `inverse_aux [`f]) "." `tensor)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `inverse_aux [`f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `inverse_aux
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `inverse_aux [`f]) ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `hom.tensor [`f `g])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `hom.tensor
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app (Term.proj (Term.app `inverse_aux [`g]) "." `comp) [(Term.app `inverse_aux [`f])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `inverse_aux [`f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `inverse_aux
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `inverse_aux [`f]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app `inverse_aux [`g]) "." `comp)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `inverse_aux [`g])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `inverse_aux
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `inverse_aux [`g]) ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `comp [`f `g])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `comp
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app `l_hom [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `l_hom
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `l_inv [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `l_inv
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app `l_inv [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `l_inv
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `l_hom [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `l_hom
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app `ρ_hom [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `ρ_hom
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `ρ_inv [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `ρ_inv
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app `ρ_inv [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `ρ_inv
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `ρ_hom [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `ρ_hom
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app `α_hom [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
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
      `α_hom
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `α_inv [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
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
      `α_inv
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app `α_inv [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
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
      `α_inv
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `α_hom [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
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
      `α_hom
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app `id [`X])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `X
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `id
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `id [`X])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `X
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `id
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.forall
       "∀"
       [(Term.implicitBinder
         "{"
         [`X `Y]
         [":"
          (Term.app
           (CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termF "F")
           [`C])]
         "}")]
       []
       ","
       (Term.arrow
        (CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.«term_⟶ᵐ_»
         `X
         " ⟶ᵐ "
         `Y)
        "→"
        (CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.«term_⟶ᵐ_»
         `Y
         " ⟶ᵐ "
         `X)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.arrow
       (CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.«term_⟶ᵐ_»
        `X
        " ⟶ᵐ "
        `Y)
       "→"
       (CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.«term_⟶ᵐ_»
        `Y
        " ⟶ᵐ "
        `X))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.«term_⟶ᵐ_»
       `Y
       " ⟶ᵐ "
       `X)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.«term_⟶ᵐ_»', expected 'CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.term_⟶ᵐ_._@.CategoryTheory.Monoidal.Free.Coherence._hyg.404'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    Auxiliary construction for showing that the free monoidal category is a groupoid. Do not use
        this, use `is_iso.inv` instead. -/
  def
    inverseAux
    : ∀ { X Y : F C } , X ⟶ᵐ Y → Y ⟶ᵐ X
    | _ , _ , id X => id X
      | _ , _ , α_hom _ _ _ => α_inv _ _ _
      | _ , _ , α_inv _ _ _ => α_hom _ _ _
      | _ , _ , ρ_hom _ => ρ_inv _
      | _ , _ , ρ_inv _ => ρ_hom _
      | _ , _ , l_hom _ => l_inv _
      | _ , _ , l_inv _ => l_hom _
      | _ , _ , comp f g => inverse_aux g . comp inverse_aux f
      | _ , _ , hom.tensor f g => inverse_aux f . tensor inverse_aux g
#align
  category_theory.free_monoidal_category.inverse_aux CategoryTheory.FreeMonoidalCategory.inverseAux

end

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.instance
      (Term.attrKind [])
      "instance"
      []
      []
      (Command.declSig
       []
       (Term.typeSpec
        ":"
        (Term.app
         (Term.explicitUniv `Groupoid ".{" [`u] "}")
         [(Term.app
           (CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termF "F")
           [`C])])))
      (Command.declValSimple
       ":="
       (Term.structInst
        "{"
        [[(Term.typeAscription
           "("
           `inferInstance
           ":"
           [(Term.app
             `Category
             [(Term.app
               (CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termF
                "F")
               [`C])])]
           ")")]
         "with"]
        [(Term.structInstField
          (Term.structInstLVal `inv [])
          ":="
          (Term.fun
           "fun"
           (Term.basicFun
            [`X `Y]
            []
            "=>"
            (Term.app
             `Quotient.lift
             [(Term.fun
               "fun"
               (Term.basicFun
                [`f]
                []
                "=>"
                (Quotient.Init.Data.Quot.«term⟦_⟧» "⟦" (Term.app `inverseAux [`f]) "⟧")))
              (Term.byTactic
               "by"
               (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tidy "tidy" [])])))]))))]
        (Term.optEllipsis [])
        []
        "}")
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.structInst
       "{"
       [[(Term.typeAscription
          "("
          `inferInstance
          ":"
          [(Term.app
            `Category
            [(Term.app
              (CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termF "F")
              [`C])])]
          ")")]
        "with"]
       [(Term.structInstField
         (Term.structInstLVal `inv [])
         ":="
         (Term.fun
          "fun"
          (Term.basicFun
           [`X `Y]
           []
           "=>"
           (Term.app
            `Quotient.lift
            [(Term.fun
              "fun"
              (Term.basicFun
               [`f]
               []
               "=>"
               (Quotient.Init.Data.Quot.«term⟦_⟧» "⟦" (Term.app `inverseAux [`f]) "⟧")))
             (Term.byTactic
              "by"
              (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tidy "tidy" [])])))]))))]
       (Term.optEllipsis [])
       []
       "}")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`X `Y]
        []
        "=>"
        (Term.app
         `Quotient.lift
         [(Term.fun
           "fun"
           (Term.basicFun
            [`f]
            []
            "=>"
            (Quotient.Init.Data.Quot.«term⟦_⟧» "⟦" (Term.app `inverseAux [`f]) "⟧")))
          (Term.byTactic
           "by"
           (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tidy "tidy" [])])))])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Quotient.lift
       [(Term.fun
         "fun"
         (Term.basicFun
          [`f]
          []
          "=>"
          (Quotient.Init.Data.Quot.«term⟦_⟧» "⟦" (Term.app `inverseAux [`f]) "⟧")))
        (Term.byTactic
         "by"
         (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tidy "tidy" [])])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tidy "tidy" [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tidy "tidy" [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0,
     tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tidy "tidy" [])])))
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.fun
       "fun"
       (Term.basicFun
        [`f]
        []
        "=>"
        (Quotient.Init.Data.Quot.«term⟦_⟧» "⟦" (Term.app `inverseAux [`f]) "⟧")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Quotient.Init.Data.Quot.«term⟦_⟧» "⟦" (Term.app `inverseAux [`f]) "⟧")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `inverseAux [`f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `inverseAux
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1023, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.fun
      "fun"
      (Term.basicFun
       [`f]
       []
       "=>"
       (Quotient.Init.Data.Quot.«term⟦_⟧» "⟦" (Term.app `inverseAux [`f]) "⟧")))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Quotient.lift
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Y
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `X
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription
       "("
       `inferInstance
       ":"
       [(Term.app
         `Category
         [(Term.app
           (CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termF "F")
           [`C])])]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Category
       [(Term.app
         (CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termF "F")
         [`C])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termF "F")
       [`C])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `C
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termF "F")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termF', expected 'CategoryTheory.FreeMonoidalCategory.CategoryTheory.Monoidal.Free.Coherence.termF._@.CategoryTheory.Monoidal.Free.Coherence._hyg.10'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
instance
  : Groupoid .{ u } F C
  :=
    {
      ( inferInstance : Category F C ) with
      inv := fun X Y => Quotient.lift fun f => ⟦ inverseAux f ⟧ by tidy
      }

end Groupoid

end FreeMonoidalCategory

end CategoryTheory

