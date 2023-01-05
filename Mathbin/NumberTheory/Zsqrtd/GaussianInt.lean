/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes

! This file was ported from Lean 3 source module number_theory.zsqrtd.gaussian_int
! leanprover-community/mathlib commit 5a3e819569b0f12cbec59d740a2613018e7b8eec
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.NumberTheory.Zsqrtd.Basic
import Mathbin.Data.Complex.Basic
import Mathbin.RingTheory.PrincipalIdealDomain
import Mathbin.NumberTheory.LegendreSymbol.QuadraticReciprocity

/-!
# Gaussian integers

The Gaussian integers are complex integer, complex numbers whose real and imaginary parts are both
integers.

## Main definitions

The Euclidean domain structure on `ℤ[i]` is defined in this file.

The homomorphism `to_complex` into the complex numbers is also defined in this file.

## Main statements

`prime_iff_mod_four_eq_three_of_nat_prime`
A prime natural number is prime in `ℤ[i]` if and only if it is `3` mod `4`

## Notations

This file uses the local notation `ℤ[i]` for `gaussian_int`

## Implementation notes

Gaussian integers are implemented using the more general definition `zsqrtd`, the type of integers
adjoined a square root of `d`, in this case `-1`. The definition is reducible, so that properties
and definitions about `zsqrtd` can easily be used.
-/


open Zsqrtd Complex

/-- The Gaussian integers, defined as `ℤ√(-1)`. -/
@[reducible]
def GaussianInt : Type :=
  Zsqrtd (-1)
#align gaussian_int GaussianInt

-- mathport name: «exprℤ[i]»
local notation "ℤ[i]" => GaussianInt

namespace GaussianInt

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
       (Term.typeSpec ":" (Term.app `Repr [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")])))
      (Command.declValSimple
       ":="
       (Term.anonymousCtor
        "⟨"
        [(Term.fun
          "fun"
          (Term.basicFun
           [`x]
           []
           "=>"
           («term_++_»
            («term_++_»
             («term_++_»
              («term_++_» (str "\"⟨\"") "++" (Term.app `repr [(Term.proj `x "." `re)]))
              "++"
              (str "\", \""))
             "++"
             (Term.app `repr [(Term.proj `x "." `im)]))
            "++"
            (str "\"⟩\""))))]
        "⟩")
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.fun
         "fun"
         (Term.basicFun
          [`x]
          []
          "=>"
          («term_++_»
           («term_++_»
            («term_++_»
             («term_++_» (str "\"⟨\"") "++" (Term.app `repr [(Term.proj `x "." `re)]))
             "++"
             (str "\", \""))
            "++"
            (Term.app `repr [(Term.proj `x "." `im)]))
           "++"
           (str "\"⟩\""))))]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`x]
        []
        "=>"
        («term_++_»
         («term_++_»
          («term_++_»
           («term_++_» (str "\"⟨\"") "++" (Term.app `repr [(Term.proj `x "." `re)]))
           "++"
           (str "\", \""))
          "++"
          (Term.app `repr [(Term.proj `x "." `im)]))
         "++"
         (str "\"⟩\""))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_++_»
       («term_++_»
        («term_++_»
         («term_++_» (str "\"⟨\"") "++" (Term.app `repr [(Term.proj `x "." `re)]))
         "++"
         (str "\", \""))
        "++"
        (Term.app `repr [(Term.proj `x "." `im)]))
       "++"
       (str "\"⟩\""))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (str "\"⟩\"")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      («term_++_»
       («term_++_»
        («term_++_» (str "\"⟨\"") "++" (Term.app `repr [(Term.proj `x "." `re)]))
        "++"
        (str "\", \""))
       "++"
       (Term.app `repr [(Term.proj `x "." `im)]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `repr [(Term.proj `x "." `im)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `x "." `im)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `repr
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      («term_++_»
       («term_++_» (str "\"⟨\"") "++" (Term.app `repr [(Term.proj `x "." `re)]))
       "++"
       (str "\", \""))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (str "\", \"")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      («term_++_» (str "\"⟨\"") "++" (Term.app `repr [(Term.proj `x "." `re)]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `repr [(Term.proj `x "." `re)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `x "." `re)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `repr
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      (str "\"⟨\"")
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 65 >? 65, (some 66, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 65 >? 65, (some 66, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 65 >? 65, (some 66, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app `Repr [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]»', expected 'NumberTheory.Zsqrtd.GaussianInt.termℤ[i]._@.NumberTheory.Zsqrtd.GaussianInt._hyg.6'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
instance : Repr ℤ[i] := ⟨ fun x => "⟨" ++ repr x . re ++ ", " ++ repr x . im ++ "⟩" ⟩

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
        (Term.app `CommRing [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")])))
      (Command.declValSimple ":=" `Zsqrtd.commRing [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Zsqrtd.commRing
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app `CommRing [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]»', expected 'NumberTheory.Zsqrtd.GaussianInt.termℤ[i]._@.NumberTheory.Zsqrtd.GaussianInt._hyg.6'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
instance : CommRing ℤ[i] := Zsqrtd.commRing

section

attribute [-instance] Complex.field

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "The embedding of the Gaussian integers into the complex numbers, as a ring homomorphism. -/")]
      []
      []
      []
      []
      [])
     (Command.def
      "def"
      (Command.declId `toComplex [])
      (Command.optDeclSig
       []
       [(Term.typeSpec
         ":"
         (Algebra.Hom.Ring.«term_→+*_»
          (NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")
          " →+* "
          (Data.Complex.Basic.termℂ "ℂ")))])
      (Command.declValSimple
       ":="
       (Term.app
        `Zsqrtd.lift
        [(Term.anonymousCtor
          "⟨"
          [`i
           ","
           (Term.byTactic
            "by"
            (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])])))]
          "⟩")])
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Zsqrtd.lift
       [(Term.anonymousCtor
         "⟨"
         [`i
          ","
          (Term.byTactic
           "by"
           (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])])))]
         "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [`i
        ","
        (Term.byTactic
         "by"
         (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])])))]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] [] [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Zsqrtd.lift
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Algebra.Hom.Ring.«term_→+*_»
       (NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")
       " →+* "
       (Data.Complex.Basic.termℂ "ℂ"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Complex.Basic.termℂ "ℂ")
[PrettyPrinter.parenthesize] ...precedences are 25 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
      (NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]»', expected 'NumberTheory.Zsqrtd.GaussianInt.termℤ[i]._@.NumberTheory.Zsqrtd.GaussianInt._hyg.6'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/-- The embedding of the Gaussian integers into the complex numbers, as a ring homomorphism. -/
  def toComplex : ℤ[i] →+* ℂ := Zsqrtd.lift ⟨ i , by simp ⟩
#align gaussian_int.to_complex GaussianInt.toComplex

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
         `Coe
         [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]") (Data.Complex.Basic.termℂ "ℂ")])))
      (Command.declValSimple ":=" (Term.anonymousCtor "⟨" [`toComplex] "⟩") [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [`toComplex] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `toComplex
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app
       `Coe
       [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]") (Data.Complex.Basic.termℂ "ℂ")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Complex.Basic.termℂ', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Complex.Basic.termℂ', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Complex.Basic.termℂ "ℂ")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]»', expected 'NumberTheory.Zsqrtd.GaussianInt.termℤ[i]._@.NumberTheory.Zsqrtd.GaussianInt._hyg.6'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
instance : Coe ℤ[i] ℂ := ⟨ toComplex ⟩

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `to_complex_def [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`x]
         [":" (NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.typeAscription "(" `x ":" [(Data.Complex.Basic.termℂ "ℂ")] ")")
         "="
         («term_+_» (Term.proj `x "." `re) "+" («term_*_» (Term.proj `x "." `im) "*" `I)))))
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
       (Term.typeAscription "(" `x ":" [(Data.Complex.Basic.termℂ "ℂ")] ")")
       "="
       («term_+_» (Term.proj `x "." `re) "+" («term_*_» (Term.proj `x "." `im) "*" `I)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_» (Term.proj `x "." `re) "+" («term_*_» (Term.proj `x "." `im) "*" `I))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_» (Term.proj `x "." `im) "*" `I)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `I
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (Term.proj `x "." `im)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      (Term.proj `x "." `re)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.typeAscription "(" `x ":" [(Data.Complex.Basic.termℂ "ℂ")] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Complex.Basic.termℂ "ℂ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]»', expected 'NumberTheory.Zsqrtd.GaussianInt.termℤ[i]._@.NumberTheory.Zsqrtd.GaussianInt._hyg.6'
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
theorem to_complex_def ( x : ℤ[i] ) : ( x : ℂ ) = x . re + x . im * I := rfl
#align gaussian_int.to_complex_def GaussianInt.to_complex_def

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `to_complex_def' [])
      (Command.declSig
       [(Term.explicitBinder "(" [`x `y] [":" (termℤ "ℤ")] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.typeAscription
          "("
          (Term.typeAscription
           "("
           (Term.anonymousCtor "⟨" [`x "," `y] "⟩")
           ":"
           [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
           ")")
          ":"
          [(Data.Complex.Basic.termℂ "ℂ")]
          ")")
         "="
         («term_+_» `x "+" («term_*_» `y "*" `I)))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `to_complex_def)] "]"] [])])))
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
         [(Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `to_complex_def)] "]"] [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `to_complex_def)] "]"] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `to_complex_def
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.typeAscription
        "("
        (Term.typeAscription
         "("
         (Term.anonymousCtor "⟨" [`x "," `y] "⟩")
         ":"
         [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
         ")")
        ":"
        [(Data.Complex.Basic.termℂ "ℂ")]
        ")")
       "="
       («term_+_» `x "+" («term_*_» `y "*" `I)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_» `x "+" («term_*_» `y "*" `I))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_» `y "*" `I)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `I
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `y
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.typeAscription
       "("
       (Term.typeAscription
        "("
        (Term.anonymousCtor "⟨" [`x "," `y] "⟩")
        ":"
        [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
        ")")
       ":"
       [(Data.Complex.Basic.termℂ "ℂ")]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Complex.Basic.termℂ "ℂ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription
       "("
       (Term.anonymousCtor "⟨" [`x "," `y] "⟩")
       ":"
       [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]»', expected 'NumberTheory.Zsqrtd.GaussianInt.termℤ[i]._@.NumberTheory.Zsqrtd.GaussianInt._hyg.6'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  to_complex_def'
  ( x y : ℤ ) : ( ( ⟨ x , y ⟩ : ℤ[i] ) : ℂ ) = x + y * I
  := by simp [ to_complex_def ]
#align gaussian_int.to_complex_def' GaussianInt.to_complex_def'

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `to_complex_def₂ [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`x]
         [":" (NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.typeAscription "(" `x ":" [(Data.Complex.Basic.termℂ "ℂ")] ")")
         "="
         (Term.anonymousCtor "⟨" [(Term.proj `x "." `re) "," (Term.proj `x "." `im)] "⟩"))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.«tactic_<;>_»
            (Tactic.apply "apply" `Complex.ext)
            "<;>"
            (Tactic.simp
             "simp"
             []
             []
             []
             ["[" [(Tactic.simpLemma [] [] `to_complex_def)] "]"]
             []))])))
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
         [(Tactic.«tactic_<;>_»
           (Tactic.apply "apply" `Complex.ext)
           "<;>"
           (Tactic.simp
            "simp"
            []
            []
            []
            ["[" [(Tactic.simpLemma [] [] `to_complex_def)] "]"]
            []))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.«tactic_<;>_»
       (Tactic.apply "apply" `Complex.ext)
       "<;>"
       (Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `to_complex_def)] "]"] []))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `to_complex_def)] "]"] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `to_complex_def
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 2 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
      (Tactic.apply "apply" `Complex.ext)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Complex.ext
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.typeAscription "(" `x ":" [(Data.Complex.Basic.termℂ "ℂ")] ")")
       "="
       (Term.anonymousCtor "⟨" [(Term.proj `x "." `re) "," (Term.proj `x "." `im)] "⟩"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [(Term.proj `x "." `re) "," (Term.proj `x "." `im)] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `x "." `im)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `x "." `re)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.typeAscription "(" `x ":" [(Data.Complex.Basic.termℂ "ℂ")] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Complex.Basic.termℂ "ℂ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]»', expected 'NumberTheory.Zsqrtd.GaussianInt.termℤ[i]._@.NumberTheory.Zsqrtd.GaussianInt._hyg.6'
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
theorem
  to_complex_def₂
  ( x : ℤ[i] ) : ( x : ℂ ) = ⟨ x . re , x . im ⟩
  := by apply Complex.ext <;> simp [ to_complex_def ]
#align gaussian_int.to_complex_def₂ GaussianInt.to_complex_def₂

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
      (Command.declId `to_real_re [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`x]
         [":" (NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.typeAscription
          "("
          (Term.typeAscription "(" (Term.proj `x "." `re) ":" [(termℤ "ℤ")] ")")
          ":"
          [(Data.Real.Basic.termℝ "ℝ")]
          ")")
         "="
         (Term.proj
          (Term.typeAscription "(" `x ":" [(Data.Complex.Basic.termℂ "ℂ")] ")")
          "."
          `re))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `to_complex_def)] "]"] [])])))
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
         [(Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `to_complex_def)] "]"] [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `to_complex_def)] "]"] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `to_complex_def
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.typeAscription
        "("
        (Term.typeAscription "(" (Term.proj `x "." `re) ":" [(termℤ "ℤ")] ")")
        ":"
        [(Data.Real.Basic.termℝ "ℝ")]
        ")")
       "="
       (Term.proj (Term.typeAscription "(" `x ":" [(Data.Complex.Basic.termℂ "ℂ")] ")") "." `re))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.typeAscription "(" `x ":" [(Data.Complex.Basic.termℂ "ℂ")] ")") "." `re)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.typeAscription "(" `x ":" [(Data.Complex.Basic.termℂ "ℂ")] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Complex.Basic.termℂ "ℂ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.typeAscription
       "("
       (Term.typeAscription "(" (Term.proj `x "." `re) ":" [(termℤ "ℤ")] ")")
       ":"
       [(Data.Real.Basic.termℝ "ℝ")]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Real.Basic.termℝ "ℝ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription "(" (Term.proj `x "." `re) ":" [(termℤ "ℤ")] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (termℤ "ℤ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `x "." `re)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]»', expected 'NumberTheory.Zsqrtd.GaussianInt.termℤ[i]._@.NumberTheory.Zsqrtd.GaussianInt._hyg.6'
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
    to_real_re
    ( x : ℤ[i] ) : ( ( x . re : ℤ ) : ℝ ) = ( x : ℂ ) . re
    := by simp [ to_complex_def ]
#align gaussian_int.to_real_re GaussianInt.to_real_re

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
      (Command.declId `to_real_im [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`x]
         [":" (NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.typeAscription
          "("
          (Term.typeAscription "(" (Term.proj `x "." `im) ":" [(termℤ "ℤ")] ")")
          ":"
          [(Data.Real.Basic.termℝ "ℝ")]
          ")")
         "="
         (Term.proj
          (Term.typeAscription "(" `x ":" [(Data.Complex.Basic.termℂ "ℂ")] ")")
          "."
          `im))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `to_complex_def)] "]"] [])])))
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
         [(Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `to_complex_def)] "]"] [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `to_complex_def)] "]"] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `to_complex_def
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.typeAscription
        "("
        (Term.typeAscription "(" (Term.proj `x "." `im) ":" [(termℤ "ℤ")] ")")
        ":"
        [(Data.Real.Basic.termℝ "ℝ")]
        ")")
       "="
       (Term.proj (Term.typeAscription "(" `x ":" [(Data.Complex.Basic.termℂ "ℂ")] ")") "." `im))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.typeAscription "(" `x ":" [(Data.Complex.Basic.termℂ "ℂ")] ")") "." `im)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.typeAscription "(" `x ":" [(Data.Complex.Basic.termℂ "ℂ")] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Complex.Basic.termℂ "ℂ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.typeAscription
       "("
       (Term.typeAscription "(" (Term.proj `x "." `im) ":" [(termℤ "ℤ")] ")")
       ":"
       [(Data.Real.Basic.termℝ "ℝ")]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Real.Basic.termℝ "ℝ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription "(" (Term.proj `x "." `im) ":" [(termℤ "ℤ")] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (termℤ "ℤ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `x "." `im)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]»', expected 'NumberTheory.Zsqrtd.GaussianInt.termℤ[i]._@.NumberTheory.Zsqrtd.GaussianInt._hyg.6'
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
    to_real_im
    ( x : ℤ[i] ) : ( ( x . im : ℤ ) : ℝ ) = ( x : ℂ ) . im
    := by simp [ to_complex_def ]
#align gaussian_int.to_real_im GaussianInt.to_real_im

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
      (Command.declId `to_complex_re [])
      (Command.declSig
       [(Term.explicitBinder "(" [`x `y] [":" (termℤ "ℤ")] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.proj
          (Term.typeAscription
           "("
           (Term.typeAscription
            "("
            (Term.anonymousCtor "⟨" [`x "," `y] "⟩")
            ":"
            [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
            ")")
           ":"
           [(Data.Complex.Basic.termℂ "ℂ")]
           ")")
          "."
          `re)
         "="
         `x)))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `to_complex_def)] "]"] [])])))
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
         [(Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `to_complex_def)] "]"] [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `to_complex_def)] "]"] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `to_complex_def
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.proj
        (Term.typeAscription
         "("
         (Term.typeAscription
          "("
          (Term.anonymousCtor "⟨" [`x "," `y] "⟩")
          ":"
          [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
          ")")
         ":"
         [(Data.Complex.Basic.termℂ "ℂ")]
         ")")
        "."
        `re)
       "="
       `x)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.proj
       (Term.typeAscription
        "("
        (Term.typeAscription
         "("
         (Term.anonymousCtor "⟨" [`x "," `y] "⟩")
         ":"
         [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
         ")")
        ":"
        [(Data.Complex.Basic.termℂ "ℂ")]
        ")")
       "."
       `re)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.typeAscription
       "("
       (Term.typeAscription
        "("
        (Term.anonymousCtor "⟨" [`x "," `y] "⟩")
        ":"
        [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
        ")")
       ":"
       [(Data.Complex.Basic.termℂ "ℂ")]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Complex.Basic.termℂ "ℂ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription
       "("
       (Term.anonymousCtor "⟨" [`x "," `y] "⟩")
       ":"
       [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]»', expected 'NumberTheory.Zsqrtd.GaussianInt.termℤ[i]._@.NumberTheory.Zsqrtd.GaussianInt._hyg.6'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ simp ]
  theorem
    to_complex_re
    ( x y : ℤ ) : ( ( ⟨ x , y ⟩ : ℤ[i] ) : ℂ ) . re = x
    := by simp [ to_complex_def ]
#align gaussian_int.to_complex_re GaussianInt.to_complex_re

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
      (Command.declId `to_complex_im [])
      (Command.declSig
       [(Term.explicitBinder "(" [`x `y] [":" (termℤ "ℤ")] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.proj
          (Term.typeAscription
           "("
           (Term.typeAscription
            "("
            (Term.anonymousCtor "⟨" [`x "," `y] "⟩")
            ":"
            [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
            ")")
           ":"
           [(Data.Complex.Basic.termℂ "ℂ")]
           ")")
          "."
          `im)
         "="
         `y)))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `to_complex_def)] "]"] [])])))
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
         [(Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `to_complex_def)] "]"] [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `to_complex_def)] "]"] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `to_complex_def
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.proj
        (Term.typeAscription
         "("
         (Term.typeAscription
          "("
          (Term.anonymousCtor "⟨" [`x "," `y] "⟩")
          ":"
          [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
          ")")
         ":"
         [(Data.Complex.Basic.termℂ "ℂ")]
         ")")
        "."
        `im)
       "="
       `y)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.proj
       (Term.typeAscription
        "("
        (Term.typeAscription
         "("
         (Term.anonymousCtor "⟨" [`x "," `y] "⟩")
         ":"
         [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
         ")")
        ":"
        [(Data.Complex.Basic.termℂ "ℂ")]
        ")")
       "."
       `im)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.typeAscription
       "("
       (Term.typeAscription
        "("
        (Term.anonymousCtor "⟨" [`x "," `y] "⟩")
        ":"
        [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
        ")")
       ":"
       [(Data.Complex.Basic.termℂ "ℂ")]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Complex.Basic.termℂ "ℂ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription
       "("
       (Term.anonymousCtor "⟨" [`x "," `y] "⟩")
       ":"
       [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]»', expected 'NumberTheory.Zsqrtd.GaussianInt.termℤ[i]._@.NumberTheory.Zsqrtd.GaussianInt._hyg.6'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ simp ]
  theorem
    to_complex_im
    ( x y : ℤ ) : ( ( ⟨ x , y ⟩ : ℤ[i] ) : ℂ ) . im = y
    := by simp [ to_complex_def ]
#align gaussian_int.to_complex_im GaussianInt.to_complex_im

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
      (Command.declId `to_complex_add [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`x `y]
         [":" (NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.typeAscription
          "("
          (Term.typeAscription
           "("
           («term_+_» `x "+" `y)
           ":"
           [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
           ")")
          ":"
          [(Data.Complex.Basic.termℂ "ℂ")]
          ")")
         "="
         («term_+_» `x "+" `y))))
      (Command.declValSimple
       ":="
       (Term.app (Term.proj `toComplex "." `map_add) [(Term.hole "_") (Term.hole "_")])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj `toComplex "." `map_add) [(Term.hole "_") (Term.hole "_")])
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
      (Term.proj `toComplex "." `map_add)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `toComplex
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.typeAscription
        "("
        (Term.typeAscription
         "("
         («term_+_» `x "+" `y)
         ":"
         [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
         ")")
        ":"
        [(Data.Complex.Basic.termℂ "ℂ")]
        ")")
       "="
       («term_+_» `x "+" `y))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_» `x "+" `y)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.typeAscription
       "("
       (Term.typeAscription
        "("
        («term_+_» `x "+" `y)
        ":"
        [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
        ")")
       ":"
       [(Data.Complex.Basic.termℂ "ℂ")]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Complex.Basic.termℂ "ℂ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription
       "("
       («term_+_» `x "+" `y)
       ":"
       [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]»', expected 'NumberTheory.Zsqrtd.GaussianInt.termℤ[i]._@.NumberTheory.Zsqrtd.GaussianInt._hyg.6'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ simp ]
  theorem
    to_complex_add
    ( x y : ℤ[i] ) : ( ( x + y : ℤ[i] ) : ℂ ) = x + y
    := toComplex . map_add _ _
#align gaussian_int.to_complex_add GaussianInt.to_complex_add

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
      (Command.declId `to_complex_mul [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`x `y]
         [":" (NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.typeAscription
          "("
          (Term.typeAscription
           "("
           («term_*_» `x "*" `y)
           ":"
           [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
           ")")
          ":"
          [(Data.Complex.Basic.termℂ "ℂ")]
          ")")
         "="
         («term_*_» `x "*" `y))))
      (Command.declValSimple
       ":="
       (Term.app (Term.proj `toComplex "." `map_mul) [(Term.hole "_") (Term.hole "_")])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj `toComplex "." `map_mul) [(Term.hole "_") (Term.hole "_")])
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
      (Term.proj `toComplex "." `map_mul)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `toComplex
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.typeAscription
        "("
        (Term.typeAscription
         "("
         («term_*_» `x "*" `y)
         ":"
         [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
         ")")
        ":"
        [(Data.Complex.Basic.termℂ "ℂ")]
        ")")
       "="
       («term_*_» `x "*" `y))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_» `x "*" `y)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.typeAscription
       "("
       (Term.typeAscription
        "("
        («term_*_» `x "*" `y)
        ":"
        [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
        ")")
       ":"
       [(Data.Complex.Basic.termℂ "ℂ")]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Complex.Basic.termℂ "ℂ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription
       "("
       («term_*_» `x "*" `y)
       ":"
       [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]»', expected 'NumberTheory.Zsqrtd.GaussianInt.termℤ[i]._@.NumberTheory.Zsqrtd.GaussianInt._hyg.6'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ simp ]
  theorem
    to_complex_mul
    ( x y : ℤ[i] ) : ( ( x * y : ℤ[i] ) : ℂ ) = x * y
    := toComplex . map_mul _ _
#align gaussian_int.to_complex_mul GaussianInt.to_complex_mul

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
      (Command.declId `to_complex_one [])
      (Command.declSig
       []
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.typeAscription
          "("
          (Term.typeAscription
           "("
           (num "1")
           ":"
           [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
           ")")
          ":"
          [(Data.Complex.Basic.termℂ "ℂ")]
          ")")
         "="
         (num "1"))))
      (Command.declValSimple ":=" (Term.proj `toComplex "." `map_one) [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `toComplex "." `map_one)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `toComplex
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.typeAscription
        "("
        (Term.typeAscription
         "("
         (num "1")
         ":"
         [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
         ")")
        ":"
        [(Data.Complex.Basic.termℂ "ℂ")]
        ")")
       "="
       (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.typeAscription
       "("
       (Term.typeAscription
        "("
        (num "1")
        ":"
        [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
        ")")
       ":"
       [(Data.Complex.Basic.termℂ "ℂ")]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Complex.Basic.termℂ "ℂ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription
       "("
       (num "1")
       ":"
       [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]»', expected 'NumberTheory.Zsqrtd.GaussianInt.termℤ[i]._@.NumberTheory.Zsqrtd.GaussianInt._hyg.6'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ simp ] theorem to_complex_one : ( ( 1 : ℤ[i] ) : ℂ ) = 1 := toComplex . map_one
#align gaussian_int.to_complex_one GaussianInt.to_complex_one

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
      (Command.declId `to_complex_zero [])
      (Command.declSig
       []
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.typeAscription
          "("
          (Term.typeAscription
           "("
           (num "0")
           ":"
           [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
           ")")
          ":"
          [(Data.Complex.Basic.termℂ "ℂ")]
          ")")
         "="
         (num "0"))))
      (Command.declValSimple ":=" (Term.proj `toComplex "." `map_zero) [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `toComplex "." `map_zero)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `toComplex
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.typeAscription
        "("
        (Term.typeAscription
         "("
         (num "0")
         ":"
         [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
         ")")
        ":"
        [(Data.Complex.Basic.termℂ "ℂ")]
        ")")
       "="
       (num "0"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.typeAscription
       "("
       (Term.typeAscription
        "("
        (num "0")
        ":"
        [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
        ")")
       ":"
       [(Data.Complex.Basic.termℂ "ℂ")]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Complex.Basic.termℂ "ℂ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription
       "("
       (num "0")
       ":"
       [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]»', expected 'NumberTheory.Zsqrtd.GaussianInt.termℤ[i]._@.NumberTheory.Zsqrtd.GaussianInt._hyg.6'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ simp ] theorem to_complex_zero : ( ( 0 : ℤ[i] ) : ℂ ) = 0 := toComplex . map_zero
#align gaussian_int.to_complex_zero GaussianInt.to_complex_zero

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
      (Command.declId `to_complex_neg [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`x]
         [":" (NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.typeAscription
          "("
          (Term.typeAscription
           "("
           («term-_» "-" `x)
           ":"
           [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
           ")")
          ":"
          [(Data.Complex.Basic.termℂ "ℂ")]
          ")")
         "="
         («term-_» "-" `x))))
      (Command.declValSimple
       ":="
       (Term.app (Term.proj `toComplex "." `map_neg) [(Term.hole "_")])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj `toComplex "." `map_neg) [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `toComplex "." `map_neg)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `toComplex
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.typeAscription
        "("
        (Term.typeAscription
         "("
         («term-_» "-" `x)
         ":"
         [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
         ")")
        ":"
        [(Data.Complex.Basic.termℂ "ℂ")]
        ")")
       "="
       («term-_» "-" `x))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term-_» "-" `x)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 75 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 75, (some 75, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.typeAscription
       "("
       (Term.typeAscription
        "("
        («term-_» "-" `x)
        ":"
        [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
        ")")
       ":"
       [(Data.Complex.Basic.termℂ "ℂ")]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Complex.Basic.termℂ "ℂ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription
       "("
       («term-_» "-" `x)
       ":"
       [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]»', expected 'NumberTheory.Zsqrtd.GaussianInt.termℤ[i]._@.NumberTheory.Zsqrtd.GaussianInt._hyg.6'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ simp ]
  theorem to_complex_neg ( x : ℤ[i] ) : ( ( - x : ℤ[i] ) : ℂ ) = - x := toComplex . map_neg _
#align gaussian_int.to_complex_neg GaussianInt.to_complex_neg

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
      (Command.declId `to_complex_sub [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`x `y]
         [":" (NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.typeAscription
          "("
          (Term.typeAscription
           "("
           («term_-_» `x "-" `y)
           ":"
           [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
           ")")
          ":"
          [(Data.Complex.Basic.termℂ "ℂ")]
          ")")
         "="
         («term_-_» `x "-" `y))))
      (Command.declValSimple
       ":="
       (Term.app (Term.proj `toComplex "." `map_sub) [(Term.hole "_") (Term.hole "_")])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj `toComplex "." `map_sub) [(Term.hole "_") (Term.hole "_")])
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
      (Term.proj `toComplex "." `map_sub)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `toComplex
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.typeAscription
        "("
        (Term.typeAscription
         "("
         («term_-_» `x "-" `y)
         ":"
         [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
         ")")
        ":"
        [(Data.Complex.Basic.termℂ "ℂ")]
        ")")
       "="
       («term_-_» `x "-" `y))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_-_» `x "-" `y)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.typeAscription
       "("
       (Term.typeAscription
        "("
        («term_-_» `x "-" `y)
        ":"
        [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
        ")")
       ":"
       [(Data.Complex.Basic.termℂ "ℂ")]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Complex.Basic.termℂ "ℂ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription
       "("
       («term_-_» `x "-" `y)
       ":"
       [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]»', expected 'NumberTheory.Zsqrtd.GaussianInt.termℤ[i]._@.NumberTheory.Zsqrtd.GaussianInt._hyg.6'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ simp ]
  theorem
    to_complex_sub
    ( x y : ℤ[i] ) : ( ( x - y : ℤ[i] ) : ℂ ) = x - y
    := toComplex . map_sub _ _
#align gaussian_int.to_complex_sub GaussianInt.to_complex_sub

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
      (Command.declId `to_complex_inj [])
      (Command.declSig
       [(Term.implicitBinder
         "{"
         [`x `y]
         [":" (NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
         "}")]
       (Term.typeSpec
        ":"
        («term_↔_»
         («term_=_» (Term.typeAscription "(" `x ":" [(Data.Complex.Basic.termℂ "ℂ")] ")") "=" `y)
         "↔"
         («term_=_» `x "=" `y))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.«tactic_<;>_»
            (Tactic.«tactic_<;>_»
             (Tactic.cases "cases" [(Tactic.casesTarget [] `x)] [] [])
             "<;>"
             (Tactic.cases "cases" [(Tactic.casesTarget [] `y)] [] []))
            "<;>"
            (Tactic.simp
             "simp"
             []
             []
             []
             ["[" [(Tactic.simpLemma [] [] `to_complex_def₂)] "]"]
             []))])))
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
         [(Tactic.«tactic_<;>_»
           (Tactic.«tactic_<;>_»
            (Tactic.cases "cases" [(Tactic.casesTarget [] `x)] [] [])
            "<;>"
            (Tactic.cases "cases" [(Tactic.casesTarget [] `y)] [] []))
           "<;>"
           (Tactic.simp
            "simp"
            []
            []
            []
            ["[" [(Tactic.simpLemma [] [] `to_complex_def₂)] "]"]
            []))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.«tactic_<;>_»
       (Tactic.«tactic_<;>_»
        (Tactic.cases "cases" [(Tactic.casesTarget [] `x)] [] [])
        "<;>"
        (Tactic.cases "cases" [(Tactic.casesTarget [] `y)] [] []))
       "<;>"
       (Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `to_complex_def₂)] "]"] []))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `to_complex_def₂)] "]"] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `to_complex_def₂
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 2 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
      (Tactic.«tactic_<;>_»
       (Tactic.cases "cases" [(Tactic.casesTarget [] `x)] [] [])
       "<;>"
       (Tactic.cases "cases" [(Tactic.casesTarget [] `y)] [] []))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.cases "cases" [(Tactic.casesTarget [] `y)] [] [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 2 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
      (Tactic.cases "cases" [(Tactic.casesTarget [] `x)] [] [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_↔_»
       («term_=_» (Term.typeAscription "(" `x ":" [(Data.Complex.Basic.termℂ "ℂ")] ")") "=" `y)
       "↔"
       («term_=_» `x "=" `y))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_» `x "=" `y)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 21 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 20, term))
      («term_=_» (Term.typeAscription "(" `x ":" [(Data.Complex.Basic.termℂ "ℂ")] ")") "=" `y)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.typeAscription "(" `x ":" [(Data.Complex.Basic.termℂ "ℂ")] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Complex.Basic.termℂ "ℂ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 21 >? 50, (some 51, term) <=? (some 20, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 20, (some 21,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.implicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.implicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.implicitBinder', expected 'Lean.Parser.Term.explicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.implicitBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]»', expected 'NumberTheory.Zsqrtd.GaussianInt.termℤ[i]._@.NumberTheory.Zsqrtd.GaussianInt._hyg.6'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.implicitBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ simp ]
  theorem
    to_complex_inj
    { x y : ℤ[i] } : ( x : ℂ ) = y ↔ x = y
    := by cases x <;> cases y <;> simp [ to_complex_def₂ ]
#align gaussian_int.to_complex_inj GaussianInt.to_complex_inj

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
      (Command.declId `to_complex_eq_zero [])
      (Command.declSig
       [(Term.implicitBinder
         "{"
         [`x]
         [":" (NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
         "}")]
       (Term.typeSpec
        ":"
        («term_↔_»
         («term_=_»
          (Term.typeAscription "(" `x ":" [(Data.Complex.Basic.termℂ "ℂ")] ")")
          "="
          (num "0"))
         "↔"
         («term_=_» `x "=" (num "0")))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `to_complex_zero)
              ","
              (Tactic.rwRule [] `to_complex_inj)]
             "]")
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
         [(Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `to_complex_zero)
             ","
             (Tactic.rwRule [] `to_complex_inj)]
            "]")
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `to_complex_zero)
         ","
         (Tactic.rwRule [] `to_complex_inj)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `to_complex_inj
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `to_complex_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_↔_»
       («term_=_»
        (Term.typeAscription "(" `x ":" [(Data.Complex.Basic.termℂ "ℂ")] ")")
        "="
        (num "0"))
       "↔"
       («term_=_» `x "=" (num "0")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_» `x "=" (num "0"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 21 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 20, term))
      («term_=_»
       (Term.typeAscription "(" `x ":" [(Data.Complex.Basic.termℂ "ℂ")] ")")
       "="
       (num "0"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.typeAscription "(" `x ":" [(Data.Complex.Basic.termℂ "ℂ")] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Complex.Basic.termℂ "ℂ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 21 >? 50, (some 51, term) <=? (some 20, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 20, (some 21,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.implicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.implicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.implicitBinder', expected 'Lean.Parser.Term.explicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.implicitBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]»', expected 'NumberTheory.Zsqrtd.GaussianInt.termℤ[i]._@.NumberTheory.Zsqrtd.GaussianInt._hyg.6'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.implicitBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ simp ]
  theorem
    to_complex_eq_zero
    { x : ℤ[i] } : ( x : ℂ ) = 0 ↔ x = 0
    := by rw [ ← to_complex_zero , to_complex_inj ]
#align gaussian_int.to_complex_eq_zero GaussianInt.to_complex_eq_zero

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
      (Command.declId `nat_cast_real_norm [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`x]
         [":" (NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.typeAscription "(" (Term.proj `x "." `norm) ":" [(Data.Real.Basic.termℝ "ℝ")] ")")
         "="
         (Term.proj
          (Term.typeAscription "(" `x ":" [(Data.Complex.Basic.termℂ "ℂ")] ")")
          "."
          `normSq))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.«tactic_<;>_»
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] `Zsqrtd.norm) "," (Tactic.rwRule [] `norm_sq)]
              "]")
             [])
            "<;>"
            (Tactic.simp "simp" [] [] [] [] []))])))
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
         [(Tactic.«tactic_<;>_»
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [] `Zsqrtd.norm) "," (Tactic.rwRule [] `norm_sq)]
             "]")
            [])
           "<;>"
           (Tactic.simp "simp" [] [] [] [] []))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.«tactic_<;>_»
       (Tactic.rwSeq
        "rw"
        []
        (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Zsqrtd.norm) "," (Tactic.rwRule [] `norm_sq)] "]")
        [])
       "<;>"
       (Tactic.simp "simp" [] [] [] [] []))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] [] [] [])
[PrettyPrinter.parenthesize] ...precedences are 2 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Zsqrtd.norm) "," (Tactic.rwRule [] `norm_sq)] "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `norm_sq
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Zsqrtd.norm
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.typeAscription "(" (Term.proj `x "." `norm) ":" [(Data.Real.Basic.termℝ "ℝ")] ")")
       "="
       (Term.proj
        (Term.typeAscription "(" `x ":" [(Data.Complex.Basic.termℂ "ℂ")] ")")
        "."
        `normSq))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.typeAscription "(" `x ":" [(Data.Complex.Basic.termℂ "ℂ")] ")") "." `normSq)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.typeAscription "(" `x ":" [(Data.Complex.Basic.termℂ "ℂ")] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Complex.Basic.termℂ "ℂ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.typeAscription "(" (Term.proj `x "." `norm) ":" [(Data.Real.Basic.termℝ "ℝ")] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Real.Basic.termℝ "ℝ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `x "." `norm)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]»', expected 'NumberTheory.Zsqrtd.GaussianInt.termℤ[i]._@.NumberTheory.Zsqrtd.GaussianInt._hyg.6'
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
    nat_cast_real_norm
    ( x : ℤ[i] ) : ( x . norm : ℝ ) = ( x : ℂ ) . normSq
    := by rw [ Zsqrtd.norm , norm_sq ] <;> simp
#align gaussian_int.nat_cast_real_norm GaussianInt.nat_cast_real_norm

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
      (Command.declId `nat_cast_complex_norm [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`x]
         [":" (NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.typeAscription "(" (Term.proj `x "." `norm) ":" [(Data.Complex.Basic.termℂ "ℂ")] ")")
         "="
         (Term.proj
          (Term.typeAscription "(" `x ":" [(Data.Complex.Basic.termℂ "ℂ")] ")")
          "."
          `normSq))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.«tactic_<;>_»
            (Tactic.«tactic_<;>_»
             (Tactic.cases "cases" [(Tactic.casesTarget [] `x)] [] [])
             "<;>"
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [] `Zsqrtd.norm) "," (Tactic.rwRule [] `norm_sq)]
               "]")
              []))
            "<;>"
            (Tactic.simp "simp" [] [] [] [] []))])))
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
         [(Tactic.«tactic_<;>_»
           (Tactic.«tactic_<;>_»
            (Tactic.cases "cases" [(Tactic.casesTarget [] `x)] [] [])
            "<;>"
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] `Zsqrtd.norm) "," (Tactic.rwRule [] `norm_sq)]
              "]")
             []))
           "<;>"
           (Tactic.simp "simp" [] [] [] [] []))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.«tactic_<;>_»
       (Tactic.«tactic_<;>_»
        (Tactic.cases "cases" [(Tactic.casesTarget [] `x)] [] [])
        "<;>"
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule [] `Zsqrtd.norm) "," (Tactic.rwRule [] `norm_sq)]
          "]")
         []))
       "<;>"
       (Tactic.simp "simp" [] [] [] [] []))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] [] [] [])
[PrettyPrinter.parenthesize] ...precedences are 2 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
      (Tactic.«tactic_<;>_»
       (Tactic.cases "cases" [(Tactic.casesTarget [] `x)] [] [])
       "<;>"
       (Tactic.rwSeq
        "rw"
        []
        (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Zsqrtd.norm) "," (Tactic.rwRule [] `norm_sq)] "]")
        []))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Zsqrtd.norm) "," (Tactic.rwRule [] `norm_sq)] "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `norm_sq
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Zsqrtd.norm
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 2 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
      (Tactic.cases "cases" [(Tactic.casesTarget [] `x)] [] [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.typeAscription "(" (Term.proj `x "." `norm) ":" [(Data.Complex.Basic.termℂ "ℂ")] ")")
       "="
       (Term.proj
        (Term.typeAscription "(" `x ":" [(Data.Complex.Basic.termℂ "ℂ")] ")")
        "."
        `normSq))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.typeAscription "(" `x ":" [(Data.Complex.Basic.termℂ "ℂ")] ")") "." `normSq)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.typeAscription "(" `x ":" [(Data.Complex.Basic.termℂ "ℂ")] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Complex.Basic.termℂ "ℂ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.typeAscription "(" (Term.proj `x "." `norm) ":" [(Data.Complex.Basic.termℂ "ℂ")] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Complex.Basic.termℂ "ℂ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `x "." `norm)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]»', expected 'NumberTheory.Zsqrtd.GaussianInt.termℤ[i]._@.NumberTheory.Zsqrtd.GaussianInt._hyg.6'
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
    nat_cast_complex_norm
    ( x : ℤ[i] ) : ( x . norm : ℂ ) = ( x : ℂ ) . normSq
    := by cases x <;> rw [ Zsqrtd.norm , norm_sq ] <;> simp
#align gaussian_int.nat_cast_complex_norm GaussianInt.nat_cast_complex_norm

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `norm_nonneg [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`x]
         [":" (NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
         []
         ")")]
       (Term.typeSpec ":" («term_≤_» (num "0") "≤" (Term.app `norm [`x]))))
      (Command.declValSimple
       ":="
       (Term.app
        `norm_nonneg
        [(Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented [(Mathlib.Tactic.normNum "norm_num" [] [] [])])))
         (Term.hole "_")])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `norm_nonneg
       [(Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented [(Mathlib.Tactic.normNum "norm_num" [] [] [])])))
        (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented [(Mathlib.Tactic.normNum "norm_num" [] [] [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.normNum "norm_num" [] [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, tactic) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.byTactic
      "by"
      (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Mathlib.Tactic.normNum "norm_num" [] [] [])])))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `norm_nonneg
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_≤_» (num "0") "≤" (Term.app `norm [`x]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `norm [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `norm
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]»', expected 'NumberTheory.Zsqrtd.GaussianInt.termℤ[i]._@.NumberTheory.Zsqrtd.GaussianInt._hyg.6'
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
theorem norm_nonneg ( x : ℤ[i] ) : 0 ≤ norm x := norm_nonneg by norm_num _
#align gaussian_int.norm_nonneg GaussianInt.norm_nonneg

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
      (Command.declId `norm_eq_zero [])
      (Command.declSig
       [(Term.implicitBinder
         "{"
         [`x]
         [":" (NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
         "}")]
       (Term.typeSpec
        ":"
        («term_↔_»
         («term_=_» (Term.app `norm [`x]) "=" (num "0"))
         "↔"
         («term_=_» `x "=" (num "0")))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.«tactic_<;>_»
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule
                [(patternIgnore (token.«← » "←"))]
                (Term.app
                 (Term.explicit "@" `Int.cast_inj)
                 [(Data.Real.Basic.termℝ "ℝ") (Term.hole "_") (Term.hole "_") (Term.hole "_")]))]
              "]")
             [])
            "<;>"
            (Tactic.simp "simp" [] [] [] [] []))])))
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
         [(Tactic.«tactic_<;>_»
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule
               [(patternIgnore (token.«← » "←"))]
               (Term.app
                (Term.explicit "@" `Int.cast_inj)
                [(Data.Real.Basic.termℝ "ℝ") (Term.hole "_") (Term.hole "_") (Term.hole "_")]))]
             "]")
            [])
           "<;>"
           (Tactic.simp "simp" [] [] [] [] []))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.«tactic_<;>_»
       (Tactic.rwSeq
        "rw"
        []
        (Tactic.rwRuleSeq
         "["
         [(Tactic.rwRule
           [(patternIgnore (token.«← » "←"))]
           (Term.app
            (Term.explicit "@" `Int.cast_inj)
            [(Data.Real.Basic.termℝ "ℝ") (Term.hole "_") (Term.hole "_") (Term.hole "_")]))]
         "]")
        [])
       "<;>"
       (Tactic.simp "simp" [] [] [] [] []))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] [] [] [])
[PrettyPrinter.parenthesize] ...precedences are 2 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule
          [(patternIgnore (token.«← » "←"))]
          (Term.app
           (Term.explicit "@" `Int.cast_inj)
           [(Data.Real.Basic.termℝ "ℝ") (Term.hole "_") (Term.hole "_") (Term.hole "_")]))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.explicit "@" `Int.cast_inj)
       [(Data.Real.Basic.termℝ "ℝ") (Term.hole "_") (Term.hole "_") (Term.hole "_")])
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Basic.termℝ', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Basic.termℝ', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Data.Real.Basic.termℝ "ℝ")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.explicit "@" `Int.cast_inj)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Int.cast_inj
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (some 1024,
     term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_↔_» («term_=_» (Term.app `norm [`x]) "=" (num "0")) "↔" («term_=_» `x "=" (num "0")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_» `x "=" (num "0"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 21 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 20, term))
      («term_=_» (Term.app `norm [`x]) "=" (num "0"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app `norm [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `norm
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 21 >? 50, (some 51, term) <=? (some 20, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 20, (some 21,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.implicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.implicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.implicitBinder', expected 'Lean.Parser.Term.explicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.implicitBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]»', expected 'NumberTheory.Zsqrtd.GaussianInt.termℤ[i]._@.NumberTheory.Zsqrtd.GaussianInt._hyg.6'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.implicitBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ simp ]
  theorem
    norm_eq_zero
    { x : ℤ[i] } : norm x = 0 ↔ x = 0
    := by rw [ ← @ Int.cast_inj ℝ _ _ _ ] <;> simp
#align gaussian_int.norm_eq_zero GaussianInt.norm_eq_zero

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `norm_pos [])
      (Command.declSig
       [(Term.implicitBinder
         "{"
         [`x]
         [":" (NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
         "}")]
       (Term.typeSpec
        ":"
        («term_↔_»
         («term_<_» (num "0") "<" (Term.app `norm [`x]))
         "↔"
         («term_≠_» `x "≠" (num "0")))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.«tactic_<;>_»
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] `lt_iff_le_and_ne)
               ","
               (Tactic.rwRule [] `Ne.def)
               ","
               (Tactic.rwRule [] `eq_comm)
               ","
               (Tactic.rwRule [] `norm_eq_zero)]
              "]")
             [])
            "<;>"
            (Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `norm_nonneg)] "]"] []))])))
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
         [(Tactic.«tactic_<;>_»
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [] `lt_iff_le_and_ne)
              ","
              (Tactic.rwRule [] `Ne.def)
              ","
              (Tactic.rwRule [] `eq_comm)
              ","
              (Tactic.rwRule [] `norm_eq_zero)]
             "]")
            [])
           "<;>"
           (Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `norm_nonneg)] "]"] []))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.«tactic_<;>_»
       (Tactic.rwSeq
        "rw"
        []
        (Tactic.rwRuleSeq
         "["
         [(Tactic.rwRule [] `lt_iff_le_and_ne)
          ","
          (Tactic.rwRule [] `Ne.def)
          ","
          (Tactic.rwRule [] `eq_comm)
          ","
          (Tactic.rwRule [] `norm_eq_zero)]
         "]")
        [])
       "<;>"
       (Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `norm_nonneg)] "]"] []))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `norm_nonneg)] "]"] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `norm_nonneg
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 2 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `lt_iff_le_and_ne)
         ","
         (Tactic.rwRule [] `Ne.def)
         ","
         (Tactic.rwRule [] `eq_comm)
         ","
         (Tactic.rwRule [] `norm_eq_zero)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `norm_eq_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `eq_comm
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Ne.def
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `lt_iff_le_and_ne
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_↔_» («term_<_» (num "0") "<" (Term.app `norm [`x])) "↔" («term_≠_» `x "≠" (num "0")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≠_» `x "≠" (num "0"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 21 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 20, term))
      («term_<_» (num "0") "<" (Term.app `norm [`x]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `norm [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `norm
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 21 >? 50, (some 51, term) <=? (some 20, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 20, (some 21,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.implicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.implicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.implicitBinder', expected 'Lean.Parser.Term.explicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.implicitBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]»', expected 'NumberTheory.Zsqrtd.GaussianInt.termℤ[i]._@.NumberTheory.Zsqrtd.GaussianInt._hyg.6'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.implicitBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  norm_pos
  { x : ℤ[i] } : 0 < norm x ↔ x ≠ 0
  := by rw [ lt_iff_le_and_ne , Ne.def , eq_comm , norm_eq_zero ] <;> simp [ norm_nonneg ]
#align gaussian_int.norm_pos GaussianInt.norm_pos

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `coe_nat_abs_norm [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`x]
         [":" (NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.typeAscription
          "("
          (Term.proj (Term.proj `x "." `norm) "." `natAbs)
          ":"
          [(termℤ "ℤ")]
          ")")
         "="
         (Term.proj `x "." `norm))))
      (Command.declValSimple
       ":="
       (Term.app `Int.natAbs_of_nonneg [(Term.app `norm_nonneg [(Term.hole "_")])])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Int.natAbs_of_nonneg [(Term.app `norm_nonneg [(Term.hole "_")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `norm_nonneg [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `norm_nonneg
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `norm_nonneg [(Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Int.natAbs_of_nonneg
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.typeAscription
        "("
        (Term.proj (Term.proj `x "." `norm) "." `natAbs)
        ":"
        [(termℤ "ℤ")]
        ")")
       "="
       (Term.proj `x "." `norm))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `x "." `norm)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.typeAscription
       "("
       (Term.proj (Term.proj `x "." `norm) "." `natAbs)
       ":"
       [(termℤ "ℤ")]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (termℤ "ℤ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.proj `x "." `norm) "." `natAbs)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj `x "." `norm)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]»', expected 'NumberTheory.Zsqrtd.GaussianInt.termℤ[i]._@.NumberTheory.Zsqrtd.GaussianInt._hyg.6'
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
theorem
  coe_nat_abs_norm
  ( x : ℤ[i] ) : ( x . norm . natAbs : ℤ ) = x . norm
  := Int.natAbs_of_nonneg norm_nonneg _
#align gaussian_int.coe_nat_abs_norm GaussianInt.coe_nat_abs_norm

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
      (Command.declId `nat_cast_nat_abs_norm [])
      (Command.declSig
       [(Term.implicitBinder "{" [`α] [":" (Term.type "Type" [(Level.hole "_")])] "}")
        (Term.instBinder "[" [] (Term.app `Ring [`α]) "]")
        (Term.explicitBinder
         "("
         [`x]
         [":" (NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.typeAscription "(" (Term.proj (Term.proj `x "." `norm) "." `natAbs) ":" [`α] ")")
         "="
         (Term.proj `x "." `norm))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Int.cast_ofNat)
              ","
              (Tactic.rwRule [] `coe_nat_abs_norm)]
             "]")
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
         [(Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Int.cast_ofNat)
             ","
             (Tactic.rwRule [] `coe_nat_abs_norm)]
            "]")
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Int.cast_ofNat)
         ","
         (Tactic.rwRule [] `coe_nat_abs_norm)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `coe_nat_abs_norm
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Int.cast_ofNat
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.typeAscription "(" (Term.proj (Term.proj `x "." `norm) "." `natAbs) ":" [`α] ")")
       "="
       (Term.proj `x "." `norm))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `x "." `norm)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.typeAscription "(" (Term.proj (Term.proj `x "." `norm) "." `natAbs) ":" [`α] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `α
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.proj `x "." `norm) "." `natAbs)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj `x "." `norm)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]»', expected 'NumberTheory.Zsqrtd.GaussianInt.termℤ[i]._@.NumberTheory.Zsqrtd.GaussianInt._hyg.6'
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
    nat_cast_nat_abs_norm
    { α : Type _ } [ Ring α ] ( x : ℤ[i] ) : ( x . norm . natAbs : α ) = x . norm
    := by rw [ ← Int.cast_ofNat , coe_nat_abs_norm ]
#align gaussian_int.nat_cast_nat_abs_norm GaussianInt.nat_cast_nat_abs_norm

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `nat_abs_norm_eq [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`x]
         [":" (NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.proj (Term.proj `x "." `norm) "." `natAbs)
         "="
         («term_+_»
          («term_*_»
           (Term.proj (Term.proj `x "." `re) "." `natAbs)
           "*"
           (Term.proj (Term.proj `x "." `re) "." `natAbs))
          "+"
          («term_*_»
           (Term.proj (Term.proj `x "." `im) "." `natAbs)
           "*"
           (Term.proj (Term.proj `x "." `im) "." `natAbs))))))
      (Command.declValSimple
       ":="
       («term_<|_»
        `Int.ofNat.inj
        "<|"
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Tactic.simp "simp" [] [] [] [] [])
            ";"
            (Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `Zsqrtd.norm)] "]"] [])]))))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_»
       `Int.ofNat.inj
       "<|"
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.simp "simp" [] [] [] [] [])
           ";"
           (Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `Zsqrtd.norm)] "]"] [])]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.simp "simp" [] [] [] [] [])
          ";"
          (Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `Zsqrtd.norm)] "]"] [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `Zsqrtd.norm)] "]"] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Zsqrtd.norm
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] [] [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      `Int.ofNat.inj
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.proj (Term.proj `x "." `norm) "." `natAbs)
       "="
       («term_+_»
        («term_*_»
         (Term.proj (Term.proj `x "." `re) "." `natAbs)
         "*"
         (Term.proj (Term.proj `x "." `re) "." `natAbs))
        "+"
        («term_*_»
         (Term.proj (Term.proj `x "." `im) "." `natAbs)
         "*"
         (Term.proj (Term.proj `x "." `im) "." `natAbs))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_»
       («term_*_»
        (Term.proj (Term.proj `x "." `re) "." `natAbs)
        "*"
        (Term.proj (Term.proj `x "." `re) "." `natAbs))
       "+"
       («term_*_»
        (Term.proj (Term.proj `x "." `im) "." `natAbs)
        "*"
        (Term.proj (Term.proj `x "." `im) "." `natAbs)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_»
       (Term.proj (Term.proj `x "." `im) "." `natAbs)
       "*"
       (Term.proj (Term.proj `x "." `im) "." `natAbs))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.proj `x "." `im) "." `natAbs)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj `x "." `im)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (Term.proj (Term.proj `x "." `im) "." `natAbs)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj `x "." `im)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      («term_*_»
       (Term.proj (Term.proj `x "." `re) "." `natAbs)
       "*"
       (Term.proj (Term.proj `x "." `re) "." `natAbs))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.proj `x "." `re) "." `natAbs)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj `x "." `re)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (Term.proj (Term.proj `x "." `re) "." `natAbs)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj `x "." `re)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 65 >? 70, (some 71, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.proj (Term.proj `x "." `norm) "." `natAbs)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj `x "." `norm)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]»', expected 'NumberTheory.Zsqrtd.GaussianInt.termℤ[i]._@.NumberTheory.Zsqrtd.GaussianInt._hyg.6'
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
theorem
  nat_abs_norm_eq
  ( x : ℤ[i] )
    : x . norm . natAbs = x . re . natAbs * x . re . natAbs + x . im . natAbs * x . im . natAbs
  := Int.ofNat.inj <| by simp ; simp [ Zsqrtd.norm ]
#align gaussian_int.nat_abs_norm_eq GaussianInt.nat_abs_norm_eq

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
       (Term.typeSpec ":" (Term.app `Div [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")])))
      (Command.declValSimple
       ":="
       (Term.anonymousCtor
        "⟨"
        [(Term.fun
          "fun"
          (Term.basicFun
           [`x `y]
           []
           "=>"
           (Term.let
            "let"
            (Term.letDecl
             (Term.letIdDecl
              `n
              []
              []
              ":="
              («term_⁻¹»
               (Term.typeAscription "(" (Term.app `norm [`y]) ":" [(Data.Rat.Init.termℚ "ℚ")] ")")
               "⁻¹")))
            []
            (Term.let
             "let"
             (Term.letDecl (Term.letIdDecl `c [] [] ":=" (Term.proj `y "." `conj)))
             []
             (Term.anonymousCtor
              "⟨"
              [(Term.app
                `round
                [(Term.typeAscription
                  "("
                  («term_*_» (Term.proj («term_*_» `x "*" `c) "." `re) "*" `n)
                  ":"
                  [(Data.Rat.Init.termℚ "ℚ")]
                  ")")])
               ","
               (Term.app
                `round
                [(Term.typeAscription
                  "("
                  («term_*_» (Term.proj («term_*_» `x "*" `c) "." `im) "*" `n)
                  ":"
                  [(Data.Rat.Init.termℚ "ℚ")]
                  ")")])]
              "⟩")))))]
        "⟩")
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.fun
         "fun"
         (Term.basicFun
          [`x `y]
          []
          "=>"
          (Term.let
           "let"
           (Term.letDecl
            (Term.letIdDecl
             `n
             []
             []
             ":="
             («term_⁻¹»
              (Term.typeAscription "(" (Term.app `norm [`y]) ":" [(Data.Rat.Init.termℚ "ℚ")] ")")
              "⁻¹")))
           []
           (Term.let
            "let"
            (Term.letDecl (Term.letIdDecl `c [] [] ":=" (Term.proj `y "." `conj)))
            []
            (Term.anonymousCtor
             "⟨"
             [(Term.app
               `round
               [(Term.typeAscription
                 "("
                 («term_*_» (Term.proj («term_*_» `x "*" `c) "." `re) "*" `n)
                 ":"
                 [(Data.Rat.Init.termℚ "ℚ")]
                 ")")])
              ","
              (Term.app
               `round
               [(Term.typeAscription
                 "("
                 («term_*_» (Term.proj («term_*_» `x "*" `c) "." `im) "*" `n)
                 ":"
                 [(Data.Rat.Init.termℚ "ℚ")]
                 ")")])]
             "⟩")))))]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`x `y]
        []
        "=>"
        (Term.let
         "let"
         (Term.letDecl
          (Term.letIdDecl
           `n
           []
           []
           ":="
           («term_⁻¹»
            (Term.typeAscription "(" (Term.app `norm [`y]) ":" [(Data.Rat.Init.termℚ "ℚ")] ")")
            "⁻¹")))
         []
         (Term.let
          "let"
          (Term.letDecl (Term.letIdDecl `c [] [] ":=" (Term.proj `y "." `conj)))
          []
          (Term.anonymousCtor
           "⟨"
           [(Term.app
             `round
             [(Term.typeAscription
               "("
               («term_*_» (Term.proj («term_*_» `x "*" `c) "." `re) "*" `n)
               ":"
               [(Data.Rat.Init.termℚ "ℚ")]
               ")")])
            ","
            (Term.app
             `round
             [(Term.typeAscription
               "("
               («term_*_» (Term.proj («term_*_» `x "*" `c) "." `im) "*" `n)
               ":"
               [(Data.Rat.Init.termℚ "ℚ")]
               ")")])]
           "⟩")))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.let
       "let"
       (Term.letDecl
        (Term.letIdDecl
         `n
         []
         []
         ":="
         («term_⁻¹»
          (Term.typeAscription "(" (Term.app `norm [`y]) ":" [(Data.Rat.Init.termℚ "ℚ")] ")")
          "⁻¹")))
       []
       (Term.let
        "let"
        (Term.letDecl (Term.letIdDecl `c [] [] ":=" (Term.proj `y "." `conj)))
        []
        (Term.anonymousCtor
         "⟨"
         [(Term.app
           `round
           [(Term.typeAscription
             "("
             («term_*_» (Term.proj («term_*_» `x "*" `c) "." `re) "*" `n)
             ":"
             [(Data.Rat.Init.termℚ "ℚ")]
             ")")])
          ","
          (Term.app
           `round
           [(Term.typeAscription
             "("
             («term_*_» (Term.proj («term_*_» `x "*" `c) "." `im) "*" `n)
             ":"
             [(Data.Rat.Init.termℚ "ℚ")]
             ")")])]
         "⟩")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.let
       "let"
       (Term.letDecl (Term.letIdDecl `c [] [] ":=" (Term.proj `y "." `conj)))
       []
       (Term.anonymousCtor
        "⟨"
        [(Term.app
          `round
          [(Term.typeAscription
            "("
            («term_*_» (Term.proj («term_*_» `x "*" `c) "." `re) "*" `n)
            ":"
            [(Data.Rat.Init.termℚ "ℚ")]
            ")")])
         ","
         (Term.app
          `round
          [(Term.typeAscription
            "("
            («term_*_» (Term.proj («term_*_» `x "*" `c) "." `im) "*" `n)
            ":"
            [(Data.Rat.Init.termℚ "ℚ")]
            ")")])]
        "⟩"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.app
         `round
         [(Term.typeAscription
           "("
           («term_*_» (Term.proj («term_*_» `x "*" `c) "." `re) "*" `n)
           ":"
           [(Data.Rat.Init.termℚ "ℚ")]
           ")")])
        ","
        (Term.app
         `round
         [(Term.typeAscription
           "("
           («term_*_» (Term.proj («term_*_» `x "*" `c) "." `im) "*" `n)
           ":"
           [(Data.Rat.Init.termℚ "ℚ")]
           ")")])]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `round
       [(Term.typeAscription
         "("
         («term_*_» (Term.proj («term_*_» `x "*" `c) "." `im) "*" `n)
         ":"
         [(Data.Rat.Init.termℚ "ℚ")]
         ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription
       "("
       («term_*_» (Term.proj («term_*_» `x "*" `c) "." `im) "*" `n)
       ":"
       [(Data.Rat.Init.termℚ "ℚ")]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Rat.Init.termℚ "ℚ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_» (Term.proj («term_*_» `x "*" `c) "." `im) "*" `n)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (Term.proj («term_*_» `x "*" `c) "." `im)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      («term_*_» `x "*" `c)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `c
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 70, (some 71, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_*_» `x "*" `c) ")")
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `round
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `round
       [(Term.typeAscription
         "("
         («term_*_» (Term.proj («term_*_» `x "*" `c) "." `re) "*" `n)
         ":"
         [(Data.Rat.Init.termℚ "ℚ")]
         ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription
       "("
       («term_*_» (Term.proj («term_*_» `x "*" `c) "." `re) "*" `n)
       ":"
       [(Data.Rat.Init.termℚ "ℚ")]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Rat.Init.termℚ "ℚ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_» (Term.proj («term_*_» `x "*" `c) "." `re) "*" `n)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (Term.proj («term_*_» `x "*" `c) "." `re)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      («term_*_» `x "*" `c)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `c
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 70, (some 71, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_*_» `x "*" `c) ")")
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `round
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `y "." `conj)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `y
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_⁻¹»
       (Term.typeAscription "(" (Term.app `norm [`y]) ":" [(Data.Rat.Init.termℚ "ℚ")] ")")
       "⁻¹")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.typeAscription "(" (Term.app `norm [`y]) ":" [(Data.Rat.Init.termℚ "ℚ")] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Rat.Init.termℚ "ℚ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `norm [`y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `norm
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app `Div [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]»', expected 'NumberTheory.Zsqrtd.GaussianInt.termℤ[i]._@.NumberTheory.Zsqrtd.GaussianInt._hyg.6'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
instance
  : Div ℤ[i]
  :=
    ⟨
      fun
        x y
          =>
          let
            n := ( norm y : ℚ ) ⁻¹
            let c := y . conj ⟨ round ( x * c . re * n : ℚ ) , round ( x * c . im * n : ℚ ) ⟩
      ⟩

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `div_def [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`x `y]
         [":" (NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         («term_/_» `x "/" `y)
         "="
         (Term.anonymousCtor
          "⟨"
          [(Term.app
            `round
            [(Term.typeAscription
              "("
              («term_/_»
               (Term.proj («term_*_» `x "*" (Term.app `conj [`y])) "." `re)
               "/"
               (Term.app `norm [`y]))
              ":"
              [(Data.Rat.Init.termℚ "ℚ")]
              ")")])
           ","
           (Term.app
            `round
            [(Term.typeAscription
              "("
              («term_/_»
               (Term.proj («term_*_» `x "*" (Term.app `conj [`y])) "." `im)
               "/"
               (Term.app `norm [`y]))
              ":"
              [(Data.Rat.Init.termℚ "ℚ")]
              ")")])]
          "⟩"))))
      (Command.declValSimple
       ":="
       (Term.show
        "show"
        («term_=_» (Term.app `Zsqrtd.mk [(Term.hole "_") (Term.hole "_")]) "=" (Term.hole "_"))
        (Term.byTactic'
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Tactic.simp
             "simp"
             []
             []
             []
             ["[" [(Tactic.simpLemma [] [] `div_eq_mul_inv)] "]"]
             [])]))))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.show
       "show"
       («term_=_» (Term.app `Zsqrtd.mk [(Term.hole "_") (Term.hole "_")]) "=" (Term.hole "_"))
       (Term.byTactic'
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.simp
            "simp"
            []
            []
            []
            ["[" [(Tactic.simpLemma [] [] `div_eq_mul_inv)] "]"]
            [])]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic'', expected 'Lean.Parser.Term.fromTerm'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `div_eq_mul_inv)] "]"] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `div_eq_mul_inv
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_» (Term.app `Zsqrtd.mk [(Term.hole "_") (Term.hole "_")]) "=" (Term.hole "_"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app `Zsqrtd.mk [(Term.hole "_") (Term.hole "_")])
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
      `Zsqrtd.mk
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       («term_/_» `x "/" `y)
       "="
       (Term.anonymousCtor
        "⟨"
        [(Term.app
          `round
          [(Term.typeAscription
            "("
            («term_/_»
             (Term.proj («term_*_» `x "*" (Term.app `conj [`y])) "." `re)
             "/"
             (Term.app `norm [`y]))
            ":"
            [(Data.Rat.Init.termℚ "ℚ")]
            ")")])
         ","
         (Term.app
          `round
          [(Term.typeAscription
            "("
            («term_/_»
             (Term.proj («term_*_» `x "*" (Term.app `conj [`y])) "." `im)
             "/"
             (Term.app `norm [`y]))
            ":"
            [(Data.Rat.Init.termℚ "ℚ")]
            ")")])]
        "⟩"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.app
         `round
         [(Term.typeAscription
           "("
           («term_/_»
            (Term.proj («term_*_» `x "*" (Term.app `conj [`y])) "." `re)
            "/"
            (Term.app `norm [`y]))
           ":"
           [(Data.Rat.Init.termℚ "ℚ")]
           ")")])
        ","
        (Term.app
         `round
         [(Term.typeAscription
           "("
           («term_/_»
            (Term.proj («term_*_» `x "*" (Term.app `conj [`y])) "." `im)
            "/"
            (Term.app `norm [`y]))
           ":"
           [(Data.Rat.Init.termℚ "ℚ")]
           ")")])]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `round
       [(Term.typeAscription
         "("
         («term_/_»
          (Term.proj («term_*_» `x "*" (Term.app `conj [`y])) "." `im)
          "/"
          (Term.app `norm [`y]))
         ":"
         [(Data.Rat.Init.termℚ "ℚ")]
         ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription
       "("
       («term_/_»
        (Term.proj («term_*_» `x "*" (Term.app `conj [`y])) "." `im)
        "/"
        (Term.app `norm [`y]))
       ":"
       [(Data.Rat.Init.termℚ "ℚ")]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Rat.Init.termℚ "ℚ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_/_»
       (Term.proj («term_*_» `x "*" (Term.app `conj [`y])) "." `im)
       "/"
       (Term.app `norm [`y]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `norm [`y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `norm
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (Term.proj («term_*_» `x "*" (Term.app `conj [`y])) "." `im)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      («term_*_» `x "*" (Term.app `conj [`y]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `conj [`y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `conj
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 70, (some 71, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_*_» `x "*" (Term.app `conj [`y]))
     ")")
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `round
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `round
       [(Term.typeAscription
         "("
         («term_/_»
          (Term.proj («term_*_» `x "*" (Term.app `conj [`y])) "." `re)
          "/"
          (Term.app `norm [`y]))
         ":"
         [(Data.Rat.Init.termℚ "ℚ")]
         ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription
       "("
       («term_/_»
        (Term.proj («term_*_» `x "*" (Term.app `conj [`y])) "." `re)
        "/"
        (Term.app `norm [`y]))
       ":"
       [(Data.Rat.Init.termℚ "ℚ")]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Rat.Init.termℚ "ℚ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_/_»
       (Term.proj («term_*_» `x "*" (Term.app `conj [`y])) "." `re)
       "/"
       (Term.app `norm [`y]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `norm [`y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `norm
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (Term.proj («term_*_» `x "*" (Term.app `conj [`y])) "." `re)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      («term_*_» `x "*" (Term.app `conj [`y]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `conj [`y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `conj
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 70, (some 71, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_*_» `x "*" (Term.app `conj [`y]))
     ")")
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `round
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      («term_/_» `x "/" `y)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 70, (some 71, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]»', expected 'NumberTheory.Zsqrtd.GaussianInt.termℤ[i]._@.NumberTheory.Zsqrtd.GaussianInt._hyg.6'
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
theorem
  div_def
  ( x y : ℤ[i] )
    : x / y = ⟨ round ( x * conj y . re / norm y : ℚ ) , round ( x * conj y . im / norm y : ℚ ) ⟩
  := show Zsqrtd.mk _ _ = _ by simp [ div_eq_mul_inv ]
#align gaussian_int.div_def GaussianInt.div_def

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `to_complex_div_re [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`x `y]
         [":" (NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.proj
          (Term.typeAscription
           "("
           (Term.typeAscription
            "("
            («term_/_» `x "/" `y)
            ":"
            [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
            ")")
           ":"
           [(Data.Complex.Basic.termℂ "ℂ")]
           ")")
          "."
          `re)
         "="
         (Term.app
          `round
          [(Term.proj
            (Term.typeAscription "(" («term_/_» `x "/" `y) ":" [(Data.Complex.Basic.termℂ "ℂ")] ")")
            "."
            `re)]))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.«tactic_<;>_»
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] `div_def)
               ","
               (Tactic.rwRule
                [(patternIgnore (token.«← » "←"))]
                (Term.app
                 (Term.explicit "@" `Rat.round_cast)
                 [(Data.Real.Basic.termℝ "ℝ") (Term.hole "_") (Term.hole "_")]))]
              "]")
             [])
            "<;>"
            (Tactic.simp
             "simp"
             []
             []
             []
             ["["
              [(Tactic.simpErase "-" `Rat.round_cast)
               ","
               (Tactic.simpLemma [] [] `mul_assoc)
               ","
               (Tactic.simpLemma [] [] `div_eq_mul_inv)
               ","
               (Tactic.simpLemma [] [] `mul_add)
               ","
               (Tactic.simpLemma [] [] `add_mul)]
              "]"]
             []))])))
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
         [(Tactic.«tactic_<;>_»
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [] `div_def)
              ","
              (Tactic.rwRule
               [(patternIgnore (token.«← » "←"))]
               (Term.app
                (Term.explicit "@" `Rat.round_cast)
                [(Data.Real.Basic.termℝ "ℝ") (Term.hole "_") (Term.hole "_")]))]
             "]")
            [])
           "<;>"
           (Tactic.simp
            "simp"
            []
            []
            []
            ["["
             [(Tactic.simpErase "-" `Rat.round_cast)
              ","
              (Tactic.simpLemma [] [] `mul_assoc)
              ","
              (Tactic.simpLemma [] [] `div_eq_mul_inv)
              ","
              (Tactic.simpLemma [] [] `mul_add)
              ","
              (Tactic.simpLemma [] [] `add_mul)]
             "]"]
            []))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.«tactic_<;>_»
       (Tactic.rwSeq
        "rw"
        []
        (Tactic.rwRuleSeq
         "["
         [(Tactic.rwRule [] `div_def)
          ","
          (Tactic.rwRule
           [(patternIgnore (token.«← » "←"))]
           (Term.app
            (Term.explicit "@" `Rat.round_cast)
            [(Data.Real.Basic.termℝ "ℝ") (Term.hole "_") (Term.hole "_")]))]
         "]")
        [])
       "<;>"
       (Tactic.simp
        "simp"
        []
        []
        []
        ["["
         [(Tactic.simpErase "-" `Rat.round_cast)
          ","
          (Tactic.simpLemma [] [] `mul_assoc)
          ","
          (Tactic.simpLemma [] [] `div_eq_mul_inv)
          ","
          (Tactic.simpLemma [] [] `mul_add)
          ","
          (Tactic.simpLemma [] [] `add_mul)]
         "]"]
        []))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       []
       ["["
        [(Tactic.simpErase "-" `Rat.round_cast)
         ","
         (Tactic.simpLemma [] [] `mul_assoc)
         ","
         (Tactic.simpLemma [] [] `div_eq_mul_inv)
         ","
         (Tactic.simpLemma [] [] `mul_add)
         ","
         (Tactic.simpLemma [] [] `add_mul)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `add_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_add
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `div_eq_mul_inv
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_assoc
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpErase', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Rat.round_cast
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 2 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `div_def)
         ","
         (Tactic.rwRule
          [(patternIgnore (token.«← » "←"))]
          (Term.app
           (Term.explicit "@" `Rat.round_cast)
           [(Data.Real.Basic.termℝ "ℝ") (Term.hole "_") (Term.hole "_")]))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.explicit "@" `Rat.round_cast)
       [(Data.Real.Basic.termℝ "ℝ") (Term.hole "_") (Term.hole "_")])
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Basic.termℝ', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Basic.termℝ', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Data.Real.Basic.termℝ "ℝ")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.explicit "@" `Rat.round_cast)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Rat.round_cast
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (some 1024,
     term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `div_def
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.proj
        (Term.typeAscription
         "("
         (Term.typeAscription
          "("
          («term_/_» `x "/" `y)
          ":"
          [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
          ")")
         ":"
         [(Data.Complex.Basic.termℂ "ℂ")]
         ")")
        "."
        `re)
       "="
       (Term.app
        `round
        [(Term.proj
          (Term.typeAscription "(" («term_/_» `x "/" `y) ":" [(Data.Complex.Basic.termℂ "ℂ")] ")")
          "."
          `re)]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `round
       [(Term.proj
         (Term.typeAscription "(" («term_/_» `x "/" `y) ":" [(Data.Complex.Basic.termℂ "ℂ")] ")")
         "."
         `re)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj
       (Term.typeAscription "(" («term_/_» `x "/" `y) ":" [(Data.Complex.Basic.termℂ "ℂ")] ")")
       "."
       `re)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.typeAscription "(" («term_/_» `x "/" `y) ":" [(Data.Complex.Basic.termℂ "ℂ")] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Complex.Basic.termℂ "ℂ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_/_» `x "/" `y)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `round
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.proj
       (Term.typeAscription
        "("
        (Term.typeAscription
         "("
         («term_/_» `x "/" `y)
         ":"
         [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
         ")")
        ":"
        [(Data.Complex.Basic.termℂ "ℂ")]
        ")")
       "."
       `re)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.typeAscription
       "("
       (Term.typeAscription
        "("
        («term_/_» `x "/" `y)
        ":"
        [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
        ")")
       ":"
       [(Data.Complex.Basic.termℂ "ℂ")]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Complex.Basic.termℂ "ℂ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription
       "("
       («term_/_» `x "/" `y)
       ":"
       [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]»', expected 'NumberTheory.Zsqrtd.GaussianInt.termℤ[i]._@.NumberTheory.Zsqrtd.GaussianInt._hyg.6'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  to_complex_div_re
  ( x y : ℤ[i] ) : ( ( x / y : ℤ[i] ) : ℂ ) . re = round ( x / y : ℂ ) . re
  :=
    by
      rw [ div_def , ← @ Rat.round_cast ℝ _ _ ]
        <;>
        simp [ - Rat.round_cast , mul_assoc , div_eq_mul_inv , mul_add , add_mul ]
#align gaussian_int.to_complex_div_re GaussianInt.to_complex_div_re

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `to_complex_div_im [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`x `y]
         [":" (NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.proj
          (Term.typeAscription
           "("
           (Term.typeAscription
            "("
            («term_/_» `x "/" `y)
            ":"
            [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
            ")")
           ":"
           [(Data.Complex.Basic.termℂ "ℂ")]
           ")")
          "."
          `im)
         "="
         (Term.app
          `round
          [(Term.proj
            (Term.typeAscription "(" («term_/_» `x "/" `y) ":" [(Data.Complex.Basic.termℂ "ℂ")] ")")
            "."
            `im)]))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.«tactic_<;>_»
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] `div_def)
               ","
               (Tactic.rwRule
                [(patternIgnore (token.«← » "←"))]
                (Term.app
                 (Term.explicit "@" `Rat.round_cast)
                 [(Data.Real.Basic.termℝ "ℝ") (Term.hole "_") (Term.hole "_")]))
               ","
               (Tactic.rwRule
                [(patternIgnore (token.«← » "←"))]
                (Term.app
                 (Term.explicit "@" `Rat.round_cast)
                 [(Data.Real.Basic.termℝ "ℝ") (Term.hole "_") (Term.hole "_")]))]
              "]")
             [])
            "<;>"
            (Tactic.simp
             "simp"
             []
             []
             []
             ["["
              [(Tactic.simpErase "-" `Rat.round_cast)
               ","
               (Tactic.simpLemma [] [] `mul_assoc)
               ","
               (Tactic.simpLemma [] [] `div_eq_mul_inv)
               ","
               (Tactic.simpLemma [] [] `mul_add)
               ","
               (Tactic.simpLemma [] [] `add_mul)]
              "]"]
             []))])))
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
         [(Tactic.«tactic_<;>_»
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [] `div_def)
              ","
              (Tactic.rwRule
               [(patternIgnore (token.«← » "←"))]
               (Term.app
                (Term.explicit "@" `Rat.round_cast)
                [(Data.Real.Basic.termℝ "ℝ") (Term.hole "_") (Term.hole "_")]))
              ","
              (Tactic.rwRule
               [(patternIgnore (token.«← » "←"))]
               (Term.app
                (Term.explicit "@" `Rat.round_cast)
                [(Data.Real.Basic.termℝ "ℝ") (Term.hole "_") (Term.hole "_")]))]
             "]")
            [])
           "<;>"
           (Tactic.simp
            "simp"
            []
            []
            []
            ["["
             [(Tactic.simpErase "-" `Rat.round_cast)
              ","
              (Tactic.simpLemma [] [] `mul_assoc)
              ","
              (Tactic.simpLemma [] [] `div_eq_mul_inv)
              ","
              (Tactic.simpLemma [] [] `mul_add)
              ","
              (Tactic.simpLemma [] [] `add_mul)]
             "]"]
            []))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.«tactic_<;>_»
       (Tactic.rwSeq
        "rw"
        []
        (Tactic.rwRuleSeq
         "["
         [(Tactic.rwRule [] `div_def)
          ","
          (Tactic.rwRule
           [(patternIgnore (token.«← » "←"))]
           (Term.app
            (Term.explicit "@" `Rat.round_cast)
            [(Data.Real.Basic.termℝ "ℝ") (Term.hole "_") (Term.hole "_")]))
          ","
          (Tactic.rwRule
           [(patternIgnore (token.«← » "←"))]
           (Term.app
            (Term.explicit "@" `Rat.round_cast)
            [(Data.Real.Basic.termℝ "ℝ") (Term.hole "_") (Term.hole "_")]))]
         "]")
        [])
       "<;>"
       (Tactic.simp
        "simp"
        []
        []
        []
        ["["
         [(Tactic.simpErase "-" `Rat.round_cast)
          ","
          (Tactic.simpLemma [] [] `mul_assoc)
          ","
          (Tactic.simpLemma [] [] `div_eq_mul_inv)
          ","
          (Tactic.simpLemma [] [] `mul_add)
          ","
          (Tactic.simpLemma [] [] `add_mul)]
         "]"]
        []))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       []
       ["["
        [(Tactic.simpErase "-" `Rat.round_cast)
         ","
         (Tactic.simpLemma [] [] `mul_assoc)
         ","
         (Tactic.simpLemma [] [] `div_eq_mul_inv)
         ","
         (Tactic.simpLemma [] [] `mul_add)
         ","
         (Tactic.simpLemma [] [] `add_mul)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `add_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_add
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `div_eq_mul_inv
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_assoc
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpErase', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Rat.round_cast
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 2 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `div_def)
         ","
         (Tactic.rwRule
          [(patternIgnore (token.«← » "←"))]
          (Term.app
           (Term.explicit "@" `Rat.round_cast)
           [(Data.Real.Basic.termℝ "ℝ") (Term.hole "_") (Term.hole "_")]))
         ","
         (Tactic.rwRule
          [(patternIgnore (token.«← » "←"))]
          (Term.app
           (Term.explicit "@" `Rat.round_cast)
           [(Data.Real.Basic.termℝ "ℝ") (Term.hole "_") (Term.hole "_")]))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.explicit "@" `Rat.round_cast)
       [(Data.Real.Basic.termℝ "ℝ") (Term.hole "_") (Term.hole "_")])
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Basic.termℝ', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Basic.termℝ', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Data.Real.Basic.termℝ "ℝ")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.explicit "@" `Rat.round_cast)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Rat.round_cast
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (some 1024,
     term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.explicit "@" `Rat.round_cast)
       [(Data.Real.Basic.termℝ "ℝ") (Term.hole "_") (Term.hole "_")])
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Basic.termℝ', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Basic.termℝ', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Data.Real.Basic.termℝ "ℝ")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.explicit "@" `Rat.round_cast)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Rat.round_cast
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (some 1024,
     term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `div_def
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.proj
        (Term.typeAscription
         "("
         (Term.typeAscription
          "("
          («term_/_» `x "/" `y)
          ":"
          [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
          ")")
         ":"
         [(Data.Complex.Basic.termℂ "ℂ")]
         ")")
        "."
        `im)
       "="
       (Term.app
        `round
        [(Term.proj
          (Term.typeAscription "(" («term_/_» `x "/" `y) ":" [(Data.Complex.Basic.termℂ "ℂ")] ")")
          "."
          `im)]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `round
       [(Term.proj
         (Term.typeAscription "(" («term_/_» `x "/" `y) ":" [(Data.Complex.Basic.termℂ "ℂ")] ")")
         "."
         `im)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj
       (Term.typeAscription "(" («term_/_» `x "/" `y) ":" [(Data.Complex.Basic.termℂ "ℂ")] ")")
       "."
       `im)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.typeAscription "(" («term_/_» `x "/" `y) ":" [(Data.Complex.Basic.termℂ "ℂ")] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Complex.Basic.termℂ "ℂ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_/_» `x "/" `y)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `round
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.proj
       (Term.typeAscription
        "("
        (Term.typeAscription
         "("
         («term_/_» `x "/" `y)
         ":"
         [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
         ")")
        ":"
        [(Data.Complex.Basic.termℂ "ℂ")]
        ")")
       "."
       `im)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.typeAscription
       "("
       (Term.typeAscription
        "("
        («term_/_» `x "/" `y)
        ":"
        [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
        ")")
       ":"
       [(Data.Complex.Basic.termℂ "ℂ")]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Complex.Basic.termℂ "ℂ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription
       "("
       («term_/_» `x "/" `y)
       ":"
       [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]»', expected 'NumberTheory.Zsqrtd.GaussianInt.termℤ[i]._@.NumberTheory.Zsqrtd.GaussianInt._hyg.6'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  to_complex_div_im
  ( x y : ℤ[i] ) : ( ( x / y : ℤ[i] ) : ℂ ) . im = round ( x / y : ℂ ) . im
  :=
    by
      rw [ div_def , ← @ Rat.round_cast ℝ _ _ , ← @ Rat.round_cast ℝ _ _ ]
        <;>
        simp [ - Rat.round_cast , mul_assoc , div_eq_mul_inv , mul_add , add_mul ]
#align gaussian_int.to_complex_div_im GaussianInt.to_complex_div_im

theorem norm_sq_le_norm_sq_of_re_le_of_im_le {x y : ℂ} (hre : |x.re| ≤ |y.re|)
    (him : |x.im| ≤ |y.im|) : x.normSq ≤ y.normSq := by
  rw [norm_sq_apply, norm_sq_apply, ← _root_.abs_mul_self, _root_.abs_mul, ←
      _root_.abs_mul_self y.re, _root_.abs_mul y.re, ← _root_.abs_mul_self x.im,
      _root_.abs_mul x.im, ← _root_.abs_mul_self y.im, _root_.abs_mul y.im] <;>
    exact
      add_le_add (mul_self_le_mul_self (abs_nonneg _) hre) (mul_self_le_mul_self (abs_nonneg _) him)
#align
  gaussian_int.norm_sq_le_norm_sq_of_re_le_of_im_le GaussianInt.norm_sq_le_norm_sq_of_re_le_of_im_le

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `norm_sq_div_sub_div_lt_one [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`x `y]
         [":" (NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_<_»
         (Term.proj
          («term_-_»
           (Term.typeAscription "(" («term_/_» `x "/" `y) ":" [(Data.Complex.Basic.termℂ "ℂ")] ")")
           "-"
           (Term.typeAscription
            "("
            (Term.typeAscription
             "("
             («term_/_» `x "/" `y)
             ":"
             [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
             ")")
            ":"
            [(Data.Complex.Basic.termℂ "ℂ")]
            ")"))
          "."
          `normSq)
         "<"
         (num "1"))))
      (Command.declValSimple
       ":="
       (calc
        "calc"
        (calcStep
         («term_=_»
          (Term.proj
           («term_-_»
            (Term.typeAscription "(" («term_/_» `x "/" `y) ":" [(Data.Complex.Basic.termℂ "ℂ")] ")")
            "-"
            (Term.typeAscription
             "("
             (Term.typeAscription
              "("
              («term_/_» `x "/" `y)
              ":"
              [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
              ")")
             ":"
             [(Data.Complex.Basic.termℂ "ℂ")]
             ")"))
           "."
           `normSq)
          "="
          (Term.proj
           (Term.typeAscription
            "("
            («term_+_»
             («term_-_»
              (Term.proj
               (Term.typeAscription
                "("
                («term_/_» `x "/" `y)
                ":"
                [(Data.Complex.Basic.termℂ "ℂ")]
                ")")
               "."
               `re)
              "-"
              (Term.proj
               (Term.typeAscription
                "("
                (Term.typeAscription
                 "("
                 («term_/_» `x "/" `y)
                 ":"
                 [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
                 ")")
                ":"
                [(Data.Complex.Basic.termℂ "ℂ")]
                ")")
               "."
               `re))
             "+"
             («term_*_»
              («term_-_»
               (Term.proj
                (Term.typeAscription
                 "("
                 («term_/_» `x "/" `y)
                 ":"
                 [(Data.Complex.Basic.termℂ "ℂ")]
                 ")")
                "."
                `im)
               "-"
               (Term.proj
                (Term.typeAscription
                 "("
                 (Term.typeAscription
                  "("
                  («term_/_» `x "/" `y)
                  ":"
                  [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
                  ")")
                 ":"
                 [(Data.Complex.Basic.termℂ "ℂ")]
                 ")")
                "."
                `im))
              "*"
              `I))
            ":"
            [(Data.Complex.Basic.termℂ "ℂ")]
            ")")
           "."
           `normSq))
         ":="
         («term_<|_»
          (Term.app `congr_arg [(Term.hole "_")])
          "<|"
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(Tactic.«tactic_<;>_»
               (Tactic.apply "apply" `Complex.ext)
               "<;>"
               (Tactic.simp "simp" [] [] [] [] []))])))))
        [(calcStep
          («term_≤_»
           (Term.hole "_")
           "≤"
           (Term.proj
            («term_+_»
             («term_/_» (num "1") "/" (num "2"))
             "+"
             («term_*_» («term_/_» (num "1") "/" (num "2")) "*" `I))
            "."
            `normSq))
          ":="
          (Term.have
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             []
             [(Term.typeSpec
               ":"
               («term_=_»
                («term|___|»
                 (group "|")
                 (Term.typeAscription
                  "("
                  («term_⁻¹» (num "2") "⁻¹")
                  ":"
                  [(Data.Real.Basic.termℝ "ℝ")]
                  ")")
                 (group)
                 "|")
                "="
                («term_⁻¹» (num "2") "⁻¹")))]
             ":="
             (Term.app
              `abs_of_nonneg
              [(Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented [(Mathlib.Tactic.normNum "norm_num" [] [] [])])))])))
           []
           (Term.app
            `norm_sq_le_norm_sq_of_re_le_of_im_le
            [(Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.«tactic_<;>_»
                  (Tactic.«tactic_<;>_»
                   (Tactic.rwSeq
                    "rw"
                    []
                    (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `to_complex_div_re)] "]")
                    [])
                   "<;>"
                   (Tactic.simp
                    "simp"
                    []
                    []
                    []
                    ["[" [(Tactic.simpLemma [] [] `norm_sq) "," (Tactic.simpLemma [] [] `this)] "]"]
                    []))
                  "<;>"
                  (Std.Tactic.Simpa.simpa
                   "simpa"
                   []
                   []
                   (Std.Tactic.Simpa.simpaArgsRest
                    []
                    []
                    []
                    []
                    ["using"
                     (Term.app
                      `abs_sub_round
                      [(Term.proj
                        (Term.typeAscription
                         "("
                         («term_/_» `x "/" `y)
                         ":"
                         [(Data.Complex.Basic.termℂ "ℂ")]
                         ")")
                        "."
                        `re)])])))])))
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.«tactic_<;>_»
                  (Tactic.«tactic_<;>_»
                   (Tactic.rwSeq
                    "rw"
                    []
                    (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `to_complex_div_im)] "]")
                    [])
                   "<;>"
                   (Tactic.simp
                    "simp"
                    []
                    []
                    []
                    ["[" [(Tactic.simpLemma [] [] `norm_sq) "," (Tactic.simpLemma [] [] `this)] "]"]
                    []))
                  "<;>"
                  (Std.Tactic.Simpa.simpa
                   "simpa"
                   []
                   []
                   (Std.Tactic.Simpa.simpaArgsRest
                    []
                    []
                    []
                    []
                    ["using"
                     (Term.app
                      `abs_sub_round
                      [(Term.proj
                        (Term.typeAscription
                         "("
                         («term_/_» `x "/" `y)
                         ":"
                         [(Data.Complex.Basic.termℂ "ℂ")]
                         ")")
                        "."
                        `im)])])))])))])))
         (calcStep
          («term_<_» (Term.hole "_") "<" (num "1"))
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(Tactic.«tactic_<;>_»
               (Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `norm_sq)] "]"] [])
               "<;>"
               (Mathlib.Tactic.normNum "norm_num" [] [] []))]))))])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (calc
       "calc"
       (calcStep
        («term_=_»
         (Term.proj
          («term_-_»
           (Term.typeAscription "(" («term_/_» `x "/" `y) ":" [(Data.Complex.Basic.termℂ "ℂ")] ")")
           "-"
           (Term.typeAscription
            "("
            (Term.typeAscription
             "("
             («term_/_» `x "/" `y)
             ":"
             [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
             ")")
            ":"
            [(Data.Complex.Basic.termℂ "ℂ")]
            ")"))
          "."
          `normSq)
         "="
         (Term.proj
          (Term.typeAscription
           "("
           («term_+_»
            («term_-_»
             (Term.proj
              (Term.typeAscription
               "("
               («term_/_» `x "/" `y)
               ":"
               [(Data.Complex.Basic.termℂ "ℂ")]
               ")")
              "."
              `re)
             "-"
             (Term.proj
              (Term.typeAscription
               "("
               (Term.typeAscription
                "("
                («term_/_» `x "/" `y)
                ":"
                [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
                ")")
               ":"
               [(Data.Complex.Basic.termℂ "ℂ")]
               ")")
              "."
              `re))
            "+"
            («term_*_»
             («term_-_»
              (Term.proj
               (Term.typeAscription
                "("
                («term_/_» `x "/" `y)
                ":"
                [(Data.Complex.Basic.termℂ "ℂ")]
                ")")
               "."
               `im)
              "-"
              (Term.proj
               (Term.typeAscription
                "("
                (Term.typeAscription
                 "("
                 («term_/_» `x "/" `y)
                 ":"
                 [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
                 ")")
                ":"
                [(Data.Complex.Basic.termℂ "ℂ")]
                ")")
               "."
               `im))
             "*"
             `I))
           ":"
           [(Data.Complex.Basic.termℂ "ℂ")]
           ")")
          "."
          `normSq))
        ":="
        («term_<|_»
         (Term.app `congr_arg [(Term.hole "_")])
         "<|"
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.«tactic_<;>_»
              (Tactic.apply "apply" `Complex.ext)
              "<;>"
              (Tactic.simp "simp" [] [] [] [] []))])))))
       [(calcStep
         («term_≤_»
          (Term.hole "_")
          "≤"
          (Term.proj
           («term_+_»
            («term_/_» (num "1") "/" (num "2"))
            "+"
            («term_*_» («term_/_» (num "1") "/" (num "2")) "*" `I))
           "."
           `normSq))
         ":="
         (Term.have
          "have"
          (Term.haveDecl
           (Term.haveIdDecl
            []
            [(Term.typeSpec
              ":"
              («term_=_»
               («term|___|»
                (group "|")
                (Term.typeAscription
                 "("
                 («term_⁻¹» (num "2") "⁻¹")
                 ":"
                 [(Data.Real.Basic.termℝ "ℝ")]
                 ")")
                (group)
                "|")
               "="
               («term_⁻¹» (num "2") "⁻¹")))]
            ":="
            (Term.app
             `abs_of_nonneg
             [(Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented [(Mathlib.Tactic.normNum "norm_num" [] [] [])])))])))
          []
          (Term.app
           `norm_sq_le_norm_sq_of_re_le_of_im_le
           [(Term.byTactic
             "by"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(Tactic.«tactic_<;>_»
                 (Tactic.«tactic_<;>_»
                  (Tactic.rwSeq
                   "rw"
                   []
                   (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `to_complex_div_re)] "]")
                   [])
                  "<;>"
                  (Tactic.simp
                   "simp"
                   []
                   []
                   []
                   ["[" [(Tactic.simpLemma [] [] `norm_sq) "," (Tactic.simpLemma [] [] `this)] "]"]
                   []))
                 "<;>"
                 (Std.Tactic.Simpa.simpa
                  "simpa"
                  []
                  []
                  (Std.Tactic.Simpa.simpaArgsRest
                   []
                   []
                   []
                   []
                   ["using"
                    (Term.app
                     `abs_sub_round
                     [(Term.proj
                       (Term.typeAscription
                        "("
                        («term_/_» `x "/" `y)
                        ":"
                        [(Data.Complex.Basic.termℂ "ℂ")]
                        ")")
                       "."
                       `re)])])))])))
            (Term.byTactic
             "by"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(Tactic.«tactic_<;>_»
                 (Tactic.«tactic_<;>_»
                  (Tactic.rwSeq
                   "rw"
                   []
                   (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `to_complex_div_im)] "]")
                   [])
                  "<;>"
                  (Tactic.simp
                   "simp"
                   []
                   []
                   []
                   ["[" [(Tactic.simpLemma [] [] `norm_sq) "," (Tactic.simpLemma [] [] `this)] "]"]
                   []))
                 "<;>"
                 (Std.Tactic.Simpa.simpa
                  "simpa"
                  []
                  []
                  (Std.Tactic.Simpa.simpaArgsRest
                   []
                   []
                   []
                   []
                   ["using"
                    (Term.app
                     `abs_sub_round
                     [(Term.proj
                       (Term.typeAscription
                        "("
                        («term_/_» `x "/" `y)
                        ":"
                        [(Data.Complex.Basic.termℂ "ℂ")]
                        ")")
                       "."
                       `im)])])))])))])))
        (calcStep
         («term_<_» (Term.hole "_") "<" (num "1"))
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.«tactic_<;>_»
              (Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `norm_sq)] "]"] [])
              "<;>"
              (Mathlib.Tactic.normNum "norm_num" [] [] []))]))))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.«tactic_<;>_»
           (Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `norm_sq)] "]"] [])
           "<;>"
           (Mathlib.Tactic.normNum "norm_num" [] [] []))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.«tactic_<;>_»
       (Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `norm_sq)] "]"] [])
       "<;>"
       (Mathlib.Tactic.normNum "norm_num" [] [] []))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.normNum "norm_num" [] [] [])
[PrettyPrinter.parenthesize] ...precedences are 2 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
      (Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `norm_sq)] "]"] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `norm_sq
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<_» (Term.hole "_") "<" (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
      (Term.have
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         []
         [(Term.typeSpec
           ":"
           («term_=_»
            («term|___|»
             (group "|")
             (Term.typeAscription
              "("
              («term_⁻¹» (num "2") "⁻¹")
              ":"
              [(Data.Real.Basic.termℝ "ℝ")]
              ")")
             (group)
             "|")
            "="
            («term_⁻¹» (num "2") "⁻¹")))]
         ":="
         (Term.app
          `abs_of_nonneg
          [(Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented [(Mathlib.Tactic.normNum "norm_num" [] [] [])])))])))
       []
       (Term.app
        `norm_sq_le_norm_sq_of_re_le_of_im_le
        [(Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.«tactic_<;>_»
              (Tactic.«tactic_<;>_»
               (Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `to_complex_div_re)] "]")
                [])
               "<;>"
               (Tactic.simp
                "simp"
                []
                []
                []
                ["[" [(Tactic.simpLemma [] [] `norm_sq) "," (Tactic.simpLemma [] [] `this)] "]"]
                []))
              "<;>"
              (Std.Tactic.Simpa.simpa
               "simpa"
               []
               []
               (Std.Tactic.Simpa.simpaArgsRest
                []
                []
                []
                []
                ["using"
                 (Term.app
                  `abs_sub_round
                  [(Term.proj
                    (Term.typeAscription
                     "("
                     («term_/_» `x "/" `y)
                     ":"
                     [(Data.Complex.Basic.termℂ "ℂ")]
                     ")")
                    "."
                    `re)])])))])))
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.«tactic_<;>_»
              (Tactic.«tactic_<;>_»
               (Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `to_complex_div_im)] "]")
                [])
               "<;>"
               (Tactic.simp
                "simp"
                []
                []
                []
                ["[" [(Tactic.simpLemma [] [] `norm_sq) "," (Tactic.simpLemma [] [] `this)] "]"]
                []))
              "<;>"
              (Std.Tactic.Simpa.simpa
               "simpa"
               []
               []
               (Std.Tactic.Simpa.simpaArgsRest
                []
                []
                []
                []
                ["using"
                 (Term.app
                  `abs_sub_round
                  [(Term.proj
                    (Term.typeAscription
                     "("
                     («term_/_» `x "/" `y)
                     ":"
                     [(Data.Complex.Basic.termℂ "ℂ")]
                     ")")
                    "."
                    `im)])])))])))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `norm_sq_le_norm_sq_of_re_le_of_im_le
       [(Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Tactic.«tactic_<;>_»
             (Tactic.«tactic_<;>_»
              (Tactic.rwSeq
               "rw"
               []
               (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `to_complex_div_re)] "]")
               [])
              "<;>"
              (Tactic.simp
               "simp"
               []
               []
               []
               ["[" [(Tactic.simpLemma [] [] `norm_sq) "," (Tactic.simpLemma [] [] `this)] "]"]
               []))
             "<;>"
             (Std.Tactic.Simpa.simpa
              "simpa"
              []
              []
              (Std.Tactic.Simpa.simpaArgsRest
               []
               []
               []
               []
               ["using"
                (Term.app
                 `abs_sub_round
                 [(Term.proj
                   (Term.typeAscription
                    "("
                    («term_/_» `x "/" `y)
                    ":"
                    [(Data.Complex.Basic.termℂ "ℂ")]
                    ")")
                   "."
                   `re)])])))])))
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Tactic.«tactic_<;>_»
             (Tactic.«tactic_<;>_»
              (Tactic.rwSeq
               "rw"
               []
               (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `to_complex_div_im)] "]")
               [])
              "<;>"
              (Tactic.simp
               "simp"
               []
               []
               []
               ["[" [(Tactic.simpLemma [] [] `norm_sq) "," (Tactic.simpLemma [] [] `this)] "]"]
               []))
             "<;>"
             (Std.Tactic.Simpa.simpa
              "simpa"
              []
              []
              (Std.Tactic.Simpa.simpaArgsRest
               []
               []
               []
               []
               ["using"
                (Term.app
                 `abs_sub_round
                 [(Term.proj
                   (Term.typeAscription
                    "("
                    («term_/_» `x "/" `y)
                    ":"
                    [(Data.Complex.Basic.termℂ "ℂ")]
                    ")")
                   "."
                   `im)])])))])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.«tactic_<;>_»
           (Tactic.«tactic_<;>_»
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `to_complex_div_im)] "]")
             [])
            "<;>"
            (Tactic.simp
             "simp"
             []
             []
             []
             ["[" [(Tactic.simpLemma [] [] `norm_sq) "," (Tactic.simpLemma [] [] `this)] "]"]
             []))
           "<;>"
           (Std.Tactic.Simpa.simpa
            "simpa"
            []
            []
            (Std.Tactic.Simpa.simpaArgsRest
             []
             []
             []
             []
             ["using"
              (Term.app
               `abs_sub_round
               [(Term.proj
                 (Term.typeAscription
                  "("
                  («term_/_» `x "/" `y)
                  ":"
                  [(Data.Complex.Basic.termℂ "ℂ")]
                  ")")
                 "."
                 `im)])])))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.«tactic_<;>_»
       (Tactic.«tactic_<;>_»
        (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `to_complex_div_im)] "]") [])
        "<;>"
        (Tactic.simp
         "simp"
         []
         []
         []
         ["[" [(Tactic.simpLemma [] [] `norm_sq) "," (Tactic.simpLemma [] [] `this)] "]"]
         []))
       "<;>"
       (Std.Tactic.Simpa.simpa
        "simpa"
        []
        []
        (Std.Tactic.Simpa.simpaArgsRest
         []
         []
         []
         []
         ["using"
          (Term.app
           `abs_sub_round
           [(Term.proj
             (Term.typeAscription
              "("
              («term_/_» `x "/" `y)
              ":"
              [(Data.Complex.Basic.termℂ "ℂ")]
              ")")
             "."
             `im)])])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Simpa.simpa
       "simpa"
       []
       []
       (Std.Tactic.Simpa.simpaArgsRest
        []
        []
        []
        []
        ["using"
         (Term.app
          `abs_sub_round
          [(Term.proj
            (Term.typeAscription "(" («term_/_» `x "/" `y) ":" [(Data.Complex.Basic.termℂ "ℂ")] ")")
            "."
            `im)])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `abs_sub_round
       [(Term.proj
         (Term.typeAscription "(" («term_/_» `x "/" `y) ":" [(Data.Complex.Basic.termℂ "ℂ")] ")")
         "."
         `im)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj
       (Term.typeAscription "(" («term_/_» `x "/" `y) ":" [(Data.Complex.Basic.termℂ "ℂ")] ")")
       "."
       `im)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.typeAscription "(" («term_/_» `x "/" `y) ":" [(Data.Complex.Basic.termℂ "ℂ")] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Complex.Basic.termℂ "ℂ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_/_» `x "/" `y)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `abs_sub_round
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 2 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
      (Tactic.«tactic_<;>_»
       (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `to_complex_div_im)] "]") [])
       "<;>"
       (Tactic.simp
        "simp"
        []
        []
        []
        ["[" [(Tactic.simpLemma [] [] `norm_sq) "," (Tactic.simpLemma [] [] `this)] "]"]
        []))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       []
       ["[" [(Tactic.simpLemma [] [] `norm_sq) "," (Tactic.simpLemma [] [] `this)] "]"]
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
      `norm_sq
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 2 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
      (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `to_complex_div_im)] "]") [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `to_complex_div_im
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0,
     tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(Tactic.«tactic_<;>_»
          (Tactic.«tactic_<;>_»
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `to_complex_div_im)] "]")
            [])
           "<;>"
           (Tactic.simp
            "simp"
            []
            []
            []
            ["[" [(Tactic.simpLemma [] [] `norm_sq) "," (Tactic.simpLemma [] [] `this)] "]"]
            []))
          "<;>"
          (Std.Tactic.Simpa.simpa
           "simpa"
           []
           []
           (Std.Tactic.Simpa.simpaArgsRest
            []
            []
            []
            []
            ["using"
             (Term.app
              `abs_sub_round
              [(Term.proj
                (Term.typeAscription
                 "("
                 («term_/_» `x "/" `y)
                 ":"
                 [(Data.Complex.Basic.termℂ "ℂ")]
                 ")")
                "."
                `im)])])))])))
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.«tactic_<;>_»
           (Tactic.«tactic_<;>_»
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `to_complex_div_re)] "]")
             [])
            "<;>"
            (Tactic.simp
             "simp"
             []
             []
             []
             ["[" [(Tactic.simpLemma [] [] `norm_sq) "," (Tactic.simpLemma [] [] `this)] "]"]
             []))
           "<;>"
           (Std.Tactic.Simpa.simpa
            "simpa"
            []
            []
            (Std.Tactic.Simpa.simpaArgsRest
             []
             []
             []
             []
             ["using"
              (Term.app
               `abs_sub_round
               [(Term.proj
                 (Term.typeAscription
                  "("
                  («term_/_» `x "/" `y)
                  ":"
                  [(Data.Complex.Basic.termℂ "ℂ")]
                  ")")
                 "."
                 `re)])])))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.«tactic_<;>_»
       (Tactic.«tactic_<;>_»
        (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `to_complex_div_re)] "]") [])
        "<;>"
        (Tactic.simp
         "simp"
         []
         []
         []
         ["[" [(Tactic.simpLemma [] [] `norm_sq) "," (Tactic.simpLemma [] [] `this)] "]"]
         []))
       "<;>"
       (Std.Tactic.Simpa.simpa
        "simpa"
        []
        []
        (Std.Tactic.Simpa.simpaArgsRest
         []
         []
         []
         []
         ["using"
          (Term.app
           `abs_sub_round
           [(Term.proj
             (Term.typeAscription
              "("
              («term_/_» `x "/" `y)
              ":"
              [(Data.Complex.Basic.termℂ "ℂ")]
              ")")
             "."
             `re)])])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Simpa.simpa
       "simpa"
       []
       []
       (Std.Tactic.Simpa.simpaArgsRest
        []
        []
        []
        []
        ["using"
         (Term.app
          `abs_sub_round
          [(Term.proj
            (Term.typeAscription "(" («term_/_» `x "/" `y) ":" [(Data.Complex.Basic.termℂ "ℂ")] ")")
            "."
            `re)])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `abs_sub_round
       [(Term.proj
         (Term.typeAscription "(" («term_/_» `x "/" `y) ":" [(Data.Complex.Basic.termℂ "ℂ")] ")")
         "."
         `re)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj
       (Term.typeAscription "(" («term_/_» `x "/" `y) ":" [(Data.Complex.Basic.termℂ "ℂ")] ")")
       "."
       `re)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.typeAscription "(" («term_/_» `x "/" `y) ":" [(Data.Complex.Basic.termℂ "ℂ")] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Complex.Basic.termℂ "ℂ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_/_» `x "/" `y)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `abs_sub_round
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 2 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
      (Tactic.«tactic_<;>_»
       (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `to_complex_div_re)] "]") [])
       "<;>"
       (Tactic.simp
        "simp"
        []
        []
        []
        ["[" [(Tactic.simpLemma [] [] `norm_sq) "," (Tactic.simpLemma [] [] `this)] "]"]
        []))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       []
       ["[" [(Tactic.simpLemma [] [] `norm_sq) "," (Tactic.simpLemma [] [] `this)] "]"]
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
      `norm_sq
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 2 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
      (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `to_complex_div_re)] "]") [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `to_complex_div_re
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, tactic) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(Tactic.«tactic_<;>_»
          (Tactic.«tactic_<;>_»
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `to_complex_div_re)] "]")
            [])
           "<;>"
           (Tactic.simp
            "simp"
            []
            []
            []
            ["[" [(Tactic.simpLemma [] [] `norm_sq) "," (Tactic.simpLemma [] [] `this)] "]"]
            []))
          "<;>"
          (Std.Tactic.Simpa.simpa
           "simpa"
           []
           []
           (Std.Tactic.Simpa.simpaArgsRest
            []
            []
            []
            []
            ["using"
             (Term.app
              `abs_sub_round
              [(Term.proj
                (Term.typeAscription
                 "("
                 («term_/_» `x "/" `y)
                 ":"
                 [(Data.Complex.Basic.termℂ "ℂ")]
                 ")")
                "."
                `re)])])))])))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `norm_sq_le_norm_sq_of_re_le_of_im_le
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `abs_of_nonneg
       [(Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented [(Mathlib.Tactic.normNum "norm_num" [] [] [])])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented [(Mathlib.Tactic.normNum "norm_num" [] [] [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.normNum "norm_num" [] [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0,
     tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.byTactic
      "by"
      (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Mathlib.Tactic.normNum "norm_num" [] [] [])])))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `abs_of_nonneg
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       («term|___|»
        (group "|")
        (Term.typeAscription "(" («term_⁻¹» (num "2") "⁻¹") ":" [(Data.Real.Basic.termℝ "ℝ")] ")")
        (group)
        "|")
       "="
       («term_⁻¹» (num "2") "⁻¹"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_⁻¹» (num "2") "⁻¹")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      («term|___|»
       (group "|")
       (Term.typeAscription "(" («term_⁻¹» (num "2") "⁻¹") ":" [(Data.Real.Basic.termℝ "ℝ")] ")")
       (group)
       "|")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription "(" («term_⁻¹» (num "2") "⁻¹") ":" [(Data.Real.Basic.termℝ "ℝ")] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Real.Basic.termℝ "ℝ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_⁻¹» (num "2") "⁻¹")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≤_»
       (Term.hole "_")
       "≤"
       (Term.proj
        («term_+_»
         («term_/_» (num "1") "/" (num "2"))
         "+"
         («term_*_» («term_/_» (num "1") "/" (num "2")) "*" `I))
        "."
        `normSq))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj
       («term_+_»
        («term_/_» (num "1") "/" (num "2"))
        "+"
        («term_*_» («term_/_» (num "1") "/" (num "2")) "*" `I))
       "."
       `normSq)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      («term_+_»
       («term_/_» (num "1") "/" (num "2"))
       "+"
       («term_*_» («term_/_» (num "1") "/" (num "2")) "*" `I))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_» («term_/_» (num "1") "/" (num "2")) "*" `I)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `I
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      («term_/_» (num "1") "/" (num "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 70, (some 71, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      («term_/_» (num "1") "/" (num "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 65 >? 70, (some 71, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 65, (some 66, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_+_»
      («term_/_» (num "1") "/" (num "2"))
      "+"
      («term_*_» («term_/_» (num "1") "/" (num "2")) "*" `I))
     ")")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
      («term_<|_»
       (Term.app `congr_arg [(Term.hole "_")])
       "<|"
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.«tactic_<;>_»
            (Tactic.apply "apply" `Complex.ext)
            "<;>"
            (Tactic.simp "simp" [] [] [] [] []))]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.«tactic_<;>_»
           (Tactic.apply "apply" `Complex.ext)
           "<;>"
           (Tactic.simp "simp" [] [] [] [] []))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.«tactic_<;>_»
       (Tactic.apply "apply" `Complex.ext)
       "<;>"
       (Tactic.simp "simp" [] [] [] [] []))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] [] [] [])
[PrettyPrinter.parenthesize] ...precedences are 2 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
      (Tactic.apply "apply" `Complex.ext)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Complex.ext
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      (Term.app `congr_arg [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `congr_arg
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 0, term) <=? (none, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Term.proj
        («term_-_»
         (Term.typeAscription "(" («term_/_» `x "/" `y) ":" [(Data.Complex.Basic.termℂ "ℂ")] ")")
         "-"
         (Term.typeAscription
          "("
          (Term.typeAscription
           "("
           («term_/_» `x "/" `y)
           ":"
           [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
           ")")
          ":"
          [(Data.Complex.Basic.termℂ "ℂ")]
          ")"))
        "."
        `normSq)
       "="
       (Term.proj
        (Term.typeAscription
         "("
         («term_+_»
          («term_-_»
           (Term.proj
            (Term.typeAscription "(" («term_/_» `x "/" `y) ":" [(Data.Complex.Basic.termℂ "ℂ")] ")")
            "."
            `re)
           "-"
           (Term.proj
            (Term.typeAscription
             "("
             (Term.typeAscription
              "("
              («term_/_» `x "/" `y)
              ":"
              [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
              ")")
             ":"
             [(Data.Complex.Basic.termℂ "ℂ")]
             ")")
            "."
            `re))
          "+"
          («term_*_»
           («term_-_»
            (Term.proj
             (Term.typeAscription
              "("
              («term_/_» `x "/" `y)
              ":"
              [(Data.Complex.Basic.termℂ "ℂ")]
              ")")
             "."
             `im)
            "-"
            (Term.proj
             (Term.typeAscription
              "("
              (Term.typeAscription
               "("
               («term_/_» `x "/" `y)
               ":"
               [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
               ")")
              ":"
              [(Data.Complex.Basic.termℂ "ℂ")]
              ")")
             "."
             `im))
           "*"
           `I))
         ":"
         [(Data.Complex.Basic.termℂ "ℂ")]
         ")")
        "."
        `normSq))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj
       (Term.typeAscription
        "("
        («term_+_»
         («term_-_»
          (Term.proj
           (Term.typeAscription "(" («term_/_» `x "/" `y) ":" [(Data.Complex.Basic.termℂ "ℂ")] ")")
           "."
           `re)
          "-"
          (Term.proj
           (Term.typeAscription
            "("
            (Term.typeAscription
             "("
             («term_/_» `x "/" `y)
             ":"
             [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
             ")")
            ":"
            [(Data.Complex.Basic.termℂ "ℂ")]
            ")")
           "."
           `re))
         "+"
         («term_*_»
          («term_-_»
           (Term.proj
            (Term.typeAscription "(" («term_/_» `x "/" `y) ":" [(Data.Complex.Basic.termℂ "ℂ")] ")")
            "."
            `im)
           "-"
           (Term.proj
            (Term.typeAscription
             "("
             (Term.typeAscription
              "("
              («term_/_» `x "/" `y)
              ":"
              [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
              ")")
             ":"
             [(Data.Complex.Basic.termℂ "ℂ")]
             ")")
            "."
            `im))
          "*"
          `I))
        ":"
        [(Data.Complex.Basic.termℂ "ℂ")]
        ")")
       "."
       `normSq)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.typeAscription
       "("
       («term_+_»
        («term_-_»
         (Term.proj
          (Term.typeAscription "(" («term_/_» `x "/" `y) ":" [(Data.Complex.Basic.termℂ "ℂ")] ")")
          "."
          `re)
         "-"
         (Term.proj
          (Term.typeAscription
           "("
           (Term.typeAscription
            "("
            («term_/_» `x "/" `y)
            ":"
            [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
            ")")
           ":"
           [(Data.Complex.Basic.termℂ "ℂ")]
           ")")
          "."
          `re))
        "+"
        («term_*_»
         («term_-_»
          (Term.proj
           (Term.typeAscription "(" («term_/_» `x "/" `y) ":" [(Data.Complex.Basic.termℂ "ℂ")] ")")
           "."
           `im)
          "-"
          (Term.proj
           (Term.typeAscription
            "("
            (Term.typeAscription
             "("
             («term_/_» `x "/" `y)
             ":"
             [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
             ")")
            ":"
            [(Data.Complex.Basic.termℂ "ℂ")]
            ")")
           "."
           `im))
         "*"
         `I))
       ":"
       [(Data.Complex.Basic.termℂ "ℂ")]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Complex.Basic.termℂ "ℂ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_»
       («term_-_»
        (Term.proj
         (Term.typeAscription "(" («term_/_» `x "/" `y) ":" [(Data.Complex.Basic.termℂ "ℂ")] ")")
         "."
         `re)
        "-"
        (Term.proj
         (Term.typeAscription
          "("
          (Term.typeAscription
           "("
           («term_/_» `x "/" `y)
           ":"
           [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
           ")")
          ":"
          [(Data.Complex.Basic.termℂ "ℂ")]
          ")")
         "."
         `re))
       "+"
       («term_*_»
        («term_-_»
         (Term.proj
          (Term.typeAscription "(" («term_/_» `x "/" `y) ":" [(Data.Complex.Basic.termℂ "ℂ")] ")")
          "."
          `im)
         "-"
         (Term.proj
          (Term.typeAscription
           "("
           (Term.typeAscription
            "("
            («term_/_» `x "/" `y)
            ":"
            [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
            ")")
           ":"
           [(Data.Complex.Basic.termℂ "ℂ")]
           ")")
          "."
          `im))
        "*"
        `I))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_»
       («term_-_»
        (Term.proj
         (Term.typeAscription "(" («term_/_» `x "/" `y) ":" [(Data.Complex.Basic.termℂ "ℂ")] ")")
         "."
         `im)
        "-"
        (Term.proj
         (Term.typeAscription
          "("
          (Term.typeAscription
           "("
           («term_/_» `x "/" `y)
           ":"
           [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
           ")")
          ":"
          [(Data.Complex.Basic.termℂ "ℂ")]
          ")")
         "."
         `im))
       "*"
       `I)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `I
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      («term_-_»
       (Term.proj
        (Term.typeAscription "(" («term_/_» `x "/" `y) ":" [(Data.Complex.Basic.termℂ "ℂ")] ")")
        "."
        `im)
       "-"
       (Term.proj
        (Term.typeAscription
         "("
         (Term.typeAscription
          "("
          («term_/_» `x "/" `y)
          ":"
          [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
          ")")
         ":"
         [(Data.Complex.Basic.termℂ "ℂ")]
         ")")
        "."
        `im))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj
       (Term.typeAscription
        "("
        (Term.typeAscription
         "("
         («term_/_» `x "/" `y)
         ":"
         [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
         ")")
        ":"
        [(Data.Complex.Basic.termℂ "ℂ")]
        ")")
       "."
       `im)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.typeAscription
       "("
       (Term.typeAscription
        "("
        («term_/_» `x "/" `y)
        ":"
        [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
        ")")
       ":"
       [(Data.Complex.Basic.termℂ "ℂ")]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Complex.Basic.termℂ "ℂ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription
       "("
       («term_/_» `x "/" `y)
       ":"
       [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]»', expected 'NumberTheory.Zsqrtd.GaussianInt.termℤ[i]._@.NumberTheory.Zsqrtd.GaussianInt._hyg.6'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  norm_sq_div_sub_div_lt_one
  ( x y : ℤ[i] ) : ( x / y : ℂ ) - ( ( x / y : ℤ[i] ) : ℂ ) . normSq < 1
  :=
    calc
      ( x / y : ℂ ) - ( ( x / y : ℤ[i] ) : ℂ ) . normSq
          =
          (
              ( x / y : ℂ ) . re - ( ( x / y : ℤ[i] ) : ℂ ) . re
                +
                ( x / y : ℂ ) . im - ( ( x / y : ℤ[i] ) : ℂ ) . im * I
              :
              ℂ
              )
            .
            normSq
        :=
        congr_arg _ <| by apply Complex.ext <;> simp
      _ ≤ 1 / 2 + 1 / 2 * I . normSq
          :=
          have
            : | ( 2 ⁻¹ : ℝ ) | = 2 ⁻¹ := abs_of_nonneg by norm_num
            norm_sq_le_norm_sq_of_re_le_of_im_le
              by
                  rw [ to_complex_div_re ] <;> simp [ norm_sq , this ]
                    <;>
                    simpa using abs_sub_round ( x / y : ℂ ) . re
                by
                  rw [ to_complex_div_im ] <;> simp [ norm_sq , this ]
                    <;>
                    simpa using abs_sub_round ( x / y : ℂ ) . im
        _ < 1 := by simp [ norm_sq ] <;> norm_num
#align gaussian_int.norm_sq_div_sub_div_lt_one GaussianInt.norm_sq_div_sub_div_lt_one

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
       (Term.typeSpec ":" (Term.app `Mod [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")])))
      (Command.declValSimple
       ":="
       (Term.anonymousCtor
        "⟨"
        [(Term.fun
          "fun"
          (Term.basicFun
           [`x `y]
           []
           "=>"
           («term_-_» `x "-" («term_*_» `y "*" («term_/_» `x "/" `y)))))]
        "⟩")
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.fun
         "fun"
         (Term.basicFun
          [`x `y]
          []
          "=>"
          («term_-_» `x "-" («term_*_» `y "*" («term_/_» `x "/" `y)))))]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun [`x `y] [] "=>" («term_-_» `x "-" («term_*_» `y "*" («term_/_» `x "/" `y)))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_-_» `x "-" («term_*_» `y "*" («term_/_» `x "/" `y)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_» `y "*" («term_/_» `x "/" `y))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_/_» `x "/" `y)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_/_» `x "/" `y) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `y
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app `Mod [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]»', expected 'NumberTheory.Zsqrtd.GaussianInt.termℤ[i]._@.NumberTheory.Zsqrtd.GaussianInt._hyg.6'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
instance : Mod ℤ[i] := ⟨ fun x y => x - y * x / y ⟩

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `mod_def [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`x `y]
         [":" (NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         («term_%_» `x "%" `y)
         "="
         («term_-_» `x "-" («term_*_» `y "*" («term_/_» `x "/" `y))))))
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
       («term_%_» `x "%" `y)
       "="
       («term_-_» `x "-" («term_*_» `y "*" («term_/_» `x "/" `y))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_-_» `x "-" («term_*_» `y "*" («term_/_» `x "/" `y)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_» `y "*" («term_/_» `x "/" `y))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_/_» `x "/" `y)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_/_» `x "/" `y) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `y
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      («term_%_» `x "%" `y)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 70, (some 71, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]»', expected 'NumberTheory.Zsqrtd.GaussianInt.termℤ[i]._@.NumberTheory.Zsqrtd.GaussianInt._hyg.6'
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
theorem mod_def ( x y : ℤ[i] ) : x % y = x - y * x / y := rfl
#align gaussian_int.mod_def GaussianInt.mod_def

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `norm_mod_lt [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`x]
         [":" (NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
         []
         ")")
        (Term.implicitBinder "{" [`y] [":" (NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")] "}")
        (Term.explicitBinder "(" [`hy] [":" («term_≠_» `y "≠" (num "0"))] [] ")")]
       (Term.typeSpec
        ":"
        («term_<_» (Term.proj («term_%_» `x "%" `y) "." `norm) "<" (Term.proj `y "." `norm))))
      (Command.declValSimple
       ":="
       (Term.have
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          []
          [(Term.typeSpec
            ":"
            («term_≠_»
             (Term.typeAscription "(" `y ":" [(Data.Complex.Basic.termℂ "ℂ")] ")")
             "≠"
             (num "0")))]
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(Std.Tactic.tacticRwa__
               "rwa"
               (Tactic.rwRuleSeq
                "["
                [(Tactic.rwRule [] `Ne.def)
                 ","
                 (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `to_complex_zero)
                 ","
                 (Tactic.rwRule [] `to_complex_inj)]
                "]")
               [])])))))
        []
        («term_<|_»
         (Term.proj
          (Term.app
           (Term.explicit "@" `Int.cast_lt)
           [(Data.Real.Basic.termℝ "ℝ")
            (Term.hole "_")
            (Term.hole "_")
            (Term.hole "_")
            (Term.hole "_")])
          "."
          (fieldIdx "1"))
         "<|"
         (calc
          "calc"
          (calcStep
           («term_=_»
            (coeNotation "↑" (Term.app `Zsqrtd.norm [(«term_%_» `x "%" `y)]))
            "="
            (Term.proj
             (Term.typeAscription
              "("
              («term_-_»
               `x
               "-"
               («term_*_»
                `y
                "*"
                (Term.typeAscription
                 "("
                 («term_/_» `x "/" `y)
                 ":"
                 [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
                 ")")))
              ":"
              [(Data.Complex.Basic.termℂ "ℂ")]
              ")")
             "."
             `normSq))
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `mod_def)] "]"] [])]))))
          [(calcStep
            («term_=_»
             (Term.hole "_")
             "="
             («term_*_»
              (Term.proj
               (Term.typeAscription "(" `y ":" [(Data.Complex.Basic.termℂ "ℂ")] ")")
               "."
               `normSq)
              "*"
              (Term.proj
               (Term.typeAscription
                "("
                («term_-_»
                 («term_/_» `x "/" `y)
                 "-"
                 (Term.typeAscription
                  "("
                  («term_/_» `x "/" `y)
                  ":"
                  [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
                  ")"))
                ":"
                [(Data.Complex.Basic.termℂ "ℂ")]
                ")")
               "."
               `normSq)))
            ":="
            (Term.byTactic
             "by"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(Tactic.rwSeq
                 "rw"
                 []
                 (Tactic.rwRuleSeq
                  "["
                  [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `norm_sq_mul)
                   ","
                   (Tactic.rwRule [] `mul_sub)
                   ","
                   (Tactic.rwRule [] (Term.app `mul_div_cancel' [(Term.hole "_") `this]))]
                  "]")
                 [])]))))
           (calcStep
            («term_<_»
             (Term.hole "_")
             "<"
             («term_*_»
              (Term.proj
               (Term.typeAscription "(" `y ":" [(Data.Complex.Basic.termℂ "ℂ")] ")")
               "."
               `normSq)
              "*"
              (num "1")))
            ":="
            (Term.app
             `mul_lt_mul_of_pos_left
             [(Term.app `norm_sq_div_sub_div_lt_one [(Term.hole "_") (Term.hole "_")])
              (Term.app (Term.proj `norm_sq_pos "." (fieldIdx "2")) [`this])]))
           (calcStep
            («term_=_» (Term.hole "_") "=" (Term.app `Zsqrtd.norm [`y]))
            ":="
            (Term.byTactic
             "by"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])]))))])))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.have
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         []
         [(Term.typeSpec
           ":"
           («term_≠_»
            (Term.typeAscription "(" `y ":" [(Data.Complex.Basic.termℂ "ℂ")] ")")
            "≠"
            (num "0")))]
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Std.Tactic.tacticRwa__
              "rwa"
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [] `Ne.def)
                ","
                (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `to_complex_zero)
                ","
                (Tactic.rwRule [] `to_complex_inj)]
               "]")
              [])])))))
       []
       («term_<|_»
        (Term.proj
         (Term.app
          (Term.explicit "@" `Int.cast_lt)
          [(Data.Real.Basic.termℝ "ℝ")
           (Term.hole "_")
           (Term.hole "_")
           (Term.hole "_")
           (Term.hole "_")])
         "."
         (fieldIdx "1"))
        "<|"
        (calc
         "calc"
         (calcStep
          («term_=_»
           (coeNotation "↑" (Term.app `Zsqrtd.norm [(«term_%_» `x "%" `y)]))
           "="
           (Term.proj
            (Term.typeAscription
             "("
             («term_-_»
              `x
              "-"
              («term_*_»
               `y
               "*"
               (Term.typeAscription
                "("
                («term_/_» `x "/" `y)
                ":"
                [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
                ")")))
             ":"
             [(Data.Complex.Basic.termℂ "ℂ")]
             ")")
            "."
            `normSq))
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `mod_def)] "]"] [])]))))
         [(calcStep
           («term_=_»
            (Term.hole "_")
            "="
            («term_*_»
             (Term.proj
              (Term.typeAscription "(" `y ":" [(Data.Complex.Basic.termℂ "ℂ")] ")")
              "."
              `normSq)
             "*"
             (Term.proj
              (Term.typeAscription
               "("
               («term_-_»
                («term_/_» `x "/" `y)
                "-"
                (Term.typeAscription
                 "("
                 («term_/_» `x "/" `y)
                 ":"
                 [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
                 ")"))
               ":"
               [(Data.Complex.Basic.termℂ "ℂ")]
               ")")
              "."
              `normSq)))
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `norm_sq_mul)
                  ","
                  (Tactic.rwRule [] `mul_sub)
                  ","
                  (Tactic.rwRule [] (Term.app `mul_div_cancel' [(Term.hole "_") `this]))]
                 "]")
                [])]))))
          (calcStep
           («term_<_»
            (Term.hole "_")
            "<"
            («term_*_»
             (Term.proj
              (Term.typeAscription "(" `y ":" [(Data.Complex.Basic.termℂ "ℂ")] ")")
              "."
              `normSq)
             "*"
             (num "1")))
           ":="
           (Term.app
            `mul_lt_mul_of_pos_left
            [(Term.app `norm_sq_div_sub_div_lt_one [(Term.hole "_") (Term.hole "_")])
             (Term.app (Term.proj `norm_sq_pos "." (fieldIdx "2")) [`this])]))
          (calcStep
           («term_=_» (Term.hole "_") "=" (Term.app `Zsqrtd.norm [`y]))
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])]))))])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_»
       (Term.proj
        (Term.app
         (Term.explicit "@" `Int.cast_lt)
         [(Data.Real.Basic.termℝ "ℝ")
          (Term.hole "_")
          (Term.hole "_")
          (Term.hole "_")
          (Term.hole "_")])
        "."
        (fieldIdx "1"))
       "<|"
       (calc
        "calc"
        (calcStep
         («term_=_»
          (coeNotation "↑" (Term.app `Zsqrtd.norm [(«term_%_» `x "%" `y)]))
          "="
          (Term.proj
           (Term.typeAscription
            "("
            («term_-_»
             `x
             "-"
             («term_*_»
              `y
              "*"
              (Term.typeAscription
               "("
               («term_/_» `x "/" `y)
               ":"
               [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
               ")")))
            ":"
            [(Data.Complex.Basic.termℂ "ℂ")]
            ")")
           "."
           `normSq))
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `mod_def)] "]"] [])]))))
        [(calcStep
          («term_=_»
           (Term.hole "_")
           "="
           («term_*_»
            (Term.proj
             (Term.typeAscription "(" `y ":" [(Data.Complex.Basic.termℂ "ℂ")] ")")
             "."
             `normSq)
            "*"
            (Term.proj
             (Term.typeAscription
              "("
              («term_-_»
               («term_/_» `x "/" `y)
               "-"
               (Term.typeAscription
                "("
                («term_/_» `x "/" `y)
                ":"
                [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
                ")"))
              ":"
              [(Data.Complex.Basic.termℂ "ℂ")]
              ")")
             "."
             `normSq)))
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(Tactic.rwSeq
               "rw"
               []
               (Tactic.rwRuleSeq
                "["
                [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `norm_sq_mul)
                 ","
                 (Tactic.rwRule [] `mul_sub)
                 ","
                 (Tactic.rwRule [] (Term.app `mul_div_cancel' [(Term.hole "_") `this]))]
                "]")
               [])]))))
         (calcStep
          («term_<_»
           (Term.hole "_")
           "<"
           («term_*_»
            (Term.proj
             (Term.typeAscription "(" `y ":" [(Data.Complex.Basic.termℂ "ℂ")] ")")
             "."
             `normSq)
            "*"
            (num "1")))
          ":="
          (Term.app
           `mul_lt_mul_of_pos_left
           [(Term.app `norm_sq_div_sub_div_lt_one [(Term.hole "_") (Term.hole "_")])
            (Term.app (Term.proj `norm_sq_pos "." (fieldIdx "2")) [`this])]))
         (calcStep
          («term_=_» (Term.hole "_") "=" (Term.app `Zsqrtd.norm [`y]))
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])]))))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (calc
       "calc"
       (calcStep
        («term_=_»
         (coeNotation "↑" (Term.app `Zsqrtd.norm [(«term_%_» `x "%" `y)]))
         "="
         (Term.proj
          (Term.typeAscription
           "("
           («term_-_»
            `x
            "-"
            («term_*_»
             `y
             "*"
             (Term.typeAscription
              "("
              («term_/_» `x "/" `y)
              ":"
              [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
              ")")))
           ":"
           [(Data.Complex.Basic.termℂ "ℂ")]
           ")")
          "."
          `normSq))
        ":="
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `mod_def)] "]"] [])]))))
       [(calcStep
         («term_=_»
          (Term.hole "_")
          "="
          («term_*_»
           (Term.proj
            (Term.typeAscription "(" `y ":" [(Data.Complex.Basic.termℂ "ℂ")] ")")
            "."
            `normSq)
           "*"
           (Term.proj
            (Term.typeAscription
             "("
             («term_-_»
              («term_/_» `x "/" `y)
              "-"
              (Term.typeAscription
               "("
               («term_/_» `x "/" `y)
               ":"
               [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
               ")"))
             ":"
             [(Data.Complex.Basic.termℂ "ℂ")]
             ")")
            "."
            `normSq)))
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `norm_sq_mul)
                ","
                (Tactic.rwRule [] `mul_sub)
                ","
                (Tactic.rwRule [] (Term.app `mul_div_cancel' [(Term.hole "_") `this]))]
               "]")
              [])]))))
        (calcStep
         («term_<_»
          (Term.hole "_")
          "<"
          («term_*_»
           (Term.proj
            (Term.typeAscription "(" `y ":" [(Data.Complex.Basic.termℂ "ℂ")] ")")
            "."
            `normSq)
           "*"
           (num "1")))
         ":="
         (Term.app
          `mul_lt_mul_of_pos_left
          [(Term.app `norm_sq_div_sub_div_lt_one [(Term.hole "_") (Term.hole "_")])
           (Term.app (Term.proj `norm_sq_pos "." (fieldIdx "2")) [`this])]))
        (calcStep
         («term_=_» (Term.hole "_") "=" (Term.app `Zsqrtd.norm [`y]))
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])]))))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] [] [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_» (Term.hole "_") "=" (Term.app `Zsqrtd.norm [`y]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Zsqrtd.norm [`y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Zsqrtd.norm
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
      (Term.app
       `mul_lt_mul_of_pos_left
       [(Term.app `norm_sq_div_sub_div_lt_one [(Term.hole "_") (Term.hole "_")])
        (Term.app (Term.proj `norm_sq_pos "." (fieldIdx "2")) [`this])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj `norm_sq_pos "." (fieldIdx "2")) [`this])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `this
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `norm_sq_pos "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `norm_sq_pos
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.proj `norm_sq_pos "." (fieldIdx "2")) [`this])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `norm_sq_div_sub_div_lt_one [(Term.hole "_") (Term.hole "_")])
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
      `norm_sq_div_sub_div_lt_one
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `norm_sq_div_sub_div_lt_one [(Term.hole "_") (Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `mul_lt_mul_of_pos_left
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<_»
       (Term.hole "_")
       "<"
       («term_*_»
        (Term.proj
         (Term.typeAscription "(" `y ":" [(Data.Complex.Basic.termℂ "ℂ")] ")")
         "."
         `normSq)
        "*"
        (num "1")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_»
       (Term.proj (Term.typeAscription "(" `y ":" [(Data.Complex.Basic.termℂ "ℂ")] ")") "." `normSq)
       "*"
       (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (Term.proj (Term.typeAscription "(" `y ":" [(Data.Complex.Basic.termℂ "ℂ")] ")") "." `normSq)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.typeAscription "(" `y ":" [(Data.Complex.Basic.termℂ "ℂ")] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Complex.Basic.termℂ "ℂ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `norm_sq_mul)
             ","
             (Tactic.rwRule [] `mul_sub)
             ","
             (Tactic.rwRule [] (Term.app `mul_div_cancel' [(Term.hole "_") `this]))]
            "]")
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `norm_sq_mul)
         ","
         (Tactic.rwRule [] `mul_sub)
         ","
         (Tactic.rwRule [] (Term.app `mul_div_cancel' [(Term.hole "_") `this]))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `mul_div_cancel' [(Term.hole "_") `this])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `this
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `mul_div_cancel'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_sub
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `norm_sq_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Term.hole "_")
       "="
       («term_*_»
        (Term.proj
         (Term.typeAscription "(" `y ":" [(Data.Complex.Basic.termℂ "ℂ")] ")")
         "."
         `normSq)
        "*"
        (Term.proj
         (Term.typeAscription
          "("
          («term_-_»
           («term_/_» `x "/" `y)
           "-"
           (Term.typeAscription
            "("
            («term_/_» `x "/" `y)
            ":"
            [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
            ")"))
          ":"
          [(Data.Complex.Basic.termℂ "ℂ")]
          ")")
         "."
         `normSq)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_»
       (Term.proj (Term.typeAscription "(" `y ":" [(Data.Complex.Basic.termℂ "ℂ")] ")") "." `normSq)
       "*"
       (Term.proj
        (Term.typeAscription
         "("
         («term_-_»
          («term_/_» `x "/" `y)
          "-"
          (Term.typeAscription
           "("
           («term_/_» `x "/" `y)
           ":"
           [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
           ")"))
         ":"
         [(Data.Complex.Basic.termℂ "ℂ")]
         ")")
        "."
        `normSq))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj
       (Term.typeAscription
        "("
        («term_-_»
         («term_/_» `x "/" `y)
         "-"
         (Term.typeAscription
          "("
          («term_/_» `x "/" `y)
          ":"
          [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
          ")"))
        ":"
        [(Data.Complex.Basic.termℂ "ℂ")]
        ")")
       "."
       `normSq)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.typeAscription
       "("
       («term_-_»
        («term_/_» `x "/" `y)
        "-"
        (Term.typeAscription
         "("
         («term_/_» `x "/" `y)
         ":"
         [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
         ")"))
       ":"
       [(Data.Complex.Basic.termℂ "ℂ")]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Complex.Basic.termℂ "ℂ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_-_»
       («term_/_» `x "/" `y)
       "-"
       (Term.typeAscription
        "("
        («term_/_» `x "/" `y)
        ":"
        [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
        ")"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription
       "("
       («term_/_» `x "/" `y)
       ":"
       [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]»', expected 'NumberTheory.Zsqrtd.GaussianInt.termℤ[i]._@.NumberTheory.Zsqrtd.GaussianInt._hyg.6'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  norm_mod_lt
  ( x : ℤ[i] ) { y : ℤ[i] } ( hy : y ≠ 0 ) : x % y . norm < y . norm
  :=
    have
      : ( y : ℂ ) ≠ 0 := by rwa [ Ne.def , ← to_complex_zero , to_complex_inj ]
      @ Int.cast_lt ℝ _ _ _ _ . 1
        <|
        calc
          ↑ Zsqrtd.norm x % y = ( x - y * ( x / y : ℤ[i] ) : ℂ ) . normSq := by simp [ mod_def ]
          _ = ( y : ℂ ) . normSq * ( x / y - ( x / y : ℤ[i] ) : ℂ ) . normSq
              :=
              by rw [ ← norm_sq_mul , mul_sub , mul_div_cancel' _ this ]
            _ < ( y : ℂ ) . normSq * 1
              :=
              mul_lt_mul_of_pos_left norm_sq_div_sub_div_lt_one _ _ norm_sq_pos . 2 this
            _ = Zsqrtd.norm y := by simp
#align gaussian_int.norm_mod_lt GaussianInt.norm_mod_lt

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `nat_abs_norm_mod_lt [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`x]
         [":" (NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
         []
         ")")
        (Term.implicitBinder "{" [`y] [":" (NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")] "}")
        (Term.explicitBinder "(" [`hy] [":" («term_≠_» `y "≠" (num "0"))] [] ")")]
       (Term.typeSpec
        ":"
        («term_<_»
         (Term.proj (Term.proj («term_%_» `x "%" `y) "." `norm) "." `natAbs)
         "<"
         (Term.proj (Term.proj `y "." `norm) "." `natAbs))))
      (Command.declValSimple
       ":="
       (Term.app
        (Term.proj `Int.ofNat_lt "." (fieldIdx "1"))
        [(Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.simp
              "simp"
              []
              []
              []
              ["["
               [(Tactic.simpErase "-" `Int.ofNat_lt)
                ","
                (Tactic.simpLemma [] [] (Term.app `norm_mod_lt [`x `hy]))]
               "]"]
              [])])))])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj `Int.ofNat_lt "." (fieldIdx "1"))
       [(Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Tactic.simp
             "simp"
             []
             []
             []
             ["["
              [(Tactic.simpErase "-" `Int.ofNat_lt)
               ","
               (Tactic.simpLemma [] [] (Term.app `norm_mod_lt [`x `hy]))]
              "]"]
             [])])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.simp
           "simp"
           []
           []
           []
           ["["
            [(Tactic.simpErase "-" `Int.ofNat_lt)
             ","
             (Tactic.simpLemma [] [] (Term.app `norm_mod_lt [`x `hy]))]
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
        [(Tactic.simpErase "-" `Int.ofNat_lt)
         ","
         (Tactic.simpLemma [] [] (Term.app `norm_mod_lt [`x `hy]))]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `norm_mod_lt [`x `hy])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hy
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `norm_mod_lt
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpErase', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Int.ofNat_lt
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0,
     tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(Tactic.simp
          "simp"
          []
          []
          []
          ["["
           [(Tactic.simpErase "-" `Int.ofNat_lt)
            ","
            (Tactic.simpLemma [] [] (Term.app `norm_mod_lt [`x `hy]))]
           "]"]
          [])])))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `Int.ofNat_lt "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `Int.ofNat_lt
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_<_»
       (Term.proj (Term.proj («term_%_» `x "%" `y) "." `norm) "." `natAbs)
       "<"
       (Term.proj (Term.proj `y "." `norm) "." `natAbs))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.proj `y "." `norm) "." `natAbs)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj `y "." `norm)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `y
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.proj (Term.proj («term_%_» `x "%" `y) "." `norm) "." `natAbs)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj («term_%_» `x "%" `y) "." `norm)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      («term_%_» `x "%" `y)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 70, (some 71, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_%_» `x "%" `y) ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≠_» `y "≠" (num "0"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `y
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.implicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.implicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.implicitBinder', expected 'Lean.Parser.Term.explicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.implicitBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]»', expected 'NumberTheory.Zsqrtd.GaussianInt.termℤ[i]._@.NumberTheory.Zsqrtd.GaussianInt._hyg.6'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.implicitBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  nat_abs_norm_mod_lt
  ( x : ℤ[i] ) { y : ℤ[i] } ( hy : y ≠ 0 ) : x % y . norm . natAbs < y . norm . natAbs
  := Int.ofNat_lt . 1 by simp [ - Int.ofNat_lt , norm_mod_lt x hy ]
#align gaussian_int.nat_abs_norm_mod_lt GaussianInt.nat_abs_norm_mod_lt

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `norm_le_norm_mul_left [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`x]
         [":" (NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
         []
         ")")
        (Term.implicitBinder "{" [`y] [":" (NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")] "}")
        (Term.explicitBinder "(" [`hy] [":" («term_≠_» `y "≠" (num "0"))] [] ")")]
       (Term.typeSpec
        ":"
        («term_≤_»
         (Term.proj (Term.app `norm [`x]) "." `natAbs)
         "≤"
         (Term.proj (Term.app `norm [(«term_*_» `x "*" `y)]) "." `natAbs))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.«tactic_<;>_»
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] `Zsqrtd.norm_mul) "," (Tactic.rwRule [] `Int.natAbs_mul)]
              "]")
             [])
            "<;>"
            (Tactic.exact
             "exact"
             (Term.app
              `le_mul_of_one_le_right
              [(Term.app `Nat.zero_le [(Term.hole "_")])
               (Term.app
                (Term.proj `Int.ofNat_le "." (fieldIdx "1"))
                [(Term.byTactic
                  "by"
                  (Tactic.tacticSeq
                   (Tactic.tacticSeq1Indented
                    [(Tactic.«tactic_<;>_»
                      (Tactic.rwSeq
                       "rw"
                       []
                       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `coe_nat_abs_norm)] "]")
                       [])
                      "<;>"
                      (Tactic.exact
                       "exact"
                       (Term.app
                        `Int.add_one_le_of_lt
                        [(Term.app (Term.proj `norm_pos "." (fieldIdx "2")) [`hy])])))])))])])))])))
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
         [(Tactic.«tactic_<;>_»
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [] `Zsqrtd.norm_mul) "," (Tactic.rwRule [] `Int.natAbs_mul)]
             "]")
            [])
           "<;>"
           (Tactic.exact
            "exact"
            (Term.app
             `le_mul_of_one_le_right
             [(Term.app `Nat.zero_le [(Term.hole "_")])
              (Term.app
               (Term.proj `Int.ofNat_le "." (fieldIdx "1"))
               [(Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(Tactic.«tactic_<;>_»
                     (Tactic.rwSeq
                      "rw"
                      []
                      (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `coe_nat_abs_norm)] "]")
                      [])
                     "<;>"
                     (Tactic.exact
                      "exact"
                      (Term.app
                       `Int.add_one_le_of_lt
                       [(Term.app (Term.proj `norm_pos "." (fieldIdx "2")) [`hy])])))])))])])))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.«tactic_<;>_»
       (Tactic.rwSeq
        "rw"
        []
        (Tactic.rwRuleSeq
         "["
         [(Tactic.rwRule [] `Zsqrtd.norm_mul) "," (Tactic.rwRule [] `Int.natAbs_mul)]
         "]")
        [])
       "<;>"
       (Tactic.exact
        "exact"
        (Term.app
         `le_mul_of_one_le_right
         [(Term.app `Nat.zero_le [(Term.hole "_")])
          (Term.app
           (Term.proj `Int.ofNat_le "." (fieldIdx "1"))
           [(Term.byTactic
             "by"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(Tactic.«tactic_<;>_»
                 (Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `coe_nat_abs_norm)] "]")
                  [])
                 "<;>"
                 (Tactic.exact
                  "exact"
                  (Term.app
                   `Int.add_one_le_of_lt
                   [(Term.app (Term.proj `norm_pos "." (fieldIdx "2")) [`hy])])))])))])])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.app
        `le_mul_of_one_le_right
        [(Term.app `Nat.zero_le [(Term.hole "_")])
         (Term.app
          (Term.proj `Int.ofNat_le "." (fieldIdx "1"))
          [(Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.«tactic_<;>_»
                (Tactic.rwSeq
                 "rw"
                 []
                 (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `coe_nat_abs_norm)] "]")
                 [])
                "<;>"
                (Tactic.exact
                 "exact"
                 (Term.app
                  `Int.add_one_le_of_lt
                  [(Term.app (Term.proj `norm_pos "." (fieldIdx "2")) [`hy])])))])))])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `le_mul_of_one_le_right
       [(Term.app `Nat.zero_le [(Term.hole "_")])
        (Term.app
         (Term.proj `Int.ofNat_le "." (fieldIdx "1"))
         [(Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(Tactic.«tactic_<;>_»
               (Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `coe_nat_abs_norm)] "]")
                [])
               "<;>"
               (Tactic.exact
                "exact"
                (Term.app
                 `Int.add_one_le_of_lt
                 [(Term.app (Term.proj `norm_pos "." (fieldIdx "2")) [`hy])])))])))])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj `Int.ofNat_le "." (fieldIdx "1"))
       [(Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Tactic.«tactic_<;>_»
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `coe_nat_abs_norm)] "]")
              [])
             "<;>"
             (Tactic.exact
              "exact"
              (Term.app
               `Int.add_one_le_of_lt
               [(Term.app (Term.proj `norm_pos "." (fieldIdx "2")) [`hy])])))])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.«tactic_<;>_»
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `coe_nat_abs_norm)] "]")
            [])
           "<;>"
           (Tactic.exact
            "exact"
            (Term.app
             `Int.add_one_le_of_lt
             [(Term.app (Term.proj `norm_pos "." (fieldIdx "2")) [`hy])])))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.«tactic_<;>_»
       (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `coe_nat_abs_norm)] "]") [])
       "<;>"
       (Tactic.exact
        "exact"
        (Term.app
         `Int.add_one_le_of_lt
         [(Term.app (Term.proj `norm_pos "." (fieldIdx "2")) [`hy])])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.app `Int.add_one_le_of_lt [(Term.app (Term.proj `norm_pos "." (fieldIdx "2")) [`hy])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Int.add_one_le_of_lt [(Term.app (Term.proj `norm_pos "." (fieldIdx "2")) [`hy])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj `norm_pos "." (fieldIdx "2")) [`hy])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hy
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `norm_pos "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `norm_pos
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.proj `norm_pos "." (fieldIdx "2")) [`hy])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Int.add_one_le_of_lt
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 2 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
      (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `coe_nat_abs_norm)] "]") [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `coe_nat_abs_norm
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0,
     tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(Tactic.«tactic_<;>_»
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `coe_nat_abs_norm)] "]")
           [])
          "<;>"
          (Tactic.exact
           "exact"
           (Term.app
            `Int.add_one_le_of_lt
            [(Term.paren "(" (Term.app (Term.proj `norm_pos "." (fieldIdx "2")) [`hy]) ")")])))])))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `Int.ofNat_le "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `Int.ofNat_le
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      (Term.proj `Int.ofNat_le "." (fieldIdx "1"))
      [(Term.paren
        "("
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Tactic.«tactic_<;>_»
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `coe_nat_abs_norm)] "]")
              [])
             "<;>"
             (Tactic.exact
              "exact"
              (Term.app
               `Int.add_one_le_of_lt
               [(Term.paren
                 "("
                 (Term.app (Term.proj `norm_pos "." (fieldIdx "2")) [`hy])
                 ")")])))])))
        ")")])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `Nat.zero_le [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Nat.zero_le
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `Nat.zero_le [(Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `le_mul_of_one_le_right
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 2 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `Zsqrtd.norm_mul) "," (Tactic.rwRule [] `Int.natAbs_mul)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Int.natAbs_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Zsqrtd.norm_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_≤_»
       (Term.proj (Term.app `norm [`x]) "." `natAbs)
       "≤"
       (Term.proj (Term.app `norm [(«term_*_» `x "*" `y)]) "." `natAbs))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.app `norm [(«term_*_» `x "*" `y)]) "." `natAbs)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `norm [(«term_*_» `x "*" `y)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_*_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_*_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_» `x "*" `y)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_*_» `x "*" `y) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `norm
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `norm [(Term.paren "(" («term_*_» `x "*" `y) ")")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.proj (Term.app `norm [`x]) "." `natAbs)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `norm [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `norm
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `norm [`x]) ")")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≠_» `y "≠" (num "0"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `y
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.implicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.implicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.implicitBinder', expected 'Lean.Parser.Term.explicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.implicitBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]»', expected 'NumberTheory.Zsqrtd.GaussianInt.termℤ[i]._@.NumberTheory.Zsqrtd.GaussianInt._hyg.6'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.implicitBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  norm_le_norm_mul_left
  ( x : ℤ[i] ) { y : ℤ[i] } ( hy : y ≠ 0 ) : norm x . natAbs ≤ norm x * y . natAbs
  :=
    by
      rw [ Zsqrtd.norm_mul , Int.natAbs_mul ]
        <;>
        exact
          le_mul_of_one_le_right
            Nat.zero_le _
              Int.ofNat_le . 1
                by rw [ coe_nat_abs_norm ] <;> exact Int.add_one_le_of_lt norm_pos . 2 hy
#align gaussian_int.norm_le_norm_mul_left GaussianInt.norm_le_norm_mul_left

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
        (Term.app `Nontrivial [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")])))
      (Command.declValSimple
       ":="
       (Term.anonymousCtor
        "⟨"
        [(Term.anonymousCtor
          "⟨"
          [(num "0")
           ","
           (num "1")
           ","
           (Term.byTactic
            "by"
            (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.decide "decide")])))]
          "⟩")]
        "⟩")
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.anonymousCtor
         "⟨"
         [(num "0")
          ","
          (num "1")
          ","
          (Term.byTactic
           "by"
           (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.decide "decide")])))]
         "⟩")]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(num "0")
        ","
        (num "1")
        ","
        (Term.byTactic
         "by"
         (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.decide "decide")])))]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.decide "decide")])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.decide "decide")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app `Nontrivial [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]»', expected 'NumberTheory.Zsqrtd.GaussianInt.termℤ[i]._@.NumberTheory.Zsqrtd.GaussianInt._hyg.6'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
instance : Nontrivial ℤ[i] := ⟨ ⟨ 0 , 1 , by decide ⟩ ⟩

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
        (Term.app `EuclideanDomain [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")])))
      (Command.declValSimple
       ":="
       (Term.structInst
        "{"
        [[`GaussianInt.commRing "," `GaussianInt.nontrivial] "with"]
        [(Term.structInstField
          (Term.structInstLVal `Quotient [])
          ":="
          (Term.paren "(" («term_/_» (Term.cdot "·") "/" (Term.cdot "·")) ")"))
         []
         (Term.structInstField
          (Term.structInstLVal `remainder [])
          ":="
          (Term.paren "(" («term_%_» (Term.cdot "·") "%" (Term.cdot "·")) ")"))
         []
         (Term.structInstField
          (Term.structInstLVal `quotient_zero [])
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `div_def)] "]"] [])
              []
              (Tactic.tacticRfl "rfl")]))))
         []
         (Term.structInstField
          (Term.structInstLVal `quotient_mul_add_remainder_eq [])
          ":="
          (Term.fun
           "fun"
           (Term.basicFun
            [(Term.hole "_") (Term.hole "_")]
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
                 []
                 ["[" [(Tactic.simpLemma [] [] `mod_def)] "]"]
                 [])]))))))
         []
         (Term.structInstField (Term.structInstLVal `R []) ":=" (Term.hole "_"))
         []
         (Term.structInstField
          (Term.structInstLVal `r_well_founded [])
          ":="
          (Term.app `measure_wf [(«term_∘_» `Int.natAbs "∘" `norm)]))
         []
         (Term.structInstField (Term.structInstLVal `remainder_lt []) ":=" `nat_abs_norm_mod_lt)
         []
         (Term.structInstField
          (Term.structInstLVal `mul_left_not_lt [])
          ":="
          (Term.fun
           "fun"
           (Term.basicFun
            [`a `b `hb0]
            []
            "=>"
            («term_<|_» `not_lt_of_ge "<|" (Term.app `norm_le_norm_mul_left [`a `hb0])))))]
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
       [[`GaussianInt.commRing "," `GaussianInt.nontrivial] "with"]
       [(Term.structInstField
         (Term.structInstLVal `Quotient [])
         ":="
         (Term.paren "(" («term_/_» (Term.cdot "·") "/" (Term.cdot "·")) ")"))
        []
        (Term.structInstField
         (Term.structInstLVal `remainder [])
         ":="
         (Term.paren "(" («term_%_» (Term.cdot "·") "%" (Term.cdot "·")) ")"))
        []
        (Term.structInstField
         (Term.structInstLVal `quotient_zero [])
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `div_def)] "]"] [])
             []
             (Tactic.tacticRfl "rfl")]))))
        []
        (Term.structInstField
         (Term.structInstLVal `quotient_mul_add_remainder_eq [])
         ":="
         (Term.fun
          "fun"
          (Term.basicFun
           [(Term.hole "_") (Term.hole "_")]
           []
           "=>"
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `mod_def)] "]"] [])]))))))
        []
        (Term.structInstField (Term.structInstLVal `R []) ":=" (Term.hole "_"))
        []
        (Term.structInstField
         (Term.structInstLVal `r_well_founded [])
         ":="
         (Term.app `measure_wf [(«term_∘_» `Int.natAbs "∘" `norm)]))
        []
        (Term.structInstField (Term.structInstLVal `remainder_lt []) ":=" `nat_abs_norm_mod_lt)
        []
        (Term.structInstField
         (Term.structInstLVal `mul_left_not_lt [])
         ":="
         (Term.fun
          "fun"
          (Term.basicFun
           [`a `b `hb0]
           []
           "=>"
           («term_<|_» `not_lt_of_ge "<|" (Term.app `norm_le_norm_mul_left [`a `hb0])))))]
       (Term.optEllipsis [])
       []
       "}")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`a `b `hb0]
        []
        "=>"
        («term_<|_» `not_lt_of_ge "<|" (Term.app `norm_le_norm_mul_left [`a `hb0]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_» `not_lt_of_ge "<|" (Term.app `norm_le_norm_mul_left [`a `hb0]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `norm_le_norm_mul_left [`a `hb0])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hb0
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `norm_le_norm_mul_left
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      `not_lt_of_ge
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 10, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hb0
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `b
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `nat_abs_norm_mod_lt
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `measure_wf [(«term_∘_» `Int.natAbs "∘" `norm)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_∘_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_∘_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∘_» `Int.natAbs "∘" `norm)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `norm
[PrettyPrinter.parenthesize] ...precedences are 90 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 90, term))
      `Int.natAbs
[PrettyPrinter.parenthesize] ...precedences are 91 >? 1024, (none, [anonymous]) <=? (some 90, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 90, (some 90, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_∘_» `Int.natAbs "∘" `norm) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `measure_wf
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [(Term.hole "_") (Term.hole "_")]
        []
        "=>"
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `mod_def)] "]"] [])])))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `mod_def)] "]"] [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `mod_def)] "]"] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mod_def
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `div_def)] "]"] [])
          []
          (Tactic.tacticRfl "rfl")])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticRfl "rfl")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `div_def)] "]"] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `div_def
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.paren "(" («term_%_» (Term.cdot "·") "%" (Term.cdot "·")) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_%_» (Term.cdot "·") "%" (Term.cdot "·"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.cdot "·")
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (Term.cdot "·")
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.paren "(" («term_/_» (Term.cdot "·") "/" (Term.cdot "·")) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_/_» (Term.cdot "·") "/" (Term.cdot "·"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.cdot "·")
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (Term.cdot "·")
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `GaussianInt.nontrivial
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `GaussianInt.commRing
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app `EuclideanDomain [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]»', expected 'NumberTheory.Zsqrtd.GaussianInt.termℤ[i]._@.NumberTheory.Zsqrtd.GaussianInt._hyg.6'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
instance
  : EuclideanDomain ℤ[i]
  :=
    {
      GaussianInt.commRing , GaussianInt.nontrivial with
      Quotient := ( · / · )
        remainder := ( · % · )
        quotient_zero := by simp [ div_def ] rfl
        quotient_mul_add_remainder_eq := fun _ _ => by simp [ mod_def ]
        R := _
        r_well_founded := measure_wf Int.natAbs ∘ norm
        remainder_lt := nat_abs_norm_mod_lt
        mul_left_not_lt := fun a b hb0 => not_lt_of_ge <| norm_le_norm_mul_left a hb0
      }

open PrincipalIdealRing

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `mod_four_eq_three_of_nat_prime_of_prime [])
      (Command.declSig
       [(Term.explicitBinder "(" [`p] [":" (termℕ "ℕ")] [] ")")
        (Term.instBinder "[" [`hp ":"] (Term.app `Fact [(Term.proj `p "." `Prime)]) "]")
        (Term.explicitBinder
         "("
         [`hpi]
         [":"
          (Term.app
           `Prime
           [(Term.typeAscription
             "("
             `p
             ":"
             [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
             ")")])]
         []
         ")")]
       (Term.typeSpec ":" («term_=_» («term_%_» `p "%" (num "4")) "=" (num "3"))))
      (Command.declValSimple
       ":="
       (Term.app
        (Term.proj (Term.proj (Term.proj `hp "." (fieldIdx "1")) "." `eq_two_or_odd) "." `elim)
        [(Term.fun
          "fun"
          (Term.basicFun
           [`hp2]
           []
           "=>"
           (Term.app
            `absurd
            [`hpi
             (Term.app
              (Term.app `mt [(Term.proj `irreducible_iff_prime "." (fieldIdx "2"))])
              [(Term.fun
                "fun"
                (Term.basicFun
                 [(Term.anonymousCtor "⟨" [`hu "," `h] "⟩")]
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
                        []
                        ":="
                        (Term.app
                         `h
                         [(Term.anonymousCtor "⟨" [(num "1") "," (num "1")] "⟩")
                          (Term.anonymousCtor "⟨" [(num "1") "," («term-_» "-" (num "1"))] "⟩")
                          (Term.subst `hp2.symm "▸" [`rfl])]))))
                     []
                     (Tactic.rwSeq
                      "rw"
                      []
                      (Tactic.rwRuleSeq
                       "["
                       [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `norm_eq_one_iff)
                        ","
                        (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `norm_eq_one_iff)]
                       "]")
                      [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
                     []
                     (Tactic.exact
                      "exact"
                      (Term.app
                       `absurd
                       [`this
                        (Term.byTactic
                         "by"
                         (Tactic.tacticSeq
                          (Tactic.tacticSeq1Indented [(Tactic.decide "decide")])))]))])))))])])))
         (Term.fun
          "fun"
          (Term.basicFun
           [`hp1]
           []
           "=>"
           (Term.app
            `by_contradiction
            [(Term.fun
              "fun"
              (Term.basicFun
               [`hp3]
               [(Term.typeSpec ":" («term_≠_» («term_%_» `p "%" (num "4")) "≠" (num "3")))]
               "=>"
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(Tactic.tacticHave_
                    "have"
                    (Term.haveDecl
                     (Term.haveIdDecl
                      [`hp41 []]
                      [(Term.typeSpec ":" («term_=_» («term_%_» `p "%" (num "4")) "=" (num "1")))]
                      ":="
                      (Term.byTactic
                       "by"
                       (Tactic.tacticSeq
                        (Tactic.tacticSeq1Indented
                         [(Tactic.rwSeq
                           "rw"
                           []
                           (Tactic.rwRuleSeq
                            "["
                            [(Tactic.rwRule
                              [(patternIgnore (token.«← » "←"))]
                              (Term.app `Nat.mod_mul_left_mod [`p (num "2") (num "2")]))
                             ","
                             (Tactic.rwRule
                              []
                              (Term.show
                               "show"
                               («term_=_» («term_*_» (num "2") "*" (num "2")) "=" (num "4"))
                               (Term.fromTerm "from" `rfl)))]
                            "]")
                           [(Tactic.location "at" (Tactic.locationHyp [`hp1] []))])
                          []
                          (Tactic.tacticHave_
                           "have"
                           (Term.haveDecl
                            (Term.haveIdDecl
                             []
                             []
                             ":="
                             (Term.app
                              `Nat.mod_lt
                              [`p
                               (Term.show
                                "show"
                                («term_<_» (num "0") "<" (num "4"))
                                (Term.byTactic'
                                 "by"
                                 (Tactic.tacticSeq
                                  (Tactic.tacticSeq1Indented [(Tactic.decide "decide")]))))]))))
                          []
                          (Tactic.revert "revert" [`this `hp3 `hp1])
                          []
                          (Tactic.generalize
                           "generalize"
                           [(Tactic.generalizeArg [] («term_%_» `p "%" (num "4")) "=" `m)]
                           [])
                          ";"
                          (Tactic.decide! "decide!")]))))))
                   []
                   (Tactic.tacticLet_
                    "let"
                    (Term.letDecl
                     (Term.letPatDecl
                      (Term.anonymousCtor "⟨" [`k "," `hk] "⟩")
                      []
                      []
                      ":="
                      («term_<|_»
                       (Term.proj `Zmod.exists_sq_eq_neg_one_iff "." (fieldIdx "2"))
                       "<|"
                       (Term.byTactic
                        "by"
                        (Tactic.tacticSeq
                         (Tactic.tacticSeq1Indented
                          [(Tactic.«tactic_<;>_»
                            (Tactic.rwSeq
                             "rw"
                             []
                             (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `hp41)] "]")
                             [])
                            "<;>"
                            (Tactic.exact
                             "exact"
                             (Term.byTactic
                              "by"
                              (Tactic.tacticSeq
                               (Tactic.tacticSeq1Indented [(Tactic.decide "decide")])))))])))))))
                   []
                   (Std.Tactic.obtain
                    "obtain"
                    [(Std.Tactic.RCases.rcasesPatMed
                      [(Std.Tactic.RCases.rcasesPat.tuple
                        "⟨"
                        [(Std.Tactic.RCases.rcasesPatLo
                          (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `k)])
                          [])
                         ","
                         (Std.Tactic.RCases.rcasesPatLo
                          (Std.Tactic.RCases.rcasesPatMed
                           [(Std.Tactic.RCases.rcasesPat.one `k_lt_p)])
                          [])
                         ","
                         (Std.Tactic.RCases.rcasesPatLo
                          (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                          [])]
                        "⟩")])]
                    [":"
                     («term∃_,_»
                      "∃"
                      (Lean.explicitBinders
                       [(Lean.bracketedExplicitBinders
                         "("
                         [(Lean.binderIdent `k')]
                         ":"
                         (termℕ "ℕ")
                         ")")
                        (Lean.bracketedExplicitBinders
                         "("
                         [(Lean.binderIdent `h)]
                         ":"
                         («term_<_» `k' "<" `p)
                         ")")])
                      ","
                      («term_=_»
                       (Term.typeAscription "(" `k' ":" [(Term.app `Zmod [`p])] ")")
                       "="
                       `k))]
                    [":="
                     [(Term.byTactic
                       "by"
                       (Tactic.tacticSeq
                        (Tactic.tacticSeq1Indented
                         [(Tactic.refine'
                           "refine'"
                           (Term.anonymousCtor
                            "⟨"
                            [`k.val "," `k.val_lt "," (Term.app `Zmod.nat_cast_zmod_val [`k])]
                            "⟩"))])))]])
                   []
                   (Tactic.tacticHave_
                    "have"
                    (Term.haveDecl
                     (Term.haveIdDecl
                      [`hpk []]
                      [(Term.typeSpec
                        ":"
                        («term_∣_» `p "∣" («term_+_» («term_^_» `k "^" (num "2")) "+" (num "1"))))]
                      ":="
                      (Term.byTactic
                       "by"
                       (Tactic.tacticSeq
                        (Tactic.tacticSeq1Indented
                         [(Tactic.rwSeq
                           "rw"
                           []
                           (Tactic.rwRuleSeq
                            "["
                            [(Tactic.rwRule [] `pow_two)
                             ","
                             (Tactic.rwRule
                              [(patternIgnore (token.«← » "←"))]
                              (Term.app `CharP.cast_eq_zero_iff [(Term.app `Zmod [`p]) `p]))
                             ","
                             (Tactic.rwRule [] `Nat.cast_add)
                             ","
                             (Tactic.rwRule [] `Nat.cast_mul)
                             ","
                             (Tactic.rwRule [] `Nat.cast_one)
                             ","
                             (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `hk)
                             ","
                             (Tactic.rwRule [] `add_left_neg)]
                            "]")
                           [])]))))))
                   []
                   (Tactic.tacticHave_
                    "have"
                    (Term.haveDecl
                     (Term.haveIdDecl
                      [`hkmul []]
                      [(Term.typeSpec
                        ":"
                        («term_=_»
                         (Term.typeAscription
                          "("
                          («term_+_» («term_^_» `k "^" (num "2")) "+" (num "1"))
                          ":"
                          [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
                          ")")
                         "="
                         («term_*_»
                          (Term.anonymousCtor "⟨" [`k "," (num "1")] "⟩")
                          "*"
                          (Term.anonymousCtor "⟨" [`k "," («term-_» "-" (num "1"))] "⟩"))))]
                      ":="
                      (Term.byTactic
                       "by"
                       (Tactic.tacticSeq
                        (Tactic.tacticSeq1Indented
                         [(Tactic.simp
                           "simp"
                           []
                           []
                           []
                           ["["
                            [(Tactic.simpLemma [] [] `sq) "," (Tactic.simpLemma [] [] `Zsqrtd.ext)]
                            "]"]
                           [])]))))))
                   []
                   (Tactic.tacticHave_
                    "have"
                    (Term.haveDecl
                     (Term.haveIdDecl
                      [`hpne1 []]
                      [(Term.typeSpec ":" («term_≠_» `p "≠" (num "1")))]
                      ":="
                      (Term.app
                       `ne_of_gt
                       [(Term.proj (Term.proj `hp "." (fieldIdx "1")) "." `one_lt)]))))
                   []
                   (Tactic.tacticHave_
                    "have"
                    (Term.haveDecl
                     (Term.haveIdDecl
                      [`hkltp []]
                      [(Term.typeSpec
                        ":"
                        («term_<_»
                         («term_+_» (num "1") "+" («term_*_» `k "*" `k))
                         "<"
                         («term_*_» `p "*" `p)))]
                      ":="
                      (calc
                       "calc"
                       (calcStep
                        («term_≤_»
                         («term_+_» (num "1") "+" («term_*_» `k "*" `k))
                         "≤"
                         («term_+_» `k "+" («term_*_» `k "*" `k)))
                        ":="
                        (Term.app
                         `add_le_add_right
                         [(Term.app
                           `Nat.pos_of_ne_zero
                           [(Term.fun
                             "fun"
                             (Term.basicFun
                              [`hk0]
                              []
                              "=>"
                              (Term.byTactic
                               "by"
                               (Tactic.tacticSeq
                                (Tactic.tacticSeq1Indented
                                 [(Tactic.«tactic_<;>_»
                                   (Mathlib.Tactic.clearAuxDecl "clear_aux_decl")
                                   "<;>"
                                   (Tactic.simpAll
                                    "simp_all"
                                    []
                                    []
                                    []
                                    ["[" [(Tactic.simpLemma [] [] `pow_succ')] "]"]))])))))])
                          (Term.hole "_")]))
                       [(calcStep
                         («term_=_»
                          (Term.hole "_")
                          "="
                          («term_*_» `k "*" («term_+_» `k "+" (num "1"))))
                         ":="
                         (Term.byTactic
                          "by"
                          (Tactic.tacticSeq
                           (Tactic.tacticSeq1Indented
                            [(Tactic.simp
                              "simp"
                              []
                              []
                              []
                              ["["
                               [(Tactic.simpLemma [] [] `add_comm)
                                ","
                                (Tactic.simpLemma [] [] `mul_add)]
                               "]"]
                              [])]))))
                        (calcStep
                         («term_<_» (Term.hole "_") "<" («term_*_» `p "*" `p))
                         ":="
                         (Term.app
                          `mul_lt_mul
                          [`k_lt_p
                           `k_lt_p
                           (Term.app `Nat.succ_pos [(Term.hole "_")])
                           (Term.app `Nat.zero_le [(Term.hole "_")])]))]))))
                   []
                   (Tactic.tacticHave_
                    "have"
                    (Term.haveDecl
                     (Term.haveIdDecl
                      [`hpk₁ []]
                      [(Term.typeSpec
                        ":"
                        («term¬_»
                         "¬"
                         («term_∣_»
                          (Term.typeAscription
                           "("
                           `p
                           ":"
                           [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
                           ")")
                          "∣"
                          (Term.anonymousCtor "⟨" [`k "," («term-_» "-" (num "1"))] "⟩"))))]
                      ":="
                      (Term.fun
                       "fun"
                       (Term.basicFun
                        [(Term.anonymousCtor "⟨" [`x "," `hx] "⟩")]
                        []
                        "=>"
                        («term_<|_»
                         (Term.app
                          `lt_irrefl
                          [(Term.proj
                            (Term.proj
                             (Term.typeAscription
                              "("
                              («term_*_» `p "*" `x)
                              ":"
                              [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
                              ")")
                             "."
                             `norm)
                            "."
                            `natAbs)])
                         "<|"
                         (calc
                          "calc"
                          (calcStep
                           («term_=_»
                            (Term.proj
                             (Term.app
                              `norm
                              [(Term.typeAscription
                                "("
                                («term_*_» `p "*" `x)
                                ":"
                                [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
                                ")")])
                             "."
                             `natAbs)
                            "="
                            (Term.proj
                             (Term.app
                              `Zsqrtd.norm
                              [(Term.anonymousCtor "⟨" [`k "," («term-_» "-" (num "1"))] "⟩")])
                             "."
                             `natAbs))
                           ":="
                           (Term.byTactic
                            "by"
                            (Tactic.tacticSeq
                             (Tactic.tacticSeq1Indented
                              [(Tactic.rwSeq
                                "rw"
                                []
                                (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `hx)] "]")
                                [])]))))
                          [(calcStep
                            («term_<_»
                             (Term.hole "_")
                             "<"
                             (Term.proj
                              (Term.app
                               `norm
                               [(Term.typeAscription
                                 "("
                                 `p
                                 ":"
                                 [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
                                 ")")])
                              "."
                              `natAbs))
                            ":="
                            (Term.byTactic
                             "by"
                             (Tactic.tacticSeq
                              (Tactic.tacticSeq1Indented
                               [(Std.Tactic.Simpa.simpa
                                 "simpa"
                                 []
                                 []
                                 (Std.Tactic.Simpa.simpaArgsRest
                                  []
                                  []
                                  []
                                  [(Tactic.simpArgs
                                    "["
                                    [(Tactic.simpLemma [] [] `add_comm)
                                     ","
                                     (Tactic.simpLemma [] [] `Zsqrtd.norm)]
                                    "]")]
                                  ["using" `hkltp]))]))))
                           (calcStep
                            («term_≤_»
                             (Term.hole "_")
                             "≤"
                             (Term.proj
                              (Term.app
                               `norm
                               [(Term.typeAscription
                                 "("
                                 («term_*_» `p "*" `x)
                                 ":"
                                 [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
                                 ")")])
                              "."
                              `natAbs))
                            ":="
                            (Term.app
                             `norm_le_norm_mul_left
                             [(Term.hole "_")
                              (Term.fun
                               "fun"
                               (Term.basicFun
                                [`hx0]
                                []
                                "=>"
                                («term_<|_»
                                 (Term.show
                                  "show"
                                  («term_≠_»
                                   (Term.typeAscription
                                    "("
                                    («term-_» "-" (num "1"))
                                    ":"
                                    [(termℤ "ℤ")]
                                    ")")
                                   "≠"
                                   (num "0"))
                                  (Term.byTactic'
                                   "by"
                                   (Tactic.tacticSeq
                                    (Tactic.tacticSeq1Indented [(Tactic.decide "decide")]))))
                                 "<|"
                                 (Term.byTactic
                                  "by"
                                  (Tactic.tacticSeq
                                   (Tactic.tacticSeq1Indented
                                    [(Std.Tactic.Simpa.simpa
                                      "simpa"
                                      []
                                      []
                                      (Std.Tactic.Simpa.simpaArgsRest
                                       []
                                       []
                                       []
                                       [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `hx0)] "]")]
                                       ["using"
                                        (Term.app `congr_arg [`Zsqrtd.im `hx])]))]))))))]))])))))))
                   []
                   (Tactic.tacticHave_
                    "have"
                    (Term.haveDecl
                     (Term.haveIdDecl
                      [`hpk₂ []]
                      [(Term.typeSpec
                        ":"
                        («term¬_»
                         "¬"
                         («term_∣_»
                          (Term.typeAscription
                           "("
                           `p
                           ":"
                           [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
                           ")")
                          "∣"
                          (Term.anonymousCtor "⟨" [`k "," (num "1")] "⟩"))))]
                      ":="
                      (Term.fun
                       "fun"
                       (Term.basicFun
                        [(Term.anonymousCtor "⟨" [`x "," `hx] "⟩")]
                        []
                        "=>"
                        («term_<|_»
                         (Term.app
                          `lt_irrefl
                          [(Term.proj
                            (Term.proj
                             (Term.typeAscription
                              "("
                              («term_*_» `p "*" `x)
                              ":"
                              [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
                              ")")
                             "."
                             `norm)
                            "."
                            `natAbs)])
                         "<|"
                         (calc
                          "calc"
                          (calcStep
                           («term_=_»
                            (Term.proj
                             (Term.app
                              `norm
                              [(Term.typeAscription
                                "("
                                («term_*_» `p "*" `x)
                                ":"
                                [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
                                ")")])
                             "."
                             `natAbs)
                            "="
                            (Term.proj
                             (Term.app
                              `Zsqrtd.norm
                              [(Term.anonymousCtor "⟨" [`k "," (num "1")] "⟩")])
                             "."
                             `natAbs))
                           ":="
                           (Term.byTactic
                            "by"
                            (Tactic.tacticSeq
                             (Tactic.tacticSeq1Indented
                              [(Tactic.rwSeq
                                "rw"
                                []
                                (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `hx)] "]")
                                [])]))))
                          [(calcStep
                            («term_<_»
                             (Term.hole "_")
                             "<"
                             (Term.proj
                              (Term.app
                               `norm
                               [(Term.typeAscription
                                 "("
                                 `p
                                 ":"
                                 [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
                                 ")")])
                              "."
                              `natAbs))
                            ":="
                            (Term.byTactic
                             "by"
                             (Tactic.tacticSeq
                              (Tactic.tacticSeq1Indented
                               [(Std.Tactic.Simpa.simpa
                                 "simpa"
                                 []
                                 []
                                 (Std.Tactic.Simpa.simpaArgsRest
                                  []
                                  []
                                  []
                                  [(Tactic.simpArgs
                                    "["
                                    [(Tactic.simpLemma [] [] `add_comm)
                                     ","
                                     (Tactic.simpLemma [] [] `Zsqrtd.norm)]
                                    "]")]
                                  ["using" `hkltp]))]))))
                           (calcStep
                            («term_≤_»
                             (Term.hole "_")
                             "≤"
                             (Term.proj
                              (Term.app
                               `norm
                               [(Term.typeAscription
                                 "("
                                 («term_*_» `p "*" `x)
                                 ":"
                                 [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
                                 ")")])
                              "."
                              `natAbs))
                            ":="
                            (Term.app
                             `norm_le_norm_mul_left
                             [(Term.hole "_")
                              (Term.fun
                               "fun"
                               (Term.basicFun
                                [`hx0]
                                []
                                "=>"
                                («term_<|_»
                                 (Term.show
                                  "show"
                                  («term_≠_»
                                   (Term.typeAscription "(" (num "1") ":" [(termℤ "ℤ")] ")")
                                   "≠"
                                   (num "0"))
                                  (Term.byTactic'
                                   "by"
                                   (Tactic.tacticSeq
                                    (Tactic.tacticSeq1Indented [(Tactic.decide "decide")]))))
                                 "<|"
                                 (Term.byTactic
                                  "by"
                                  (Tactic.tacticSeq
                                   (Tactic.tacticSeq1Indented
                                    [(Std.Tactic.Simpa.simpa
                                      "simpa"
                                      []
                                      []
                                      (Std.Tactic.Simpa.simpaArgsRest
                                       []
                                       []
                                       []
                                       [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `hx0)] "]")]
                                       ["using"
                                        (Term.app `congr_arg [`Zsqrtd.im `hx])]))]))))))]))])))))))
                   []
                   (Tactic.tacticHave_
                    "have"
                    (Term.haveDecl
                     (Term.haveIdDecl
                      [`hpu []]
                      [(Term.typeSpec
                        ":"
                        («term¬_»
                         "¬"
                         (Term.app
                          `IsUnit
                          [(Term.typeAscription
                            "("
                            `p
                            ":"
                            [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
                            ")")])))]
                      ":="
                      (Term.app
                       `mt
                       [(Term.proj `norm_eq_one_iff "." (fieldIdx "2"))
                        (Term.byTactic
                         "by"
                         (Tactic.tacticSeq
                          (Tactic.tacticSeq1Indented
                           [(Tactic.«tactic_<;>_»
                             (Tactic.rwSeq
                              "rw"
                              []
                              (Tactic.rwRuleSeq
                               "["
                               [(Tactic.rwRule [] `norm_nat_cast)
                                ","
                                (Tactic.rwRule [] `Int.natAbs_mul)
                                ","
                                (Tactic.rwRule [] `Nat.mul_eq_one_iff)]
                               "]")
                              [])
                             "<;>"
                             (Tactic.exact
                              "exact"
                              (Term.fun
                               "fun"
                               (Term.basicFun
                                [`h]
                                []
                                "=>"
                                (Term.app
                                 (Term.proj
                                  (Term.app
                                   `ne_of_lt
                                   [(Term.proj (Term.proj `hp "." (fieldIdx "1")) "." `one_lt)])
                                  "."
                                  `symm)
                                 [(Term.proj `h "." (fieldIdx "1"))])))))])))]))))
                   []
                   (Std.Tactic.obtain
                    "obtain"
                    [(Std.Tactic.RCases.rcasesPatMed
                      [(Std.Tactic.RCases.rcasesPat.tuple
                        "⟨"
                        [(Std.Tactic.RCases.rcasesPatLo
                          (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `y)])
                          [])
                         ","
                         (Std.Tactic.RCases.rcasesPatLo
                          (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hy)])
                          [])]
                        "⟩")])]
                    []
                    [":=" [`hpk]])
                   []
                   (Tactic.tacticHave_
                    "have"
                    (Term.haveDecl
                     (Term.haveIdDecl
                      []
                      []
                      ":="
                      (Term.app
                       (Term.proj (Term.proj `hpi "." (fieldIdx "2")) "." (fieldIdx "2"))
                       [(Term.anonymousCtor "⟨" [`k "," (num "1")] "⟩")
                        (Term.anonymousCtor "⟨" [`k "," («term-_» "-" (num "1"))] "⟩")
                        (Term.anonymousCtor
                         "⟨"
                         [`y
                          ","
                          (Term.byTactic
                           "by"
                           (Tactic.tacticSeq
                            (Tactic.tacticSeq1Indented
                             [(Tactic.«tactic_<;>_»
                               (Tactic.rwSeq
                                "rw"
                                []
                                (Tactic.rwRuleSeq
                                 "["
                                 [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `hkmul)
                                  ","
                                  (Tactic.rwRule
                                   [(patternIgnore (token.«← » "←"))]
                                   (Term.app `Nat.cast_mul [`p]))
                                  ","
                                  (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `hy)]
                                 "]")
                                [])
                               "<;>"
                               (Tactic.simp "simp" [] [] [] [] []))])))]
                         "⟩")]))))
                   []
                   (Mathlib.Tactic.clearAuxDecl "clear_aux_decl")
                   []
                   (Mathlib.Tactic.Tauto.tauto "tauto" [])])))))])))])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj (Term.proj (Term.proj `hp "." (fieldIdx "1")) "." `eq_two_or_odd) "." `elim)
       [(Term.fun
         "fun"
         (Term.basicFun
          [`hp2]
          []
          "=>"
          (Term.app
           `absurd
           [`hpi
            (Term.app
             (Term.app `mt [(Term.proj `irreducible_iff_prime "." (fieldIdx "2"))])
             [(Term.fun
               "fun"
               (Term.basicFun
                [(Term.anonymousCtor "⟨" [`hu "," `h] "⟩")]
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
                       []
                       ":="
                       (Term.app
                        `h
                        [(Term.anonymousCtor "⟨" [(num "1") "," (num "1")] "⟩")
                         (Term.anonymousCtor "⟨" [(num "1") "," («term-_» "-" (num "1"))] "⟩")
                         (Term.subst `hp2.symm "▸" [`rfl])]))))
                    []
                    (Tactic.rwSeq
                     "rw"
                     []
                     (Tactic.rwRuleSeq
                      "["
                      [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `norm_eq_one_iff)
                       ","
                       (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `norm_eq_one_iff)]
                      "]")
                     [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
                    []
                    (Tactic.exact
                     "exact"
                     (Term.app
                      `absurd
                      [`this
                       (Term.byTactic
                        "by"
                        (Tactic.tacticSeq
                         (Tactic.tacticSeq1Indented [(Tactic.decide "decide")])))]))])))))])])))
        (Term.fun
         "fun"
         (Term.basicFun
          [`hp1]
          []
          "=>"
          (Term.app
           `by_contradiction
           [(Term.fun
             "fun"
             (Term.basicFun
              [`hp3]
              [(Term.typeSpec ":" («term_≠_» («term_%_» `p "%" (num "4")) "≠" (num "3")))]
              "=>"
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Tactic.tacticHave_
                   "have"
                   (Term.haveDecl
                    (Term.haveIdDecl
                     [`hp41 []]
                     [(Term.typeSpec ":" («term_=_» («term_%_» `p "%" (num "4")) "=" (num "1")))]
                     ":="
                     (Term.byTactic
                      "by"
                      (Tactic.tacticSeq
                       (Tactic.tacticSeq1Indented
                        [(Tactic.rwSeq
                          "rw"
                          []
                          (Tactic.rwRuleSeq
                           "["
                           [(Tactic.rwRule
                             [(patternIgnore (token.«← » "←"))]
                             (Term.app `Nat.mod_mul_left_mod [`p (num "2") (num "2")]))
                            ","
                            (Tactic.rwRule
                             []
                             (Term.show
                              "show"
                              («term_=_» («term_*_» (num "2") "*" (num "2")) "=" (num "4"))
                              (Term.fromTerm "from" `rfl)))]
                           "]")
                          [(Tactic.location "at" (Tactic.locationHyp [`hp1] []))])
                         []
                         (Tactic.tacticHave_
                          "have"
                          (Term.haveDecl
                           (Term.haveIdDecl
                            []
                            []
                            ":="
                            (Term.app
                             `Nat.mod_lt
                             [`p
                              (Term.show
                               "show"
                               («term_<_» (num "0") "<" (num "4"))
                               (Term.byTactic'
                                "by"
                                (Tactic.tacticSeq
                                 (Tactic.tacticSeq1Indented [(Tactic.decide "decide")]))))]))))
                         []
                         (Tactic.revert "revert" [`this `hp3 `hp1])
                         []
                         (Tactic.generalize
                          "generalize"
                          [(Tactic.generalizeArg [] («term_%_» `p "%" (num "4")) "=" `m)]
                          [])
                         ";"
                         (Tactic.decide! "decide!")]))))))
                  []
                  (Tactic.tacticLet_
                   "let"
                   (Term.letDecl
                    (Term.letPatDecl
                     (Term.anonymousCtor "⟨" [`k "," `hk] "⟩")
                     []
                     []
                     ":="
                     («term_<|_»
                      (Term.proj `Zmod.exists_sq_eq_neg_one_iff "." (fieldIdx "2"))
                      "<|"
                      (Term.byTactic
                       "by"
                       (Tactic.tacticSeq
                        (Tactic.tacticSeq1Indented
                         [(Tactic.«tactic_<;>_»
                           (Tactic.rwSeq
                            "rw"
                            []
                            (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `hp41)] "]")
                            [])
                           "<;>"
                           (Tactic.exact
                            "exact"
                            (Term.byTactic
                             "by"
                             (Tactic.tacticSeq
                              (Tactic.tacticSeq1Indented [(Tactic.decide "decide")])))))])))))))
                  []
                  (Std.Tactic.obtain
                   "obtain"
                   [(Std.Tactic.RCases.rcasesPatMed
                     [(Std.Tactic.RCases.rcasesPat.tuple
                       "⟨"
                       [(Std.Tactic.RCases.rcasesPatLo
                         (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `k)])
                         [])
                        ","
                        (Std.Tactic.RCases.rcasesPatLo
                         (Std.Tactic.RCases.rcasesPatMed
                          [(Std.Tactic.RCases.rcasesPat.one `k_lt_p)])
                         [])
                        ","
                        (Std.Tactic.RCases.rcasesPatLo
                         (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                         [])]
                       "⟩")])]
                   [":"
                    («term∃_,_»
                     "∃"
                     (Lean.explicitBinders
                      [(Lean.bracketedExplicitBinders
                        "("
                        [(Lean.binderIdent `k')]
                        ":"
                        (termℕ "ℕ")
                        ")")
                       (Lean.bracketedExplicitBinders
                        "("
                        [(Lean.binderIdent `h)]
                        ":"
                        («term_<_» `k' "<" `p)
                        ")")])
                     ","
                     («term_=_»
                      (Term.typeAscription "(" `k' ":" [(Term.app `Zmod [`p])] ")")
                      "="
                      `k))]
                   [":="
                    [(Term.byTactic
                      "by"
                      (Tactic.tacticSeq
                       (Tactic.tacticSeq1Indented
                        [(Tactic.refine'
                          "refine'"
                          (Term.anonymousCtor
                           "⟨"
                           [`k.val "," `k.val_lt "," (Term.app `Zmod.nat_cast_zmod_val [`k])]
                           "⟩"))])))]])
                  []
                  (Tactic.tacticHave_
                   "have"
                   (Term.haveDecl
                    (Term.haveIdDecl
                     [`hpk []]
                     [(Term.typeSpec
                       ":"
                       («term_∣_» `p "∣" («term_+_» («term_^_» `k "^" (num "2")) "+" (num "1"))))]
                     ":="
                     (Term.byTactic
                      "by"
                      (Tactic.tacticSeq
                       (Tactic.tacticSeq1Indented
                        [(Tactic.rwSeq
                          "rw"
                          []
                          (Tactic.rwRuleSeq
                           "["
                           [(Tactic.rwRule [] `pow_two)
                            ","
                            (Tactic.rwRule
                             [(patternIgnore (token.«← » "←"))]
                             (Term.app `CharP.cast_eq_zero_iff [(Term.app `Zmod [`p]) `p]))
                            ","
                            (Tactic.rwRule [] `Nat.cast_add)
                            ","
                            (Tactic.rwRule [] `Nat.cast_mul)
                            ","
                            (Tactic.rwRule [] `Nat.cast_one)
                            ","
                            (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `hk)
                            ","
                            (Tactic.rwRule [] `add_left_neg)]
                           "]")
                          [])]))))))
                  []
                  (Tactic.tacticHave_
                   "have"
                   (Term.haveDecl
                    (Term.haveIdDecl
                     [`hkmul []]
                     [(Term.typeSpec
                       ":"
                       («term_=_»
                        (Term.typeAscription
                         "("
                         («term_+_» («term_^_» `k "^" (num "2")) "+" (num "1"))
                         ":"
                         [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
                         ")")
                        "="
                        («term_*_»
                         (Term.anonymousCtor "⟨" [`k "," (num "1")] "⟩")
                         "*"
                         (Term.anonymousCtor "⟨" [`k "," («term-_» "-" (num "1"))] "⟩"))))]
                     ":="
                     (Term.byTactic
                      "by"
                      (Tactic.tacticSeq
                       (Tactic.tacticSeq1Indented
                        [(Tactic.simp
                          "simp"
                          []
                          []
                          []
                          ["["
                           [(Tactic.simpLemma [] [] `sq) "," (Tactic.simpLemma [] [] `Zsqrtd.ext)]
                           "]"]
                          [])]))))))
                  []
                  (Tactic.tacticHave_
                   "have"
                   (Term.haveDecl
                    (Term.haveIdDecl
                     [`hpne1 []]
                     [(Term.typeSpec ":" («term_≠_» `p "≠" (num "1")))]
                     ":="
                     (Term.app
                      `ne_of_gt
                      [(Term.proj (Term.proj `hp "." (fieldIdx "1")) "." `one_lt)]))))
                  []
                  (Tactic.tacticHave_
                   "have"
                   (Term.haveDecl
                    (Term.haveIdDecl
                     [`hkltp []]
                     [(Term.typeSpec
                       ":"
                       («term_<_»
                        («term_+_» (num "1") "+" («term_*_» `k "*" `k))
                        "<"
                        («term_*_» `p "*" `p)))]
                     ":="
                     (calc
                      "calc"
                      (calcStep
                       («term_≤_»
                        («term_+_» (num "1") "+" («term_*_» `k "*" `k))
                        "≤"
                        («term_+_» `k "+" («term_*_» `k "*" `k)))
                       ":="
                       (Term.app
                        `add_le_add_right
                        [(Term.app
                          `Nat.pos_of_ne_zero
                          [(Term.fun
                            "fun"
                            (Term.basicFun
                             [`hk0]
                             []
                             "=>"
                             (Term.byTactic
                              "by"
                              (Tactic.tacticSeq
                               (Tactic.tacticSeq1Indented
                                [(Tactic.«tactic_<;>_»
                                  (Mathlib.Tactic.clearAuxDecl "clear_aux_decl")
                                  "<;>"
                                  (Tactic.simpAll
                                   "simp_all"
                                   []
                                   []
                                   []
                                   ["[" [(Tactic.simpLemma [] [] `pow_succ')] "]"]))])))))])
                         (Term.hole "_")]))
                      [(calcStep
                        («term_=_»
                         (Term.hole "_")
                         "="
                         («term_*_» `k "*" («term_+_» `k "+" (num "1"))))
                        ":="
                        (Term.byTactic
                         "by"
                         (Tactic.tacticSeq
                          (Tactic.tacticSeq1Indented
                           [(Tactic.simp
                             "simp"
                             []
                             []
                             []
                             ["["
                              [(Tactic.simpLemma [] [] `add_comm)
                               ","
                               (Tactic.simpLemma [] [] `mul_add)]
                              "]"]
                             [])]))))
                       (calcStep
                        («term_<_» (Term.hole "_") "<" («term_*_» `p "*" `p))
                        ":="
                        (Term.app
                         `mul_lt_mul
                         [`k_lt_p
                          `k_lt_p
                          (Term.app `Nat.succ_pos [(Term.hole "_")])
                          (Term.app `Nat.zero_le [(Term.hole "_")])]))]))))
                  []
                  (Tactic.tacticHave_
                   "have"
                   (Term.haveDecl
                    (Term.haveIdDecl
                     [`hpk₁ []]
                     [(Term.typeSpec
                       ":"
                       («term¬_»
                        "¬"
                        («term_∣_»
                         (Term.typeAscription
                          "("
                          `p
                          ":"
                          [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
                          ")")
                         "∣"
                         (Term.anonymousCtor "⟨" [`k "," («term-_» "-" (num "1"))] "⟩"))))]
                     ":="
                     (Term.fun
                      "fun"
                      (Term.basicFun
                       [(Term.anonymousCtor "⟨" [`x "," `hx] "⟩")]
                       []
                       "=>"
                       («term_<|_»
                        (Term.app
                         `lt_irrefl
                         [(Term.proj
                           (Term.proj
                            (Term.typeAscription
                             "("
                             («term_*_» `p "*" `x)
                             ":"
                             [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
                             ")")
                            "."
                            `norm)
                           "."
                           `natAbs)])
                        "<|"
                        (calc
                         "calc"
                         (calcStep
                          («term_=_»
                           (Term.proj
                            (Term.app
                             `norm
                             [(Term.typeAscription
                               "("
                               («term_*_» `p "*" `x)
                               ":"
                               [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
                               ")")])
                            "."
                            `natAbs)
                           "="
                           (Term.proj
                            (Term.app
                             `Zsqrtd.norm
                             [(Term.anonymousCtor "⟨" [`k "," («term-_» "-" (num "1"))] "⟩")])
                            "."
                            `natAbs))
                          ":="
                          (Term.byTactic
                           "by"
                           (Tactic.tacticSeq
                            (Tactic.tacticSeq1Indented
                             [(Tactic.rwSeq
                               "rw"
                               []
                               (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `hx)] "]")
                               [])]))))
                         [(calcStep
                           («term_<_»
                            (Term.hole "_")
                            "<"
                            (Term.proj
                             (Term.app
                              `norm
                              [(Term.typeAscription
                                "("
                                `p
                                ":"
                                [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
                                ")")])
                             "."
                             `natAbs))
                           ":="
                           (Term.byTactic
                            "by"
                            (Tactic.tacticSeq
                             (Tactic.tacticSeq1Indented
                              [(Std.Tactic.Simpa.simpa
                                "simpa"
                                []
                                []
                                (Std.Tactic.Simpa.simpaArgsRest
                                 []
                                 []
                                 []
                                 [(Tactic.simpArgs
                                   "["
                                   [(Tactic.simpLemma [] [] `add_comm)
                                    ","
                                    (Tactic.simpLemma [] [] `Zsqrtd.norm)]
                                   "]")]
                                 ["using" `hkltp]))]))))
                          (calcStep
                           («term_≤_»
                            (Term.hole "_")
                            "≤"
                            (Term.proj
                             (Term.app
                              `norm
                              [(Term.typeAscription
                                "("
                                («term_*_» `p "*" `x)
                                ":"
                                [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
                                ")")])
                             "."
                             `natAbs))
                           ":="
                           (Term.app
                            `norm_le_norm_mul_left
                            [(Term.hole "_")
                             (Term.fun
                              "fun"
                              (Term.basicFun
                               [`hx0]
                               []
                               "=>"
                               («term_<|_»
                                (Term.show
                                 "show"
                                 («term_≠_»
                                  (Term.typeAscription
                                   "("
                                   («term-_» "-" (num "1"))
                                   ":"
                                   [(termℤ "ℤ")]
                                   ")")
                                  "≠"
                                  (num "0"))
                                 (Term.byTactic'
                                  "by"
                                  (Tactic.tacticSeq
                                   (Tactic.tacticSeq1Indented [(Tactic.decide "decide")]))))
                                "<|"
                                (Term.byTactic
                                 "by"
                                 (Tactic.tacticSeq
                                  (Tactic.tacticSeq1Indented
                                   [(Std.Tactic.Simpa.simpa
                                     "simpa"
                                     []
                                     []
                                     (Std.Tactic.Simpa.simpaArgsRest
                                      []
                                      []
                                      []
                                      [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `hx0)] "]")]
                                      ["using"
                                       (Term.app `congr_arg [`Zsqrtd.im `hx])]))]))))))]))])))))))
                  []
                  (Tactic.tacticHave_
                   "have"
                   (Term.haveDecl
                    (Term.haveIdDecl
                     [`hpk₂ []]
                     [(Term.typeSpec
                       ":"
                       («term¬_»
                        "¬"
                        («term_∣_»
                         (Term.typeAscription
                          "("
                          `p
                          ":"
                          [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
                          ")")
                         "∣"
                         (Term.anonymousCtor "⟨" [`k "," (num "1")] "⟩"))))]
                     ":="
                     (Term.fun
                      "fun"
                      (Term.basicFun
                       [(Term.anonymousCtor "⟨" [`x "," `hx] "⟩")]
                       []
                       "=>"
                       («term_<|_»
                        (Term.app
                         `lt_irrefl
                         [(Term.proj
                           (Term.proj
                            (Term.typeAscription
                             "("
                             («term_*_» `p "*" `x)
                             ":"
                             [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
                             ")")
                            "."
                            `norm)
                           "."
                           `natAbs)])
                        "<|"
                        (calc
                         "calc"
                         (calcStep
                          («term_=_»
                           (Term.proj
                            (Term.app
                             `norm
                             [(Term.typeAscription
                               "("
                               («term_*_» `p "*" `x)
                               ":"
                               [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
                               ")")])
                            "."
                            `natAbs)
                           "="
                           (Term.proj
                            (Term.app
                             `Zsqrtd.norm
                             [(Term.anonymousCtor "⟨" [`k "," (num "1")] "⟩")])
                            "."
                            `natAbs))
                          ":="
                          (Term.byTactic
                           "by"
                           (Tactic.tacticSeq
                            (Tactic.tacticSeq1Indented
                             [(Tactic.rwSeq
                               "rw"
                               []
                               (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `hx)] "]")
                               [])]))))
                         [(calcStep
                           («term_<_»
                            (Term.hole "_")
                            "<"
                            (Term.proj
                             (Term.app
                              `norm
                              [(Term.typeAscription
                                "("
                                `p
                                ":"
                                [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
                                ")")])
                             "."
                             `natAbs))
                           ":="
                           (Term.byTactic
                            "by"
                            (Tactic.tacticSeq
                             (Tactic.tacticSeq1Indented
                              [(Std.Tactic.Simpa.simpa
                                "simpa"
                                []
                                []
                                (Std.Tactic.Simpa.simpaArgsRest
                                 []
                                 []
                                 []
                                 [(Tactic.simpArgs
                                   "["
                                   [(Tactic.simpLemma [] [] `add_comm)
                                    ","
                                    (Tactic.simpLemma [] [] `Zsqrtd.norm)]
                                   "]")]
                                 ["using" `hkltp]))]))))
                          (calcStep
                           («term_≤_»
                            (Term.hole "_")
                            "≤"
                            (Term.proj
                             (Term.app
                              `norm
                              [(Term.typeAscription
                                "("
                                («term_*_» `p "*" `x)
                                ":"
                                [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
                                ")")])
                             "."
                             `natAbs))
                           ":="
                           (Term.app
                            `norm_le_norm_mul_left
                            [(Term.hole "_")
                             (Term.fun
                              "fun"
                              (Term.basicFun
                               [`hx0]
                               []
                               "=>"
                               («term_<|_»
                                (Term.show
                                 "show"
                                 («term_≠_»
                                  (Term.typeAscription "(" (num "1") ":" [(termℤ "ℤ")] ")")
                                  "≠"
                                  (num "0"))
                                 (Term.byTactic'
                                  "by"
                                  (Tactic.tacticSeq
                                   (Tactic.tacticSeq1Indented [(Tactic.decide "decide")]))))
                                "<|"
                                (Term.byTactic
                                 "by"
                                 (Tactic.tacticSeq
                                  (Tactic.tacticSeq1Indented
                                   [(Std.Tactic.Simpa.simpa
                                     "simpa"
                                     []
                                     []
                                     (Std.Tactic.Simpa.simpaArgsRest
                                      []
                                      []
                                      []
                                      [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `hx0)] "]")]
                                      ["using"
                                       (Term.app `congr_arg [`Zsqrtd.im `hx])]))]))))))]))])))))))
                  []
                  (Tactic.tacticHave_
                   "have"
                   (Term.haveDecl
                    (Term.haveIdDecl
                     [`hpu []]
                     [(Term.typeSpec
                       ":"
                       («term¬_»
                        "¬"
                        (Term.app
                         `IsUnit
                         [(Term.typeAscription
                           "("
                           `p
                           ":"
                           [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
                           ")")])))]
                     ":="
                     (Term.app
                      `mt
                      [(Term.proj `norm_eq_one_iff "." (fieldIdx "2"))
                       (Term.byTactic
                        "by"
                        (Tactic.tacticSeq
                         (Tactic.tacticSeq1Indented
                          [(Tactic.«tactic_<;>_»
                            (Tactic.rwSeq
                             "rw"
                             []
                             (Tactic.rwRuleSeq
                              "["
                              [(Tactic.rwRule [] `norm_nat_cast)
                               ","
                               (Tactic.rwRule [] `Int.natAbs_mul)
                               ","
                               (Tactic.rwRule [] `Nat.mul_eq_one_iff)]
                              "]")
                             [])
                            "<;>"
                            (Tactic.exact
                             "exact"
                             (Term.fun
                              "fun"
                              (Term.basicFun
                               [`h]
                               []
                               "=>"
                               (Term.app
                                (Term.proj
                                 (Term.app
                                  `ne_of_lt
                                  [(Term.proj (Term.proj `hp "." (fieldIdx "1")) "." `one_lt)])
                                 "."
                                 `symm)
                                [(Term.proj `h "." (fieldIdx "1"))])))))])))]))))
                  []
                  (Std.Tactic.obtain
                   "obtain"
                   [(Std.Tactic.RCases.rcasesPatMed
                     [(Std.Tactic.RCases.rcasesPat.tuple
                       "⟨"
                       [(Std.Tactic.RCases.rcasesPatLo
                         (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `y)])
                         [])
                        ","
                        (Std.Tactic.RCases.rcasesPatLo
                         (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hy)])
                         [])]
                       "⟩")])]
                   []
                   [":=" [`hpk]])
                  []
                  (Tactic.tacticHave_
                   "have"
                   (Term.haveDecl
                    (Term.haveIdDecl
                     []
                     []
                     ":="
                     (Term.app
                      (Term.proj (Term.proj `hpi "." (fieldIdx "2")) "." (fieldIdx "2"))
                      [(Term.anonymousCtor "⟨" [`k "," (num "1")] "⟩")
                       (Term.anonymousCtor "⟨" [`k "," («term-_» "-" (num "1"))] "⟩")
                       (Term.anonymousCtor
                        "⟨"
                        [`y
                         ","
                         (Term.byTactic
                          "by"
                          (Tactic.tacticSeq
                           (Tactic.tacticSeq1Indented
                            [(Tactic.«tactic_<;>_»
                              (Tactic.rwSeq
                               "rw"
                               []
                               (Tactic.rwRuleSeq
                                "["
                                [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `hkmul)
                                 ","
                                 (Tactic.rwRule
                                  [(patternIgnore (token.«← » "←"))]
                                  (Term.app `Nat.cast_mul [`p]))
                                 ","
                                 (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `hy)]
                                "]")
                               [])
                              "<;>"
                              (Tactic.simp "simp" [] [] [] [] []))])))]
                        "⟩")]))))
                  []
                  (Mathlib.Tactic.clearAuxDecl "clear_aux_decl")
                  []
                  (Mathlib.Tactic.Tauto.tauto "tauto" [])])))))])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`hp1]
        []
        "=>"
        (Term.app
         `by_contradiction
         [(Term.fun
           "fun"
           (Term.basicFun
            [`hp3]
            [(Term.typeSpec ":" («term_≠_» («term_%_» `p "%" (num "4")) "≠" (num "3")))]
            "=>"
            (Term.byTactic
             "by"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(Tactic.tacticHave_
                 "have"
                 (Term.haveDecl
                  (Term.haveIdDecl
                   [`hp41 []]
                   [(Term.typeSpec ":" («term_=_» («term_%_» `p "%" (num "4")) "=" (num "1")))]
                   ":="
                   (Term.byTactic
                    "by"
                    (Tactic.tacticSeq
                     (Tactic.tacticSeq1Indented
                      [(Tactic.rwSeq
                        "rw"
                        []
                        (Tactic.rwRuleSeq
                         "["
                         [(Tactic.rwRule
                           [(patternIgnore (token.«← » "←"))]
                           (Term.app `Nat.mod_mul_left_mod [`p (num "2") (num "2")]))
                          ","
                          (Tactic.rwRule
                           []
                           (Term.show
                            "show"
                            («term_=_» («term_*_» (num "2") "*" (num "2")) "=" (num "4"))
                            (Term.fromTerm "from" `rfl)))]
                         "]")
                        [(Tactic.location "at" (Tactic.locationHyp [`hp1] []))])
                       []
                       (Tactic.tacticHave_
                        "have"
                        (Term.haveDecl
                         (Term.haveIdDecl
                          []
                          []
                          ":="
                          (Term.app
                           `Nat.mod_lt
                           [`p
                            (Term.show
                             "show"
                             («term_<_» (num "0") "<" (num "4"))
                             (Term.byTactic'
                              "by"
                              (Tactic.tacticSeq
                               (Tactic.tacticSeq1Indented [(Tactic.decide "decide")]))))]))))
                       []
                       (Tactic.revert "revert" [`this `hp3 `hp1])
                       []
                       (Tactic.generalize
                        "generalize"
                        [(Tactic.generalizeArg [] («term_%_» `p "%" (num "4")) "=" `m)]
                        [])
                       ";"
                       (Tactic.decide! "decide!")]))))))
                []
                (Tactic.tacticLet_
                 "let"
                 (Term.letDecl
                  (Term.letPatDecl
                   (Term.anonymousCtor "⟨" [`k "," `hk] "⟩")
                   []
                   []
                   ":="
                   («term_<|_»
                    (Term.proj `Zmod.exists_sq_eq_neg_one_iff "." (fieldIdx "2"))
                    "<|"
                    (Term.byTactic
                     "by"
                     (Tactic.tacticSeq
                      (Tactic.tacticSeq1Indented
                       [(Tactic.«tactic_<;>_»
                         (Tactic.rwSeq
                          "rw"
                          []
                          (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `hp41)] "]")
                          [])
                         "<;>"
                         (Tactic.exact
                          "exact"
                          (Term.byTactic
                           "by"
                           (Tactic.tacticSeq
                            (Tactic.tacticSeq1Indented [(Tactic.decide "decide")])))))])))))))
                []
                (Std.Tactic.obtain
                 "obtain"
                 [(Std.Tactic.RCases.rcasesPatMed
                   [(Std.Tactic.RCases.rcasesPat.tuple
                     "⟨"
                     [(Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `k)])
                       [])
                      ","
                      (Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `k_lt_p)])
                       [])
                      ","
                      (Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                       [])]
                     "⟩")])]
                 [":"
                  («term∃_,_»
                   "∃"
                   (Lean.explicitBinders
                    [(Lean.bracketedExplicitBinders
                      "("
                      [(Lean.binderIdent `k')]
                      ":"
                      (termℕ "ℕ")
                      ")")
                     (Lean.bracketedExplicitBinders
                      "("
                      [(Lean.binderIdent `h)]
                      ":"
                      («term_<_» `k' "<" `p)
                      ")")])
                   ","
                   («term_=_»
                    (Term.typeAscription "(" `k' ":" [(Term.app `Zmod [`p])] ")")
                    "="
                    `k))]
                 [":="
                  [(Term.byTactic
                    "by"
                    (Tactic.tacticSeq
                     (Tactic.tacticSeq1Indented
                      [(Tactic.refine'
                        "refine'"
                        (Term.anonymousCtor
                         "⟨"
                         [`k.val "," `k.val_lt "," (Term.app `Zmod.nat_cast_zmod_val [`k])]
                         "⟩"))])))]])
                []
                (Tactic.tacticHave_
                 "have"
                 (Term.haveDecl
                  (Term.haveIdDecl
                   [`hpk []]
                   [(Term.typeSpec
                     ":"
                     («term_∣_» `p "∣" («term_+_» («term_^_» `k "^" (num "2")) "+" (num "1"))))]
                   ":="
                   (Term.byTactic
                    "by"
                    (Tactic.tacticSeq
                     (Tactic.tacticSeq1Indented
                      [(Tactic.rwSeq
                        "rw"
                        []
                        (Tactic.rwRuleSeq
                         "["
                         [(Tactic.rwRule [] `pow_two)
                          ","
                          (Tactic.rwRule
                           [(patternIgnore (token.«← » "←"))]
                           (Term.app `CharP.cast_eq_zero_iff [(Term.app `Zmod [`p]) `p]))
                          ","
                          (Tactic.rwRule [] `Nat.cast_add)
                          ","
                          (Tactic.rwRule [] `Nat.cast_mul)
                          ","
                          (Tactic.rwRule [] `Nat.cast_one)
                          ","
                          (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `hk)
                          ","
                          (Tactic.rwRule [] `add_left_neg)]
                         "]")
                        [])]))))))
                []
                (Tactic.tacticHave_
                 "have"
                 (Term.haveDecl
                  (Term.haveIdDecl
                   [`hkmul []]
                   [(Term.typeSpec
                     ":"
                     («term_=_»
                      (Term.typeAscription
                       "("
                       («term_+_» («term_^_» `k "^" (num "2")) "+" (num "1"))
                       ":"
                       [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
                       ")")
                      "="
                      («term_*_»
                       (Term.anonymousCtor "⟨" [`k "," (num "1")] "⟩")
                       "*"
                       (Term.anonymousCtor "⟨" [`k "," («term-_» "-" (num "1"))] "⟩"))))]
                   ":="
                   (Term.byTactic
                    "by"
                    (Tactic.tacticSeq
                     (Tactic.tacticSeq1Indented
                      [(Tactic.simp
                        "simp"
                        []
                        []
                        []
                        ["["
                         [(Tactic.simpLemma [] [] `sq) "," (Tactic.simpLemma [] [] `Zsqrtd.ext)]
                         "]"]
                        [])]))))))
                []
                (Tactic.tacticHave_
                 "have"
                 (Term.haveDecl
                  (Term.haveIdDecl
                   [`hpne1 []]
                   [(Term.typeSpec ":" («term_≠_» `p "≠" (num "1")))]
                   ":="
                   (Term.app
                    `ne_of_gt
                    [(Term.proj (Term.proj `hp "." (fieldIdx "1")) "." `one_lt)]))))
                []
                (Tactic.tacticHave_
                 "have"
                 (Term.haveDecl
                  (Term.haveIdDecl
                   [`hkltp []]
                   [(Term.typeSpec
                     ":"
                     («term_<_»
                      («term_+_» (num "1") "+" («term_*_» `k "*" `k))
                      "<"
                      («term_*_» `p "*" `p)))]
                   ":="
                   (calc
                    "calc"
                    (calcStep
                     («term_≤_»
                      («term_+_» (num "1") "+" («term_*_» `k "*" `k))
                      "≤"
                      («term_+_» `k "+" («term_*_» `k "*" `k)))
                     ":="
                     (Term.app
                      `add_le_add_right
                      [(Term.app
                        `Nat.pos_of_ne_zero
                        [(Term.fun
                          "fun"
                          (Term.basicFun
                           [`hk0]
                           []
                           "=>"
                           (Term.byTactic
                            "by"
                            (Tactic.tacticSeq
                             (Tactic.tacticSeq1Indented
                              [(Tactic.«tactic_<;>_»
                                (Mathlib.Tactic.clearAuxDecl "clear_aux_decl")
                                "<;>"
                                (Tactic.simpAll
                                 "simp_all"
                                 []
                                 []
                                 []
                                 ["[" [(Tactic.simpLemma [] [] `pow_succ')] "]"]))])))))])
                       (Term.hole "_")]))
                    [(calcStep
                      («term_=_»
                       (Term.hole "_")
                       "="
                       («term_*_» `k "*" («term_+_» `k "+" (num "1"))))
                      ":="
                      (Term.byTactic
                       "by"
                       (Tactic.tacticSeq
                        (Tactic.tacticSeq1Indented
                         [(Tactic.simp
                           "simp"
                           []
                           []
                           []
                           ["["
                            [(Tactic.simpLemma [] [] `add_comm)
                             ","
                             (Tactic.simpLemma [] [] `mul_add)]
                            "]"]
                           [])]))))
                     (calcStep
                      («term_<_» (Term.hole "_") "<" («term_*_» `p "*" `p))
                      ":="
                      (Term.app
                       `mul_lt_mul
                       [`k_lt_p
                        `k_lt_p
                        (Term.app `Nat.succ_pos [(Term.hole "_")])
                        (Term.app `Nat.zero_le [(Term.hole "_")])]))]))))
                []
                (Tactic.tacticHave_
                 "have"
                 (Term.haveDecl
                  (Term.haveIdDecl
                   [`hpk₁ []]
                   [(Term.typeSpec
                     ":"
                     («term¬_»
                      "¬"
                      («term_∣_»
                       (Term.typeAscription
                        "("
                        `p
                        ":"
                        [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
                        ")")
                       "∣"
                       (Term.anonymousCtor "⟨" [`k "," («term-_» "-" (num "1"))] "⟩"))))]
                   ":="
                   (Term.fun
                    "fun"
                    (Term.basicFun
                     [(Term.anonymousCtor "⟨" [`x "," `hx] "⟩")]
                     []
                     "=>"
                     («term_<|_»
                      (Term.app
                       `lt_irrefl
                       [(Term.proj
                         (Term.proj
                          (Term.typeAscription
                           "("
                           («term_*_» `p "*" `x)
                           ":"
                           [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
                           ")")
                          "."
                          `norm)
                         "."
                         `natAbs)])
                      "<|"
                      (calc
                       "calc"
                       (calcStep
                        («term_=_»
                         (Term.proj
                          (Term.app
                           `norm
                           [(Term.typeAscription
                             "("
                             («term_*_» `p "*" `x)
                             ":"
                             [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
                             ")")])
                          "."
                          `natAbs)
                         "="
                         (Term.proj
                          (Term.app
                           `Zsqrtd.norm
                           [(Term.anonymousCtor "⟨" [`k "," («term-_» "-" (num "1"))] "⟩")])
                          "."
                          `natAbs))
                        ":="
                        (Term.byTactic
                         "by"
                         (Tactic.tacticSeq
                          (Tactic.tacticSeq1Indented
                           [(Tactic.rwSeq
                             "rw"
                             []
                             (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `hx)] "]")
                             [])]))))
                       [(calcStep
                         («term_<_»
                          (Term.hole "_")
                          "<"
                          (Term.proj
                           (Term.app
                            `norm
                            [(Term.typeAscription
                              "("
                              `p
                              ":"
                              [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
                              ")")])
                           "."
                           `natAbs))
                         ":="
                         (Term.byTactic
                          "by"
                          (Tactic.tacticSeq
                           (Tactic.tacticSeq1Indented
                            [(Std.Tactic.Simpa.simpa
                              "simpa"
                              []
                              []
                              (Std.Tactic.Simpa.simpaArgsRest
                               []
                               []
                               []
                               [(Tactic.simpArgs
                                 "["
                                 [(Tactic.simpLemma [] [] `add_comm)
                                  ","
                                  (Tactic.simpLemma [] [] `Zsqrtd.norm)]
                                 "]")]
                               ["using" `hkltp]))]))))
                        (calcStep
                         («term_≤_»
                          (Term.hole "_")
                          "≤"
                          (Term.proj
                           (Term.app
                            `norm
                            [(Term.typeAscription
                              "("
                              («term_*_» `p "*" `x)
                              ":"
                              [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
                              ")")])
                           "."
                           `natAbs))
                         ":="
                         (Term.app
                          `norm_le_norm_mul_left
                          [(Term.hole "_")
                           (Term.fun
                            "fun"
                            (Term.basicFun
                             [`hx0]
                             []
                             "=>"
                             («term_<|_»
                              (Term.show
                               "show"
                               («term_≠_»
                                (Term.typeAscription
                                 "("
                                 («term-_» "-" (num "1"))
                                 ":"
                                 [(termℤ "ℤ")]
                                 ")")
                                "≠"
                                (num "0"))
                               (Term.byTactic'
                                "by"
                                (Tactic.tacticSeq
                                 (Tactic.tacticSeq1Indented [(Tactic.decide "decide")]))))
                              "<|"
                              (Term.byTactic
                               "by"
                               (Tactic.tacticSeq
                                (Tactic.tacticSeq1Indented
                                 [(Std.Tactic.Simpa.simpa
                                   "simpa"
                                   []
                                   []
                                   (Std.Tactic.Simpa.simpaArgsRest
                                    []
                                    []
                                    []
                                    [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `hx0)] "]")]
                                    ["using"
                                     (Term.app `congr_arg [`Zsqrtd.im `hx])]))]))))))]))])))))))
                []
                (Tactic.tacticHave_
                 "have"
                 (Term.haveDecl
                  (Term.haveIdDecl
                   [`hpk₂ []]
                   [(Term.typeSpec
                     ":"
                     («term¬_»
                      "¬"
                      («term_∣_»
                       (Term.typeAscription
                        "("
                        `p
                        ":"
                        [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
                        ")")
                       "∣"
                       (Term.anonymousCtor "⟨" [`k "," (num "1")] "⟩"))))]
                   ":="
                   (Term.fun
                    "fun"
                    (Term.basicFun
                     [(Term.anonymousCtor "⟨" [`x "," `hx] "⟩")]
                     []
                     "=>"
                     («term_<|_»
                      (Term.app
                       `lt_irrefl
                       [(Term.proj
                         (Term.proj
                          (Term.typeAscription
                           "("
                           («term_*_» `p "*" `x)
                           ":"
                           [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
                           ")")
                          "."
                          `norm)
                         "."
                         `natAbs)])
                      "<|"
                      (calc
                       "calc"
                       (calcStep
                        («term_=_»
                         (Term.proj
                          (Term.app
                           `norm
                           [(Term.typeAscription
                             "("
                             («term_*_» `p "*" `x)
                             ":"
                             [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
                             ")")])
                          "."
                          `natAbs)
                         "="
                         (Term.proj
                          (Term.app `Zsqrtd.norm [(Term.anonymousCtor "⟨" [`k "," (num "1")] "⟩")])
                          "."
                          `natAbs))
                        ":="
                        (Term.byTactic
                         "by"
                         (Tactic.tacticSeq
                          (Tactic.tacticSeq1Indented
                           [(Tactic.rwSeq
                             "rw"
                             []
                             (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `hx)] "]")
                             [])]))))
                       [(calcStep
                         («term_<_»
                          (Term.hole "_")
                          "<"
                          (Term.proj
                           (Term.app
                            `norm
                            [(Term.typeAscription
                              "("
                              `p
                              ":"
                              [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
                              ")")])
                           "."
                           `natAbs))
                         ":="
                         (Term.byTactic
                          "by"
                          (Tactic.tacticSeq
                           (Tactic.tacticSeq1Indented
                            [(Std.Tactic.Simpa.simpa
                              "simpa"
                              []
                              []
                              (Std.Tactic.Simpa.simpaArgsRest
                               []
                               []
                               []
                               [(Tactic.simpArgs
                                 "["
                                 [(Tactic.simpLemma [] [] `add_comm)
                                  ","
                                  (Tactic.simpLemma [] [] `Zsqrtd.norm)]
                                 "]")]
                               ["using" `hkltp]))]))))
                        (calcStep
                         («term_≤_»
                          (Term.hole "_")
                          "≤"
                          (Term.proj
                           (Term.app
                            `norm
                            [(Term.typeAscription
                              "("
                              («term_*_» `p "*" `x)
                              ":"
                              [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
                              ")")])
                           "."
                           `natAbs))
                         ":="
                         (Term.app
                          `norm_le_norm_mul_left
                          [(Term.hole "_")
                           (Term.fun
                            "fun"
                            (Term.basicFun
                             [`hx0]
                             []
                             "=>"
                             («term_<|_»
                              (Term.show
                               "show"
                               («term_≠_»
                                (Term.typeAscription "(" (num "1") ":" [(termℤ "ℤ")] ")")
                                "≠"
                                (num "0"))
                               (Term.byTactic'
                                "by"
                                (Tactic.tacticSeq
                                 (Tactic.tacticSeq1Indented [(Tactic.decide "decide")]))))
                              "<|"
                              (Term.byTactic
                               "by"
                               (Tactic.tacticSeq
                                (Tactic.tacticSeq1Indented
                                 [(Std.Tactic.Simpa.simpa
                                   "simpa"
                                   []
                                   []
                                   (Std.Tactic.Simpa.simpaArgsRest
                                    []
                                    []
                                    []
                                    [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `hx0)] "]")]
                                    ["using"
                                     (Term.app `congr_arg [`Zsqrtd.im `hx])]))]))))))]))])))))))
                []
                (Tactic.tacticHave_
                 "have"
                 (Term.haveDecl
                  (Term.haveIdDecl
                   [`hpu []]
                   [(Term.typeSpec
                     ":"
                     («term¬_»
                      "¬"
                      (Term.app
                       `IsUnit
                       [(Term.typeAscription
                         "("
                         `p
                         ":"
                         [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
                         ")")])))]
                   ":="
                   (Term.app
                    `mt
                    [(Term.proj `norm_eq_one_iff "." (fieldIdx "2"))
                     (Term.byTactic
                      "by"
                      (Tactic.tacticSeq
                       (Tactic.tacticSeq1Indented
                        [(Tactic.«tactic_<;>_»
                          (Tactic.rwSeq
                           "rw"
                           []
                           (Tactic.rwRuleSeq
                            "["
                            [(Tactic.rwRule [] `norm_nat_cast)
                             ","
                             (Tactic.rwRule [] `Int.natAbs_mul)
                             ","
                             (Tactic.rwRule [] `Nat.mul_eq_one_iff)]
                            "]")
                           [])
                          "<;>"
                          (Tactic.exact
                           "exact"
                           (Term.fun
                            "fun"
                            (Term.basicFun
                             [`h]
                             []
                             "=>"
                             (Term.app
                              (Term.proj
                               (Term.app
                                `ne_of_lt
                                [(Term.proj (Term.proj `hp "." (fieldIdx "1")) "." `one_lt)])
                               "."
                               `symm)
                              [(Term.proj `h "." (fieldIdx "1"))])))))])))]))))
                []
                (Std.Tactic.obtain
                 "obtain"
                 [(Std.Tactic.RCases.rcasesPatMed
                   [(Std.Tactic.RCases.rcasesPat.tuple
                     "⟨"
                     [(Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `y)])
                       [])
                      ","
                      (Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hy)])
                       [])]
                     "⟩")])]
                 []
                 [":=" [`hpk]])
                []
                (Tactic.tacticHave_
                 "have"
                 (Term.haveDecl
                  (Term.haveIdDecl
                   []
                   []
                   ":="
                   (Term.app
                    (Term.proj (Term.proj `hpi "." (fieldIdx "2")) "." (fieldIdx "2"))
                    [(Term.anonymousCtor "⟨" [`k "," (num "1")] "⟩")
                     (Term.anonymousCtor "⟨" [`k "," («term-_» "-" (num "1"))] "⟩")
                     (Term.anonymousCtor
                      "⟨"
                      [`y
                       ","
                       (Term.byTactic
                        "by"
                        (Tactic.tacticSeq
                         (Tactic.tacticSeq1Indented
                          [(Tactic.«tactic_<;>_»
                            (Tactic.rwSeq
                             "rw"
                             []
                             (Tactic.rwRuleSeq
                              "["
                              [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `hkmul)
                               ","
                               (Tactic.rwRule
                                [(patternIgnore (token.«← » "←"))]
                                (Term.app `Nat.cast_mul [`p]))
                               ","
                               (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `hy)]
                              "]")
                             [])
                            "<;>"
                            (Tactic.simp "simp" [] [] [] [] []))])))]
                      "⟩")]))))
                []
                (Mathlib.Tactic.clearAuxDecl "clear_aux_decl")
                []
                (Mathlib.Tactic.Tauto.tauto "tauto" [])])))))])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `by_contradiction
       [(Term.fun
         "fun"
         (Term.basicFun
          [`hp3]
          [(Term.typeSpec ":" («term_≠_» («term_%_» `p "%" (num "4")) "≠" (num "3")))]
          "=>"
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(Tactic.tacticHave_
               "have"
               (Term.haveDecl
                (Term.haveIdDecl
                 [`hp41 []]
                 [(Term.typeSpec ":" («term_=_» («term_%_» `p "%" (num "4")) "=" (num "1")))]
                 ":="
                 (Term.byTactic
                  "by"
                  (Tactic.tacticSeq
                   (Tactic.tacticSeq1Indented
                    [(Tactic.rwSeq
                      "rw"
                      []
                      (Tactic.rwRuleSeq
                       "["
                       [(Tactic.rwRule
                         [(patternIgnore (token.«← » "←"))]
                         (Term.app `Nat.mod_mul_left_mod [`p (num "2") (num "2")]))
                        ","
                        (Tactic.rwRule
                         []
                         (Term.show
                          "show"
                          («term_=_» («term_*_» (num "2") "*" (num "2")) "=" (num "4"))
                          (Term.fromTerm "from" `rfl)))]
                       "]")
                      [(Tactic.location "at" (Tactic.locationHyp [`hp1] []))])
                     []
                     (Tactic.tacticHave_
                      "have"
                      (Term.haveDecl
                       (Term.haveIdDecl
                        []
                        []
                        ":="
                        (Term.app
                         `Nat.mod_lt
                         [`p
                          (Term.show
                           "show"
                           («term_<_» (num "0") "<" (num "4"))
                           (Term.byTactic'
                            "by"
                            (Tactic.tacticSeq
                             (Tactic.tacticSeq1Indented [(Tactic.decide "decide")]))))]))))
                     []
                     (Tactic.revert "revert" [`this `hp3 `hp1])
                     []
                     (Tactic.generalize
                      "generalize"
                      [(Tactic.generalizeArg [] («term_%_» `p "%" (num "4")) "=" `m)]
                      [])
                     ";"
                     (Tactic.decide! "decide!")]))))))
              []
              (Tactic.tacticLet_
               "let"
               (Term.letDecl
                (Term.letPatDecl
                 (Term.anonymousCtor "⟨" [`k "," `hk] "⟩")
                 []
                 []
                 ":="
                 («term_<|_»
                  (Term.proj `Zmod.exists_sq_eq_neg_one_iff "." (fieldIdx "2"))
                  "<|"
                  (Term.byTactic
                   "by"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented
                     [(Tactic.«tactic_<;>_»
                       (Tactic.rwSeq
                        "rw"
                        []
                        (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `hp41)] "]")
                        [])
                       "<;>"
                       (Tactic.exact
                        "exact"
                        (Term.byTactic
                         "by"
                         (Tactic.tacticSeq
                          (Tactic.tacticSeq1Indented [(Tactic.decide "decide")])))))])))))))
              []
              (Std.Tactic.obtain
               "obtain"
               [(Std.Tactic.RCases.rcasesPatMed
                 [(Std.Tactic.RCases.rcasesPat.tuple
                   "⟨"
                   [(Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `k)])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `k_lt_p)])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                     [])]
                   "⟩")])]
               [":"
                («term∃_,_»
                 "∃"
                 (Lean.explicitBinders
                  [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `k')] ":" (termℕ "ℕ") ")")
                   (Lean.bracketedExplicitBinders
                    "("
                    [(Lean.binderIdent `h)]
                    ":"
                    («term_<_» `k' "<" `p)
                    ")")])
                 ","
                 («term_=_» (Term.typeAscription "(" `k' ":" [(Term.app `Zmod [`p])] ")") "=" `k))]
               [":="
                [(Term.byTactic
                  "by"
                  (Tactic.tacticSeq
                   (Tactic.tacticSeq1Indented
                    [(Tactic.refine'
                      "refine'"
                      (Term.anonymousCtor
                       "⟨"
                       [`k.val "," `k.val_lt "," (Term.app `Zmod.nat_cast_zmod_val [`k])]
                       "⟩"))])))]])
              []
              (Tactic.tacticHave_
               "have"
               (Term.haveDecl
                (Term.haveIdDecl
                 [`hpk []]
                 [(Term.typeSpec
                   ":"
                   («term_∣_» `p "∣" («term_+_» («term_^_» `k "^" (num "2")) "+" (num "1"))))]
                 ":="
                 (Term.byTactic
                  "by"
                  (Tactic.tacticSeq
                   (Tactic.tacticSeq1Indented
                    [(Tactic.rwSeq
                      "rw"
                      []
                      (Tactic.rwRuleSeq
                       "["
                       [(Tactic.rwRule [] `pow_two)
                        ","
                        (Tactic.rwRule
                         [(patternIgnore (token.«← » "←"))]
                         (Term.app `CharP.cast_eq_zero_iff [(Term.app `Zmod [`p]) `p]))
                        ","
                        (Tactic.rwRule [] `Nat.cast_add)
                        ","
                        (Tactic.rwRule [] `Nat.cast_mul)
                        ","
                        (Tactic.rwRule [] `Nat.cast_one)
                        ","
                        (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `hk)
                        ","
                        (Tactic.rwRule [] `add_left_neg)]
                       "]")
                      [])]))))))
              []
              (Tactic.tacticHave_
               "have"
               (Term.haveDecl
                (Term.haveIdDecl
                 [`hkmul []]
                 [(Term.typeSpec
                   ":"
                   («term_=_»
                    (Term.typeAscription
                     "("
                     («term_+_» («term_^_» `k "^" (num "2")) "+" (num "1"))
                     ":"
                     [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
                     ")")
                    "="
                    («term_*_»
                     (Term.anonymousCtor "⟨" [`k "," (num "1")] "⟩")
                     "*"
                     (Term.anonymousCtor "⟨" [`k "," («term-_» "-" (num "1"))] "⟩"))))]
                 ":="
                 (Term.byTactic
                  "by"
                  (Tactic.tacticSeq
                   (Tactic.tacticSeq1Indented
                    [(Tactic.simp
                      "simp"
                      []
                      []
                      []
                      ["["
                       [(Tactic.simpLemma [] [] `sq) "," (Tactic.simpLemma [] [] `Zsqrtd.ext)]
                       "]"]
                      [])]))))))
              []
              (Tactic.tacticHave_
               "have"
               (Term.haveDecl
                (Term.haveIdDecl
                 [`hpne1 []]
                 [(Term.typeSpec ":" («term_≠_» `p "≠" (num "1")))]
                 ":="
                 (Term.app
                  `ne_of_gt
                  [(Term.proj (Term.proj `hp "." (fieldIdx "1")) "." `one_lt)]))))
              []
              (Tactic.tacticHave_
               "have"
               (Term.haveDecl
                (Term.haveIdDecl
                 [`hkltp []]
                 [(Term.typeSpec
                   ":"
                   («term_<_»
                    («term_+_» (num "1") "+" («term_*_» `k "*" `k))
                    "<"
                    («term_*_» `p "*" `p)))]
                 ":="
                 (calc
                  "calc"
                  (calcStep
                   («term_≤_»
                    («term_+_» (num "1") "+" («term_*_» `k "*" `k))
                    "≤"
                    («term_+_» `k "+" («term_*_» `k "*" `k)))
                   ":="
                   (Term.app
                    `add_le_add_right
                    [(Term.app
                      `Nat.pos_of_ne_zero
                      [(Term.fun
                        "fun"
                        (Term.basicFun
                         [`hk0]
                         []
                         "=>"
                         (Term.byTactic
                          "by"
                          (Tactic.tacticSeq
                           (Tactic.tacticSeq1Indented
                            [(Tactic.«tactic_<;>_»
                              (Mathlib.Tactic.clearAuxDecl "clear_aux_decl")
                              "<;>"
                              (Tactic.simpAll
                               "simp_all"
                               []
                               []
                               []
                               ["[" [(Tactic.simpLemma [] [] `pow_succ')] "]"]))])))))])
                     (Term.hole "_")]))
                  [(calcStep
                    («term_=_» (Term.hole "_") "=" («term_*_» `k "*" («term_+_» `k "+" (num "1"))))
                    ":="
                    (Term.byTactic
                     "by"
                     (Tactic.tacticSeq
                      (Tactic.tacticSeq1Indented
                       [(Tactic.simp
                         "simp"
                         []
                         []
                         []
                         ["["
                          [(Tactic.simpLemma [] [] `add_comm) "," (Tactic.simpLemma [] [] `mul_add)]
                          "]"]
                         [])]))))
                   (calcStep
                    («term_<_» (Term.hole "_") "<" («term_*_» `p "*" `p))
                    ":="
                    (Term.app
                     `mul_lt_mul
                     [`k_lt_p
                      `k_lt_p
                      (Term.app `Nat.succ_pos [(Term.hole "_")])
                      (Term.app `Nat.zero_le [(Term.hole "_")])]))]))))
              []
              (Tactic.tacticHave_
               "have"
               (Term.haveDecl
                (Term.haveIdDecl
                 [`hpk₁ []]
                 [(Term.typeSpec
                   ":"
                   («term¬_»
                    "¬"
                    («term_∣_»
                     (Term.typeAscription
                      "("
                      `p
                      ":"
                      [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
                      ")")
                     "∣"
                     (Term.anonymousCtor "⟨" [`k "," («term-_» "-" (num "1"))] "⟩"))))]
                 ":="
                 (Term.fun
                  "fun"
                  (Term.basicFun
                   [(Term.anonymousCtor "⟨" [`x "," `hx] "⟩")]
                   []
                   "=>"
                   («term_<|_»
                    (Term.app
                     `lt_irrefl
                     [(Term.proj
                       (Term.proj
                        (Term.typeAscription
                         "("
                         («term_*_» `p "*" `x)
                         ":"
                         [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
                         ")")
                        "."
                        `norm)
                       "."
                       `natAbs)])
                    "<|"
                    (calc
                     "calc"
                     (calcStep
                      («term_=_»
                       (Term.proj
                        (Term.app
                         `norm
                         [(Term.typeAscription
                           "("
                           («term_*_» `p "*" `x)
                           ":"
                           [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
                           ")")])
                        "."
                        `natAbs)
                       "="
                       (Term.proj
                        (Term.app
                         `Zsqrtd.norm
                         [(Term.anonymousCtor "⟨" [`k "," («term-_» "-" (num "1"))] "⟩")])
                        "."
                        `natAbs))
                      ":="
                      (Term.byTactic
                       "by"
                       (Tactic.tacticSeq
                        (Tactic.tacticSeq1Indented
                         [(Tactic.rwSeq
                           "rw"
                           []
                           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `hx)] "]")
                           [])]))))
                     [(calcStep
                       («term_<_»
                        (Term.hole "_")
                        "<"
                        (Term.proj
                         (Term.app
                          `norm
                          [(Term.typeAscription
                            "("
                            `p
                            ":"
                            [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
                            ")")])
                         "."
                         `natAbs))
                       ":="
                       (Term.byTactic
                        "by"
                        (Tactic.tacticSeq
                         (Tactic.tacticSeq1Indented
                          [(Std.Tactic.Simpa.simpa
                            "simpa"
                            []
                            []
                            (Std.Tactic.Simpa.simpaArgsRest
                             []
                             []
                             []
                             [(Tactic.simpArgs
                               "["
                               [(Tactic.simpLemma [] [] `add_comm)
                                ","
                                (Tactic.simpLemma [] [] `Zsqrtd.norm)]
                               "]")]
                             ["using" `hkltp]))]))))
                      (calcStep
                       («term_≤_»
                        (Term.hole "_")
                        "≤"
                        (Term.proj
                         (Term.app
                          `norm
                          [(Term.typeAscription
                            "("
                            («term_*_» `p "*" `x)
                            ":"
                            [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
                            ")")])
                         "."
                         `natAbs))
                       ":="
                       (Term.app
                        `norm_le_norm_mul_left
                        [(Term.hole "_")
                         (Term.fun
                          "fun"
                          (Term.basicFun
                           [`hx0]
                           []
                           "=>"
                           («term_<|_»
                            (Term.show
                             "show"
                             («term_≠_»
                              (Term.typeAscription
                               "("
                               («term-_» "-" (num "1"))
                               ":"
                               [(termℤ "ℤ")]
                               ")")
                              "≠"
                              (num "0"))
                             (Term.byTactic'
                              "by"
                              (Tactic.tacticSeq
                               (Tactic.tacticSeq1Indented [(Tactic.decide "decide")]))))
                            "<|"
                            (Term.byTactic
                             "by"
                             (Tactic.tacticSeq
                              (Tactic.tacticSeq1Indented
                               [(Std.Tactic.Simpa.simpa
                                 "simpa"
                                 []
                                 []
                                 (Std.Tactic.Simpa.simpaArgsRest
                                  []
                                  []
                                  []
                                  [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `hx0)] "]")]
                                  ["using"
                                   (Term.app `congr_arg [`Zsqrtd.im `hx])]))]))))))]))])))))))
              []
              (Tactic.tacticHave_
               "have"
               (Term.haveDecl
                (Term.haveIdDecl
                 [`hpk₂ []]
                 [(Term.typeSpec
                   ":"
                   («term¬_»
                    "¬"
                    («term_∣_»
                     (Term.typeAscription
                      "("
                      `p
                      ":"
                      [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
                      ")")
                     "∣"
                     (Term.anonymousCtor "⟨" [`k "," (num "1")] "⟩"))))]
                 ":="
                 (Term.fun
                  "fun"
                  (Term.basicFun
                   [(Term.anonymousCtor "⟨" [`x "," `hx] "⟩")]
                   []
                   "=>"
                   («term_<|_»
                    (Term.app
                     `lt_irrefl
                     [(Term.proj
                       (Term.proj
                        (Term.typeAscription
                         "("
                         («term_*_» `p "*" `x)
                         ":"
                         [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
                         ")")
                        "."
                        `norm)
                       "."
                       `natAbs)])
                    "<|"
                    (calc
                     "calc"
                     (calcStep
                      («term_=_»
                       (Term.proj
                        (Term.app
                         `norm
                         [(Term.typeAscription
                           "("
                           («term_*_» `p "*" `x)
                           ":"
                           [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
                           ")")])
                        "."
                        `natAbs)
                       "="
                       (Term.proj
                        (Term.app `Zsqrtd.norm [(Term.anonymousCtor "⟨" [`k "," (num "1")] "⟩")])
                        "."
                        `natAbs))
                      ":="
                      (Term.byTactic
                       "by"
                       (Tactic.tacticSeq
                        (Tactic.tacticSeq1Indented
                         [(Tactic.rwSeq
                           "rw"
                           []
                           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `hx)] "]")
                           [])]))))
                     [(calcStep
                       («term_<_»
                        (Term.hole "_")
                        "<"
                        (Term.proj
                         (Term.app
                          `norm
                          [(Term.typeAscription
                            "("
                            `p
                            ":"
                            [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
                            ")")])
                         "."
                         `natAbs))
                       ":="
                       (Term.byTactic
                        "by"
                        (Tactic.tacticSeq
                         (Tactic.tacticSeq1Indented
                          [(Std.Tactic.Simpa.simpa
                            "simpa"
                            []
                            []
                            (Std.Tactic.Simpa.simpaArgsRest
                             []
                             []
                             []
                             [(Tactic.simpArgs
                               "["
                               [(Tactic.simpLemma [] [] `add_comm)
                                ","
                                (Tactic.simpLemma [] [] `Zsqrtd.norm)]
                               "]")]
                             ["using" `hkltp]))]))))
                      (calcStep
                       («term_≤_»
                        (Term.hole "_")
                        "≤"
                        (Term.proj
                         (Term.app
                          `norm
                          [(Term.typeAscription
                            "("
                            («term_*_» `p "*" `x)
                            ":"
                            [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
                            ")")])
                         "."
                         `natAbs))
                       ":="
                       (Term.app
                        `norm_le_norm_mul_left
                        [(Term.hole "_")
                         (Term.fun
                          "fun"
                          (Term.basicFun
                           [`hx0]
                           []
                           "=>"
                           («term_<|_»
                            (Term.show
                             "show"
                             («term_≠_»
                              (Term.typeAscription "(" (num "1") ":" [(termℤ "ℤ")] ")")
                              "≠"
                              (num "0"))
                             (Term.byTactic'
                              "by"
                              (Tactic.tacticSeq
                               (Tactic.tacticSeq1Indented [(Tactic.decide "decide")]))))
                            "<|"
                            (Term.byTactic
                             "by"
                             (Tactic.tacticSeq
                              (Tactic.tacticSeq1Indented
                               [(Std.Tactic.Simpa.simpa
                                 "simpa"
                                 []
                                 []
                                 (Std.Tactic.Simpa.simpaArgsRest
                                  []
                                  []
                                  []
                                  [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `hx0)] "]")]
                                  ["using"
                                   (Term.app `congr_arg [`Zsqrtd.im `hx])]))]))))))]))])))))))
              []
              (Tactic.tacticHave_
               "have"
               (Term.haveDecl
                (Term.haveIdDecl
                 [`hpu []]
                 [(Term.typeSpec
                   ":"
                   («term¬_»
                    "¬"
                    (Term.app
                     `IsUnit
                     [(Term.typeAscription
                       "("
                       `p
                       ":"
                       [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
                       ")")])))]
                 ":="
                 (Term.app
                  `mt
                  [(Term.proj `norm_eq_one_iff "." (fieldIdx "2"))
                   (Term.byTactic
                    "by"
                    (Tactic.tacticSeq
                     (Tactic.tacticSeq1Indented
                      [(Tactic.«tactic_<;>_»
                        (Tactic.rwSeq
                         "rw"
                         []
                         (Tactic.rwRuleSeq
                          "["
                          [(Tactic.rwRule [] `norm_nat_cast)
                           ","
                           (Tactic.rwRule [] `Int.natAbs_mul)
                           ","
                           (Tactic.rwRule [] `Nat.mul_eq_one_iff)]
                          "]")
                         [])
                        "<;>"
                        (Tactic.exact
                         "exact"
                         (Term.fun
                          "fun"
                          (Term.basicFun
                           [`h]
                           []
                           "=>"
                           (Term.app
                            (Term.proj
                             (Term.app
                              `ne_of_lt
                              [(Term.proj (Term.proj `hp "." (fieldIdx "1")) "." `one_lt)])
                             "."
                             `symm)
                            [(Term.proj `h "." (fieldIdx "1"))])))))])))]))))
              []
              (Std.Tactic.obtain
               "obtain"
               [(Std.Tactic.RCases.rcasesPatMed
                 [(Std.Tactic.RCases.rcasesPat.tuple
                   "⟨"
                   [(Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `y)])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hy)])
                     [])]
                   "⟩")])]
               []
               [":=" [`hpk]])
              []
              (Tactic.tacticHave_
               "have"
               (Term.haveDecl
                (Term.haveIdDecl
                 []
                 []
                 ":="
                 (Term.app
                  (Term.proj (Term.proj `hpi "." (fieldIdx "2")) "." (fieldIdx "2"))
                  [(Term.anonymousCtor "⟨" [`k "," (num "1")] "⟩")
                   (Term.anonymousCtor "⟨" [`k "," («term-_» "-" (num "1"))] "⟩")
                   (Term.anonymousCtor
                    "⟨"
                    [`y
                     ","
                     (Term.byTactic
                      "by"
                      (Tactic.tacticSeq
                       (Tactic.tacticSeq1Indented
                        [(Tactic.«tactic_<;>_»
                          (Tactic.rwSeq
                           "rw"
                           []
                           (Tactic.rwRuleSeq
                            "["
                            [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `hkmul)
                             ","
                             (Tactic.rwRule
                              [(patternIgnore (token.«← » "←"))]
                              (Term.app `Nat.cast_mul [`p]))
                             ","
                             (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `hy)]
                            "]")
                           [])
                          "<;>"
                          (Tactic.simp "simp" [] [] [] [] []))])))]
                    "⟩")]))))
              []
              (Mathlib.Tactic.clearAuxDecl "clear_aux_decl")
              []
              (Mathlib.Tactic.Tauto.tauto "tauto" [])])))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`hp3]
        [(Term.typeSpec ":" («term_≠_» («term_%_» `p "%" (num "4")) "≠" (num "3")))]
        "=>"
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               [`hp41 []]
               [(Term.typeSpec ":" («term_=_» («term_%_» `p "%" (num "4")) "=" (num "1")))]
               ":="
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(Tactic.rwSeq
                    "rw"
                    []
                    (Tactic.rwRuleSeq
                     "["
                     [(Tactic.rwRule
                       [(patternIgnore (token.«← » "←"))]
                       (Term.app `Nat.mod_mul_left_mod [`p (num "2") (num "2")]))
                      ","
                      (Tactic.rwRule
                       []
                       (Term.show
                        "show"
                        («term_=_» («term_*_» (num "2") "*" (num "2")) "=" (num "4"))
                        (Term.fromTerm "from" `rfl)))]
                     "]")
                    [(Tactic.location "at" (Tactic.locationHyp [`hp1] []))])
                   []
                   (Tactic.tacticHave_
                    "have"
                    (Term.haveDecl
                     (Term.haveIdDecl
                      []
                      []
                      ":="
                      (Term.app
                       `Nat.mod_lt
                       [`p
                        (Term.show
                         "show"
                         («term_<_» (num "0") "<" (num "4"))
                         (Term.byTactic'
                          "by"
                          (Tactic.tacticSeq
                           (Tactic.tacticSeq1Indented [(Tactic.decide "decide")]))))]))))
                   []
                   (Tactic.revert "revert" [`this `hp3 `hp1])
                   []
                   (Tactic.generalize
                    "generalize"
                    [(Tactic.generalizeArg [] («term_%_» `p "%" (num "4")) "=" `m)]
                    [])
                   ";"
                   (Tactic.decide! "decide!")]))))))
            []
            (Tactic.tacticLet_
             "let"
             (Term.letDecl
              (Term.letPatDecl
               (Term.anonymousCtor "⟨" [`k "," `hk] "⟩")
               []
               []
               ":="
               («term_<|_»
                (Term.proj `Zmod.exists_sq_eq_neg_one_iff "." (fieldIdx "2"))
                "<|"
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(Tactic.«tactic_<;>_»
                     (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `hp41)] "]") [])
                     "<;>"
                     (Tactic.exact
                      "exact"
                      (Term.byTactic
                       "by"
                       (Tactic.tacticSeq
                        (Tactic.tacticSeq1Indented [(Tactic.decide "decide")])))))])))))))
            []
            (Std.Tactic.obtain
             "obtain"
             [(Std.Tactic.RCases.rcasesPatMed
               [(Std.Tactic.RCases.rcasesPat.tuple
                 "⟨"
                 [(Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `k)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `k_lt_p)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                   [])]
                 "⟩")])]
             [":"
              («term∃_,_»
               "∃"
               (Lean.explicitBinders
                [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `k')] ":" (termℕ "ℕ") ")")
                 (Lean.bracketedExplicitBinders
                  "("
                  [(Lean.binderIdent `h)]
                  ":"
                  («term_<_» `k' "<" `p)
                  ")")])
               ","
               («term_=_» (Term.typeAscription "(" `k' ":" [(Term.app `Zmod [`p])] ")") "=" `k))]
             [":="
              [(Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(Tactic.refine'
                    "refine'"
                    (Term.anonymousCtor
                     "⟨"
                     [`k.val "," `k.val_lt "," (Term.app `Zmod.nat_cast_zmod_val [`k])]
                     "⟩"))])))]])
            []
            (Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               [`hpk []]
               [(Term.typeSpec
                 ":"
                 («term_∣_» `p "∣" («term_+_» («term_^_» `k "^" (num "2")) "+" (num "1"))))]
               ":="
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(Tactic.rwSeq
                    "rw"
                    []
                    (Tactic.rwRuleSeq
                     "["
                     [(Tactic.rwRule [] `pow_two)
                      ","
                      (Tactic.rwRule
                       [(patternIgnore (token.«← » "←"))]
                       (Term.app `CharP.cast_eq_zero_iff [(Term.app `Zmod [`p]) `p]))
                      ","
                      (Tactic.rwRule [] `Nat.cast_add)
                      ","
                      (Tactic.rwRule [] `Nat.cast_mul)
                      ","
                      (Tactic.rwRule [] `Nat.cast_one)
                      ","
                      (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `hk)
                      ","
                      (Tactic.rwRule [] `add_left_neg)]
                     "]")
                    [])]))))))
            []
            (Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               [`hkmul []]
               [(Term.typeSpec
                 ":"
                 («term_=_»
                  (Term.typeAscription
                   "("
                   («term_+_» («term_^_» `k "^" (num "2")) "+" (num "1"))
                   ":"
                   [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
                   ")")
                  "="
                  («term_*_»
                   (Term.anonymousCtor "⟨" [`k "," (num "1")] "⟩")
                   "*"
                   (Term.anonymousCtor "⟨" [`k "," («term-_» "-" (num "1"))] "⟩"))))]
               ":="
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(Tactic.simp
                    "simp"
                    []
                    []
                    []
                    ["["
                     [(Tactic.simpLemma [] [] `sq) "," (Tactic.simpLemma [] [] `Zsqrtd.ext)]
                     "]"]
                    [])]))))))
            []
            (Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               [`hpne1 []]
               [(Term.typeSpec ":" («term_≠_» `p "≠" (num "1")))]
               ":="
               (Term.app `ne_of_gt [(Term.proj (Term.proj `hp "." (fieldIdx "1")) "." `one_lt)]))))
            []
            (Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               [`hkltp []]
               [(Term.typeSpec
                 ":"
                 («term_<_»
                  («term_+_» (num "1") "+" («term_*_» `k "*" `k))
                  "<"
                  («term_*_» `p "*" `p)))]
               ":="
               (calc
                "calc"
                (calcStep
                 («term_≤_»
                  («term_+_» (num "1") "+" («term_*_» `k "*" `k))
                  "≤"
                  («term_+_» `k "+" («term_*_» `k "*" `k)))
                 ":="
                 (Term.app
                  `add_le_add_right
                  [(Term.app
                    `Nat.pos_of_ne_zero
                    [(Term.fun
                      "fun"
                      (Term.basicFun
                       [`hk0]
                       []
                       "=>"
                       (Term.byTactic
                        "by"
                        (Tactic.tacticSeq
                         (Tactic.tacticSeq1Indented
                          [(Tactic.«tactic_<;>_»
                            (Mathlib.Tactic.clearAuxDecl "clear_aux_decl")
                            "<;>"
                            (Tactic.simpAll
                             "simp_all"
                             []
                             []
                             []
                             ["[" [(Tactic.simpLemma [] [] `pow_succ')] "]"]))])))))])
                   (Term.hole "_")]))
                [(calcStep
                  («term_=_» (Term.hole "_") "=" («term_*_» `k "*" («term_+_» `k "+" (num "1"))))
                  ":="
                  (Term.byTactic
                   "by"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented
                     [(Tactic.simp
                       "simp"
                       []
                       []
                       []
                       ["["
                        [(Tactic.simpLemma [] [] `add_comm) "," (Tactic.simpLemma [] [] `mul_add)]
                        "]"]
                       [])]))))
                 (calcStep
                  («term_<_» (Term.hole "_") "<" («term_*_» `p "*" `p))
                  ":="
                  (Term.app
                   `mul_lt_mul
                   [`k_lt_p
                    `k_lt_p
                    (Term.app `Nat.succ_pos [(Term.hole "_")])
                    (Term.app `Nat.zero_le [(Term.hole "_")])]))]))))
            []
            (Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               [`hpk₁ []]
               [(Term.typeSpec
                 ":"
                 («term¬_»
                  "¬"
                  («term_∣_»
                   (Term.typeAscription
                    "("
                    `p
                    ":"
                    [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
                    ")")
                   "∣"
                   (Term.anonymousCtor "⟨" [`k "," («term-_» "-" (num "1"))] "⟩"))))]
               ":="
               (Term.fun
                "fun"
                (Term.basicFun
                 [(Term.anonymousCtor "⟨" [`x "," `hx] "⟩")]
                 []
                 "=>"
                 («term_<|_»
                  (Term.app
                   `lt_irrefl
                   [(Term.proj
                     (Term.proj
                      (Term.typeAscription
                       "("
                       («term_*_» `p "*" `x)
                       ":"
                       [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
                       ")")
                      "."
                      `norm)
                     "."
                     `natAbs)])
                  "<|"
                  (calc
                   "calc"
                   (calcStep
                    («term_=_»
                     (Term.proj
                      (Term.app
                       `norm
                       [(Term.typeAscription
                         "("
                         («term_*_» `p "*" `x)
                         ":"
                         [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
                         ")")])
                      "."
                      `natAbs)
                     "="
                     (Term.proj
                      (Term.app
                       `Zsqrtd.norm
                       [(Term.anonymousCtor "⟨" [`k "," («term-_» "-" (num "1"))] "⟩")])
                      "."
                      `natAbs))
                    ":="
                    (Term.byTactic
                     "by"
                     (Tactic.tacticSeq
                      (Tactic.tacticSeq1Indented
                       [(Tactic.rwSeq
                         "rw"
                         []
                         (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `hx)] "]")
                         [])]))))
                   [(calcStep
                     («term_<_»
                      (Term.hole "_")
                      "<"
                      (Term.proj
                       (Term.app
                        `norm
                        [(Term.typeAscription
                          "("
                          `p
                          ":"
                          [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
                          ")")])
                       "."
                       `natAbs))
                     ":="
                     (Term.byTactic
                      "by"
                      (Tactic.tacticSeq
                       (Tactic.tacticSeq1Indented
                        [(Std.Tactic.Simpa.simpa
                          "simpa"
                          []
                          []
                          (Std.Tactic.Simpa.simpaArgsRest
                           []
                           []
                           []
                           [(Tactic.simpArgs
                             "["
                             [(Tactic.simpLemma [] [] `add_comm)
                              ","
                              (Tactic.simpLemma [] [] `Zsqrtd.norm)]
                             "]")]
                           ["using" `hkltp]))]))))
                    (calcStep
                     («term_≤_»
                      (Term.hole "_")
                      "≤"
                      (Term.proj
                       (Term.app
                        `norm
                        [(Term.typeAscription
                          "("
                          («term_*_» `p "*" `x)
                          ":"
                          [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
                          ")")])
                       "."
                       `natAbs))
                     ":="
                     (Term.app
                      `norm_le_norm_mul_left
                      [(Term.hole "_")
                       (Term.fun
                        "fun"
                        (Term.basicFun
                         [`hx0]
                         []
                         "=>"
                         («term_<|_»
                          (Term.show
                           "show"
                           («term_≠_»
                            (Term.typeAscription "(" («term-_» "-" (num "1")) ":" [(termℤ "ℤ")] ")")
                            "≠"
                            (num "0"))
                           (Term.byTactic'
                            "by"
                            (Tactic.tacticSeq
                             (Tactic.tacticSeq1Indented [(Tactic.decide "decide")]))))
                          "<|"
                          (Term.byTactic
                           "by"
                           (Tactic.tacticSeq
                            (Tactic.tacticSeq1Indented
                             [(Std.Tactic.Simpa.simpa
                               "simpa"
                               []
                               []
                               (Std.Tactic.Simpa.simpaArgsRest
                                []
                                []
                                []
                                [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `hx0)] "]")]
                                ["using" (Term.app `congr_arg [`Zsqrtd.im `hx])]))]))))))]))])))))))
            []
            (Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               [`hpk₂ []]
               [(Term.typeSpec
                 ":"
                 («term¬_»
                  "¬"
                  («term_∣_»
                   (Term.typeAscription
                    "("
                    `p
                    ":"
                    [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
                    ")")
                   "∣"
                   (Term.anonymousCtor "⟨" [`k "," (num "1")] "⟩"))))]
               ":="
               (Term.fun
                "fun"
                (Term.basicFun
                 [(Term.anonymousCtor "⟨" [`x "," `hx] "⟩")]
                 []
                 "=>"
                 («term_<|_»
                  (Term.app
                   `lt_irrefl
                   [(Term.proj
                     (Term.proj
                      (Term.typeAscription
                       "("
                       («term_*_» `p "*" `x)
                       ":"
                       [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
                       ")")
                      "."
                      `norm)
                     "."
                     `natAbs)])
                  "<|"
                  (calc
                   "calc"
                   (calcStep
                    («term_=_»
                     (Term.proj
                      (Term.app
                       `norm
                       [(Term.typeAscription
                         "("
                         («term_*_» `p "*" `x)
                         ":"
                         [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
                         ")")])
                      "."
                      `natAbs)
                     "="
                     (Term.proj
                      (Term.app `Zsqrtd.norm [(Term.anonymousCtor "⟨" [`k "," (num "1")] "⟩")])
                      "."
                      `natAbs))
                    ":="
                    (Term.byTactic
                     "by"
                     (Tactic.tacticSeq
                      (Tactic.tacticSeq1Indented
                       [(Tactic.rwSeq
                         "rw"
                         []
                         (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `hx)] "]")
                         [])]))))
                   [(calcStep
                     («term_<_»
                      (Term.hole "_")
                      "<"
                      (Term.proj
                       (Term.app
                        `norm
                        [(Term.typeAscription
                          "("
                          `p
                          ":"
                          [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
                          ")")])
                       "."
                       `natAbs))
                     ":="
                     (Term.byTactic
                      "by"
                      (Tactic.tacticSeq
                       (Tactic.tacticSeq1Indented
                        [(Std.Tactic.Simpa.simpa
                          "simpa"
                          []
                          []
                          (Std.Tactic.Simpa.simpaArgsRest
                           []
                           []
                           []
                           [(Tactic.simpArgs
                             "["
                             [(Tactic.simpLemma [] [] `add_comm)
                              ","
                              (Tactic.simpLemma [] [] `Zsqrtd.norm)]
                             "]")]
                           ["using" `hkltp]))]))))
                    (calcStep
                     («term_≤_»
                      (Term.hole "_")
                      "≤"
                      (Term.proj
                       (Term.app
                        `norm
                        [(Term.typeAscription
                          "("
                          («term_*_» `p "*" `x)
                          ":"
                          [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
                          ")")])
                       "."
                       `natAbs))
                     ":="
                     (Term.app
                      `norm_le_norm_mul_left
                      [(Term.hole "_")
                       (Term.fun
                        "fun"
                        (Term.basicFun
                         [`hx0]
                         []
                         "=>"
                         («term_<|_»
                          (Term.show
                           "show"
                           («term_≠_»
                            (Term.typeAscription "(" (num "1") ":" [(termℤ "ℤ")] ")")
                            "≠"
                            (num "0"))
                           (Term.byTactic'
                            "by"
                            (Tactic.tacticSeq
                             (Tactic.tacticSeq1Indented [(Tactic.decide "decide")]))))
                          "<|"
                          (Term.byTactic
                           "by"
                           (Tactic.tacticSeq
                            (Tactic.tacticSeq1Indented
                             [(Std.Tactic.Simpa.simpa
                               "simpa"
                               []
                               []
                               (Std.Tactic.Simpa.simpaArgsRest
                                []
                                []
                                []
                                [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `hx0)] "]")]
                                ["using" (Term.app `congr_arg [`Zsqrtd.im `hx])]))]))))))]))])))))))
            []
            (Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               [`hpu []]
               [(Term.typeSpec
                 ":"
                 («term¬_»
                  "¬"
                  (Term.app
                   `IsUnit
                   [(Term.typeAscription
                     "("
                     `p
                     ":"
                     [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
                     ")")])))]
               ":="
               (Term.app
                `mt
                [(Term.proj `norm_eq_one_iff "." (fieldIdx "2"))
                 (Term.byTactic
                  "by"
                  (Tactic.tacticSeq
                   (Tactic.tacticSeq1Indented
                    [(Tactic.«tactic_<;>_»
                      (Tactic.rwSeq
                       "rw"
                       []
                       (Tactic.rwRuleSeq
                        "["
                        [(Tactic.rwRule [] `norm_nat_cast)
                         ","
                         (Tactic.rwRule [] `Int.natAbs_mul)
                         ","
                         (Tactic.rwRule [] `Nat.mul_eq_one_iff)]
                        "]")
                       [])
                      "<;>"
                      (Tactic.exact
                       "exact"
                       (Term.fun
                        "fun"
                        (Term.basicFun
                         [`h]
                         []
                         "=>"
                         (Term.app
                          (Term.proj
                           (Term.app
                            `ne_of_lt
                            [(Term.proj (Term.proj `hp "." (fieldIdx "1")) "." `one_lt)])
                           "."
                           `symm)
                          [(Term.proj `h "." (fieldIdx "1"))])))))])))]))))
            []
            (Std.Tactic.obtain
             "obtain"
             [(Std.Tactic.RCases.rcasesPatMed
               [(Std.Tactic.RCases.rcasesPat.tuple
                 "⟨"
                 [(Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `y)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hy)])
                   [])]
                 "⟩")])]
             []
             [":=" [`hpk]])
            []
            (Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               []
               []
               ":="
               (Term.app
                (Term.proj (Term.proj `hpi "." (fieldIdx "2")) "." (fieldIdx "2"))
                [(Term.anonymousCtor "⟨" [`k "," (num "1")] "⟩")
                 (Term.anonymousCtor "⟨" [`k "," («term-_» "-" (num "1"))] "⟩")
                 (Term.anonymousCtor
                  "⟨"
                  [`y
                   ","
                   (Term.byTactic
                    "by"
                    (Tactic.tacticSeq
                     (Tactic.tacticSeq1Indented
                      [(Tactic.«tactic_<;>_»
                        (Tactic.rwSeq
                         "rw"
                         []
                         (Tactic.rwRuleSeq
                          "["
                          [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `hkmul)
                           ","
                           (Tactic.rwRule
                            [(patternIgnore (token.«← » "←"))]
                            (Term.app `Nat.cast_mul [`p]))
                           ","
                           (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `hy)]
                          "]")
                         [])
                        "<;>"
                        (Tactic.simp "simp" [] [] [] [] []))])))]
                  "⟩")]))))
            []
            (Mathlib.Tactic.clearAuxDecl "clear_aux_decl")
            []
            (Mathlib.Tactic.Tauto.tauto "tauto" [])])))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`hp41 []]
             [(Term.typeSpec ":" («term_=_» («term_%_» `p "%" (num "4")) "=" (num "1")))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule
                     [(patternIgnore (token.«← » "←"))]
                     (Term.app `Nat.mod_mul_left_mod [`p (num "2") (num "2")]))
                    ","
                    (Tactic.rwRule
                     []
                     (Term.show
                      "show"
                      («term_=_» («term_*_» (num "2") "*" (num "2")) "=" (num "4"))
                      (Term.fromTerm "from" `rfl)))]
                   "]")
                  [(Tactic.location "at" (Tactic.locationHyp [`hp1] []))])
                 []
                 (Tactic.tacticHave_
                  "have"
                  (Term.haveDecl
                   (Term.haveIdDecl
                    []
                    []
                    ":="
                    (Term.app
                     `Nat.mod_lt
                     [`p
                      (Term.show
                       "show"
                       («term_<_» (num "0") "<" (num "4"))
                       (Term.byTactic'
                        "by"
                        (Tactic.tacticSeq
                         (Tactic.tacticSeq1Indented [(Tactic.decide "decide")]))))]))))
                 []
                 (Tactic.revert "revert" [`this `hp3 `hp1])
                 []
                 (Tactic.generalize
                  "generalize"
                  [(Tactic.generalizeArg [] («term_%_» `p "%" (num "4")) "=" `m)]
                  [])
                 ";"
                 (Tactic.decide! "decide!")]))))))
          []
          (Tactic.tacticLet_
           "let"
           (Term.letDecl
            (Term.letPatDecl
             (Term.anonymousCtor "⟨" [`k "," `hk] "⟩")
             []
             []
             ":="
             («term_<|_»
              (Term.proj `Zmod.exists_sq_eq_neg_one_iff "." (fieldIdx "2"))
              "<|"
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Tactic.«tactic_<;>_»
                   (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `hp41)] "]") [])
                   "<;>"
                   (Tactic.exact
                    "exact"
                    (Term.byTactic
                     "by"
                     (Tactic.tacticSeq
                      (Tactic.tacticSeq1Indented [(Tactic.decide "decide")])))))])))))))
          []
          (Std.Tactic.obtain
           "obtain"
           [(Std.Tactic.RCases.rcasesPatMed
             [(Std.Tactic.RCases.rcasesPat.tuple
               "⟨"
               [(Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `k)])
                 [])
                ","
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `k_lt_p)])
                 [])
                ","
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                 [])]
               "⟩")])]
           [":"
            («term∃_,_»
             "∃"
             (Lean.explicitBinders
              [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `k')] ":" (termℕ "ℕ") ")")
               (Lean.bracketedExplicitBinders
                "("
                [(Lean.binderIdent `h)]
                ":"
                («term_<_» `k' "<" `p)
                ")")])
             ","
             («term_=_» (Term.typeAscription "(" `k' ":" [(Term.app `Zmod [`p])] ")") "=" `k))]
           [":="
            [(Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.refine'
                  "refine'"
                  (Term.anonymousCtor
                   "⟨"
                   [`k.val "," `k.val_lt "," (Term.app `Zmod.nat_cast_zmod_val [`k])]
                   "⟩"))])))]])
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`hpk []]
             [(Term.typeSpec
               ":"
               («term_∣_» `p "∣" («term_+_» («term_^_» `k "^" (num "2")) "+" (num "1"))))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule [] `pow_two)
                    ","
                    (Tactic.rwRule
                     [(patternIgnore (token.«← » "←"))]
                     (Term.app `CharP.cast_eq_zero_iff [(Term.app `Zmod [`p]) `p]))
                    ","
                    (Tactic.rwRule [] `Nat.cast_add)
                    ","
                    (Tactic.rwRule [] `Nat.cast_mul)
                    ","
                    (Tactic.rwRule [] `Nat.cast_one)
                    ","
                    (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `hk)
                    ","
                    (Tactic.rwRule [] `add_left_neg)]
                   "]")
                  [])]))))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`hkmul []]
             [(Term.typeSpec
               ":"
               («term_=_»
                (Term.typeAscription
                 "("
                 («term_+_» («term_^_» `k "^" (num "2")) "+" (num "1"))
                 ":"
                 [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
                 ")")
                "="
                («term_*_»
                 (Term.anonymousCtor "⟨" [`k "," (num "1")] "⟩")
                 "*"
                 (Term.anonymousCtor "⟨" [`k "," («term-_» "-" (num "1"))] "⟩"))))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.simp
                  "simp"
                  []
                  []
                  []
                  ["[" [(Tactic.simpLemma [] [] `sq) "," (Tactic.simpLemma [] [] `Zsqrtd.ext)] "]"]
                  [])]))))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`hpne1 []]
             [(Term.typeSpec ":" («term_≠_» `p "≠" (num "1")))]
             ":="
             (Term.app `ne_of_gt [(Term.proj (Term.proj `hp "." (fieldIdx "1")) "." `one_lt)]))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`hkltp []]
             [(Term.typeSpec
               ":"
               («term_<_»
                («term_+_» (num "1") "+" («term_*_» `k "*" `k))
                "<"
                («term_*_» `p "*" `p)))]
             ":="
             (calc
              "calc"
              (calcStep
               («term_≤_»
                («term_+_» (num "1") "+" («term_*_» `k "*" `k))
                "≤"
                («term_+_» `k "+" («term_*_» `k "*" `k)))
               ":="
               (Term.app
                `add_le_add_right
                [(Term.app
                  `Nat.pos_of_ne_zero
                  [(Term.fun
                    "fun"
                    (Term.basicFun
                     [`hk0]
                     []
                     "=>"
                     (Term.byTactic
                      "by"
                      (Tactic.tacticSeq
                       (Tactic.tacticSeq1Indented
                        [(Tactic.«tactic_<;>_»
                          (Mathlib.Tactic.clearAuxDecl "clear_aux_decl")
                          "<;>"
                          (Tactic.simpAll
                           "simp_all"
                           []
                           []
                           []
                           ["[" [(Tactic.simpLemma [] [] `pow_succ')] "]"]))])))))])
                 (Term.hole "_")]))
              [(calcStep
                («term_=_» (Term.hole "_") "=" («term_*_» `k "*" («term_+_» `k "+" (num "1"))))
                ":="
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(Tactic.simp
                     "simp"
                     []
                     []
                     []
                     ["["
                      [(Tactic.simpLemma [] [] `add_comm) "," (Tactic.simpLemma [] [] `mul_add)]
                      "]"]
                     [])]))))
               (calcStep
                («term_<_» (Term.hole "_") "<" («term_*_» `p "*" `p))
                ":="
                (Term.app
                 `mul_lt_mul
                 [`k_lt_p
                  `k_lt_p
                  (Term.app `Nat.succ_pos [(Term.hole "_")])
                  (Term.app `Nat.zero_le [(Term.hole "_")])]))]))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`hpk₁ []]
             [(Term.typeSpec
               ":"
               («term¬_»
                "¬"
                («term_∣_»
                 (Term.typeAscription
                  "("
                  `p
                  ":"
                  [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
                  ")")
                 "∣"
                 (Term.anonymousCtor "⟨" [`k "," («term-_» "-" (num "1"))] "⟩"))))]
             ":="
             (Term.fun
              "fun"
              (Term.basicFun
               [(Term.anonymousCtor "⟨" [`x "," `hx] "⟩")]
               []
               "=>"
               («term_<|_»
                (Term.app
                 `lt_irrefl
                 [(Term.proj
                   (Term.proj
                    (Term.typeAscription
                     "("
                     («term_*_» `p "*" `x)
                     ":"
                     [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
                     ")")
                    "."
                    `norm)
                   "."
                   `natAbs)])
                "<|"
                (calc
                 "calc"
                 (calcStep
                  («term_=_»
                   (Term.proj
                    (Term.app
                     `norm
                     [(Term.typeAscription
                       "("
                       («term_*_» `p "*" `x)
                       ":"
                       [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
                       ")")])
                    "."
                    `natAbs)
                   "="
                   (Term.proj
                    (Term.app
                     `Zsqrtd.norm
                     [(Term.anonymousCtor "⟨" [`k "," («term-_» "-" (num "1"))] "⟩")])
                    "."
                    `natAbs))
                  ":="
                  (Term.byTactic
                   "by"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented
                     [(Tactic.rwSeq
                       "rw"
                       []
                       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `hx)] "]")
                       [])]))))
                 [(calcStep
                   («term_<_»
                    (Term.hole "_")
                    "<"
                    (Term.proj
                     (Term.app
                      `norm
                      [(Term.typeAscription
                        "("
                        `p
                        ":"
                        [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
                        ")")])
                     "."
                     `natAbs))
                   ":="
                   (Term.byTactic
                    "by"
                    (Tactic.tacticSeq
                     (Tactic.tacticSeq1Indented
                      [(Std.Tactic.Simpa.simpa
                        "simpa"
                        []
                        []
                        (Std.Tactic.Simpa.simpaArgsRest
                         []
                         []
                         []
                         [(Tactic.simpArgs
                           "["
                           [(Tactic.simpLemma [] [] `add_comm)
                            ","
                            (Tactic.simpLemma [] [] `Zsqrtd.norm)]
                           "]")]
                         ["using" `hkltp]))]))))
                  (calcStep
                   («term_≤_»
                    (Term.hole "_")
                    "≤"
                    (Term.proj
                     (Term.app
                      `norm
                      [(Term.typeAscription
                        "("
                        («term_*_» `p "*" `x)
                        ":"
                        [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
                        ")")])
                     "."
                     `natAbs))
                   ":="
                   (Term.app
                    `norm_le_norm_mul_left
                    [(Term.hole "_")
                     (Term.fun
                      "fun"
                      (Term.basicFun
                       [`hx0]
                       []
                       "=>"
                       («term_<|_»
                        (Term.show
                         "show"
                         («term_≠_»
                          (Term.typeAscription "(" («term-_» "-" (num "1")) ":" [(termℤ "ℤ")] ")")
                          "≠"
                          (num "0"))
                         (Term.byTactic'
                          "by"
                          (Tactic.tacticSeq
                           (Tactic.tacticSeq1Indented [(Tactic.decide "decide")]))))
                        "<|"
                        (Term.byTactic
                         "by"
                         (Tactic.tacticSeq
                          (Tactic.tacticSeq1Indented
                           [(Std.Tactic.Simpa.simpa
                             "simpa"
                             []
                             []
                             (Std.Tactic.Simpa.simpaArgsRest
                              []
                              []
                              []
                              [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `hx0)] "]")]
                              ["using" (Term.app `congr_arg [`Zsqrtd.im `hx])]))]))))))]))])))))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`hpk₂ []]
             [(Term.typeSpec
               ":"
               («term¬_»
                "¬"
                («term_∣_»
                 (Term.typeAscription
                  "("
                  `p
                  ":"
                  [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
                  ")")
                 "∣"
                 (Term.anonymousCtor "⟨" [`k "," (num "1")] "⟩"))))]
             ":="
             (Term.fun
              "fun"
              (Term.basicFun
               [(Term.anonymousCtor "⟨" [`x "," `hx] "⟩")]
               []
               "=>"
               («term_<|_»
                (Term.app
                 `lt_irrefl
                 [(Term.proj
                   (Term.proj
                    (Term.typeAscription
                     "("
                     («term_*_» `p "*" `x)
                     ":"
                     [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
                     ")")
                    "."
                    `norm)
                   "."
                   `natAbs)])
                "<|"
                (calc
                 "calc"
                 (calcStep
                  («term_=_»
                   (Term.proj
                    (Term.app
                     `norm
                     [(Term.typeAscription
                       "("
                       («term_*_» `p "*" `x)
                       ":"
                       [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
                       ")")])
                    "."
                    `natAbs)
                   "="
                   (Term.proj
                    (Term.app `Zsqrtd.norm [(Term.anonymousCtor "⟨" [`k "," (num "1")] "⟩")])
                    "."
                    `natAbs))
                  ":="
                  (Term.byTactic
                   "by"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented
                     [(Tactic.rwSeq
                       "rw"
                       []
                       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `hx)] "]")
                       [])]))))
                 [(calcStep
                   («term_<_»
                    (Term.hole "_")
                    "<"
                    (Term.proj
                     (Term.app
                      `norm
                      [(Term.typeAscription
                        "("
                        `p
                        ":"
                        [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
                        ")")])
                     "."
                     `natAbs))
                   ":="
                   (Term.byTactic
                    "by"
                    (Tactic.tacticSeq
                     (Tactic.tacticSeq1Indented
                      [(Std.Tactic.Simpa.simpa
                        "simpa"
                        []
                        []
                        (Std.Tactic.Simpa.simpaArgsRest
                         []
                         []
                         []
                         [(Tactic.simpArgs
                           "["
                           [(Tactic.simpLemma [] [] `add_comm)
                            ","
                            (Tactic.simpLemma [] [] `Zsqrtd.norm)]
                           "]")]
                         ["using" `hkltp]))]))))
                  (calcStep
                   («term_≤_»
                    (Term.hole "_")
                    "≤"
                    (Term.proj
                     (Term.app
                      `norm
                      [(Term.typeAscription
                        "("
                        («term_*_» `p "*" `x)
                        ":"
                        [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
                        ")")])
                     "."
                     `natAbs))
                   ":="
                   (Term.app
                    `norm_le_norm_mul_left
                    [(Term.hole "_")
                     (Term.fun
                      "fun"
                      (Term.basicFun
                       [`hx0]
                       []
                       "=>"
                       («term_<|_»
                        (Term.show
                         "show"
                         («term_≠_»
                          (Term.typeAscription "(" (num "1") ":" [(termℤ "ℤ")] ")")
                          "≠"
                          (num "0"))
                         (Term.byTactic'
                          "by"
                          (Tactic.tacticSeq
                           (Tactic.tacticSeq1Indented [(Tactic.decide "decide")]))))
                        "<|"
                        (Term.byTactic
                         "by"
                         (Tactic.tacticSeq
                          (Tactic.tacticSeq1Indented
                           [(Std.Tactic.Simpa.simpa
                             "simpa"
                             []
                             []
                             (Std.Tactic.Simpa.simpaArgsRest
                              []
                              []
                              []
                              [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `hx0)] "]")]
                              ["using" (Term.app `congr_arg [`Zsqrtd.im `hx])]))]))))))]))])))))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`hpu []]
             [(Term.typeSpec
               ":"
               («term¬_»
                "¬"
                (Term.app
                 `IsUnit
                 [(Term.typeAscription
                   "("
                   `p
                   ":"
                   [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
                   ")")])))]
             ":="
             (Term.app
              `mt
              [(Term.proj `norm_eq_one_iff "." (fieldIdx "2"))
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(Tactic.«tactic_<;>_»
                    (Tactic.rwSeq
                     "rw"
                     []
                     (Tactic.rwRuleSeq
                      "["
                      [(Tactic.rwRule [] `norm_nat_cast)
                       ","
                       (Tactic.rwRule [] `Int.natAbs_mul)
                       ","
                       (Tactic.rwRule [] `Nat.mul_eq_one_iff)]
                      "]")
                     [])
                    "<;>"
                    (Tactic.exact
                     "exact"
                     (Term.fun
                      "fun"
                      (Term.basicFun
                       [`h]
                       []
                       "=>"
                       (Term.app
                        (Term.proj
                         (Term.app
                          `ne_of_lt
                          [(Term.proj (Term.proj `hp "." (fieldIdx "1")) "." `one_lt)])
                         "."
                         `symm)
                        [(Term.proj `h "." (fieldIdx "1"))])))))])))]))))
          []
          (Std.Tactic.obtain
           "obtain"
           [(Std.Tactic.RCases.rcasesPatMed
             [(Std.Tactic.RCases.rcasesPat.tuple
               "⟨"
               [(Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `y)])
                 [])
                ","
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hy)])
                 [])]
               "⟩")])]
           []
           [":=" [`hpk]])
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             []
             []
             ":="
             (Term.app
              (Term.proj (Term.proj `hpi "." (fieldIdx "2")) "." (fieldIdx "2"))
              [(Term.anonymousCtor "⟨" [`k "," (num "1")] "⟩")
               (Term.anonymousCtor "⟨" [`k "," («term-_» "-" (num "1"))] "⟩")
               (Term.anonymousCtor
                "⟨"
                [`y
                 ","
                 (Term.byTactic
                  "by"
                  (Tactic.tacticSeq
                   (Tactic.tacticSeq1Indented
                    [(Tactic.«tactic_<;>_»
                      (Tactic.rwSeq
                       "rw"
                       []
                       (Tactic.rwRuleSeq
                        "["
                        [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `hkmul)
                         ","
                         (Tactic.rwRule
                          [(patternIgnore (token.«← » "←"))]
                          (Term.app `Nat.cast_mul [`p]))
                         ","
                         (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `hy)]
                        "]")
                       [])
                      "<;>"
                      (Tactic.simp "simp" [] [] [] [] []))])))]
                "⟩")]))))
          []
          (Mathlib.Tactic.clearAuxDecl "clear_aux_decl")
          []
          (Mathlib.Tactic.Tauto.tauto "tauto" [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.Tauto.tauto "tauto" [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.clearAuxDecl "clear_aux_decl")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         []
         []
         ":="
         (Term.app
          (Term.proj (Term.proj `hpi "." (fieldIdx "2")) "." (fieldIdx "2"))
          [(Term.anonymousCtor "⟨" [`k "," (num "1")] "⟩")
           (Term.anonymousCtor "⟨" [`k "," («term-_» "-" (num "1"))] "⟩")
           (Term.anonymousCtor
            "⟨"
            [`y
             ","
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.«tactic_<;>_»
                  (Tactic.rwSeq
                   "rw"
                   []
                   (Tactic.rwRuleSeq
                    "["
                    [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `hkmul)
                     ","
                     (Tactic.rwRule
                      [(patternIgnore (token.«← » "←"))]
                      (Term.app `Nat.cast_mul [`p]))
                     ","
                     (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `hy)]
                    "]")
                   [])
                  "<;>"
                  (Tactic.simp "simp" [] [] [] [] []))])))]
            "⟩")]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj (Term.proj `hpi "." (fieldIdx "2")) "." (fieldIdx "2"))
       [(Term.anonymousCtor "⟨" [`k "," (num "1")] "⟩")
        (Term.anonymousCtor "⟨" [`k "," («term-_» "-" (num "1"))] "⟩")
        (Term.anonymousCtor
         "⟨"
         [`y
          ","
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(Tactic.«tactic_<;>_»
               (Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `hkmul)
                  ","
                  (Tactic.rwRule [(patternIgnore (token.«← » "←"))] (Term.app `Nat.cast_mul [`p]))
                  ","
                  (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `hy)]
                 "]")
                [])
               "<;>"
               (Tactic.simp "simp" [] [] [] [] []))])))]
         "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [`y
        ","
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Tactic.«tactic_<;>_»
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `hkmul)
                ","
                (Tactic.rwRule [(patternIgnore (token.«← » "←"))] (Term.app `Nat.cast_mul [`p]))
                ","
                (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `hy)]
               "]")
              [])
             "<;>"
             (Tactic.simp "simp" [] [] [] [] []))])))]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.«tactic_<;>_»
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `hkmul)
              ","
              (Tactic.rwRule [(patternIgnore (token.«← » "←"))] (Term.app `Nat.cast_mul [`p]))
              ","
              (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `hy)]
             "]")
            [])
           "<;>"
           (Tactic.simp "simp" [] [] [] [] []))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.«tactic_<;>_»
       (Tactic.rwSeq
        "rw"
        []
        (Tactic.rwRuleSeq
         "["
         [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `hkmul)
          ","
          (Tactic.rwRule [(patternIgnore (token.«← » "←"))] (Term.app `Nat.cast_mul [`p]))
          ","
          (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `hy)]
         "]")
        [])
       "<;>"
       (Tactic.simp "simp" [] [] [] [] []))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] [] [] [])
[PrettyPrinter.parenthesize] ...precedences are 2 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `hkmul)
         ","
         (Tactic.rwRule [(patternIgnore (token.«← » "←"))] (Term.app `Nat.cast_mul [`p]))
         ","
         (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `hy)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hy
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Nat.cast_mul [`p])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Nat.cast_mul
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hkmul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.anonymousCtor "⟨" [`k "," («term-_» "-" (num "1"))] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term-_» "-" (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 75 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 75, (some 75, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.anonymousCtor "⟨" [`k "," (num "1")] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.proj `hpi "." (fieldIdx "2")) "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj `hpi "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hpi
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.obtain
       "obtain"
       [(Std.Tactic.RCases.rcasesPatMed
         [(Std.Tactic.RCases.rcasesPat.tuple
           "⟨"
           [(Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `y)])
             [])
            ","
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hy)])
             [])]
           "⟩")])]
       []
       [":=" [`hpk]])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hpk
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`hpu []]
         [(Term.typeSpec
           ":"
           («term¬_»
            "¬"
            (Term.app
             `IsUnit
             [(Term.typeAscription
               "("
               `p
               ":"
               [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
               ")")])))]
         ":="
         (Term.app
          `mt
          [(Term.proj `norm_eq_one_iff "." (fieldIdx "2"))
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.«tactic_<;>_»
                (Tactic.rwSeq
                 "rw"
                 []
                 (Tactic.rwRuleSeq
                  "["
                  [(Tactic.rwRule [] `norm_nat_cast)
                   ","
                   (Tactic.rwRule [] `Int.natAbs_mul)
                   ","
                   (Tactic.rwRule [] `Nat.mul_eq_one_iff)]
                  "]")
                 [])
                "<;>"
                (Tactic.exact
                 "exact"
                 (Term.fun
                  "fun"
                  (Term.basicFun
                   [`h]
                   []
                   "=>"
                   (Term.app
                    (Term.proj
                     (Term.app
                      `ne_of_lt
                      [(Term.proj (Term.proj `hp "." (fieldIdx "1")) "." `one_lt)])
                     "."
                     `symm)
                    [(Term.proj `h "." (fieldIdx "1"))])))))])))]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `mt
       [(Term.proj `norm_eq_one_iff "." (fieldIdx "2"))
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Tactic.«tactic_<;>_»
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [] `norm_nat_cast)
                ","
                (Tactic.rwRule [] `Int.natAbs_mul)
                ","
                (Tactic.rwRule [] `Nat.mul_eq_one_iff)]
               "]")
              [])
             "<;>"
             (Tactic.exact
              "exact"
              (Term.fun
               "fun"
               (Term.basicFun
                [`h]
                []
                "=>"
                (Term.app
                 (Term.proj
                  (Term.app `ne_of_lt [(Term.proj (Term.proj `hp "." (fieldIdx "1")) "." `one_lt)])
                  "."
                  `symm)
                 [(Term.proj `h "." (fieldIdx "1"))])))))])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.«tactic_<;>_»
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [] `norm_nat_cast)
              ","
              (Tactic.rwRule [] `Int.natAbs_mul)
              ","
              (Tactic.rwRule [] `Nat.mul_eq_one_iff)]
             "]")
            [])
           "<;>"
           (Tactic.exact
            "exact"
            (Term.fun
             "fun"
             (Term.basicFun
              [`h]
              []
              "=>"
              (Term.app
               (Term.proj
                (Term.app `ne_of_lt [(Term.proj (Term.proj `hp "." (fieldIdx "1")) "." `one_lt)])
                "."
                `symm)
               [(Term.proj `h "." (fieldIdx "1"))])))))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.«tactic_<;>_»
       (Tactic.rwSeq
        "rw"
        []
        (Tactic.rwRuleSeq
         "["
         [(Tactic.rwRule [] `norm_nat_cast)
          ","
          (Tactic.rwRule [] `Int.natAbs_mul)
          ","
          (Tactic.rwRule [] `Nat.mul_eq_one_iff)]
         "]")
        [])
       "<;>"
       (Tactic.exact
        "exact"
        (Term.fun
         "fun"
         (Term.basicFun
          [`h]
          []
          "=>"
          (Term.app
           (Term.proj
            (Term.app `ne_of_lt [(Term.proj (Term.proj `hp "." (fieldIdx "1")) "." `one_lt)])
            "."
            `symm)
           [(Term.proj `h "." (fieldIdx "1"))])))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.fun
        "fun"
        (Term.basicFun
         [`h]
         []
         "=>"
         (Term.app
          (Term.proj
           (Term.app `ne_of_lt [(Term.proj (Term.proj `hp "." (fieldIdx "1")) "." `one_lt)])
           "."
           `symm)
          [(Term.proj `h "." (fieldIdx "1"))]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`h]
        []
        "=>"
        (Term.app
         (Term.proj
          (Term.app `ne_of_lt [(Term.proj (Term.proj `hp "." (fieldIdx "1")) "." `one_lt)])
          "."
          `symm)
         [(Term.proj `h "." (fieldIdx "1"))])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (Term.app `ne_of_lt [(Term.proj (Term.proj `hp "." (fieldIdx "1")) "." `one_lt)])
        "."
        `symm)
       [(Term.proj `h "." (fieldIdx "1"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `h "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `h
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (Term.app `ne_of_lt [(Term.proj (Term.proj `hp "." (fieldIdx "1")) "." `one_lt)])
       "."
       `symm)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `ne_of_lt [(Term.proj (Term.proj `hp "." (fieldIdx "1")) "." `one_lt)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.proj `hp "." (fieldIdx "1")) "." `one_lt)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj `hp "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hp
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `ne_of_lt
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `ne_of_lt [(Term.proj (Term.proj `hp "." (fieldIdx "1")) "." `one_lt)])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 2 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `norm_nat_cast)
         ","
         (Tactic.rwRule [] `Int.natAbs_mul)
         ","
         (Tactic.rwRule [] `Nat.mul_eq_one_iff)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Nat.mul_eq_one_iff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Int.natAbs_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `norm_nat_cast
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0,
     tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(Tactic.«tactic_<;>_»
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `norm_nat_cast)
             ","
             (Tactic.rwRule [] `Int.natAbs_mul)
             ","
             (Tactic.rwRule [] `Nat.mul_eq_one_iff)]
            "]")
           [])
          "<;>"
          (Tactic.exact
           "exact"
           (Term.fun
            "fun"
            (Term.basicFun
             [`h]
             []
             "=>"
             (Term.app
              (Term.proj
               (Term.paren
                "("
                (Term.app `ne_of_lt [(Term.proj (Term.proj `hp "." (fieldIdx "1")) "." `one_lt)])
                ")")
               "."
               `symm)
              [(Term.proj `h "." (fieldIdx "1"))])))))])))
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj `norm_eq_one_iff "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `norm_eq_one_iff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `mt
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term¬_»
       "¬"
       (Term.app
        `IsUnit
        [(Term.typeAscription
          "("
          `p
          ":"
          [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
          ")")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `IsUnit
       [(Term.typeAscription "(" `p ":" [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")] ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription "(" `p ":" [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]»', expected 'NumberTheory.Zsqrtd.GaussianInt.termℤ[i]._@.NumberTheory.Zsqrtd.GaussianInt._hyg.6'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.letPatDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveEqnsDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  mod_four_eq_three_of_nat_prime_of_prime
  ( p : ℕ ) [ hp : Fact p . Prime ] ( hpi : Prime ( p : ℤ[i] ) ) : p % 4 = 3
  :=
    hp . 1 . eq_two_or_odd . elim
      fun
          hp2
            =>
            absurd
              hpi
                mt irreducible_iff_prime . 2
                  fun
                    ⟨ hu , h ⟩
                      =>
                      by
                        have := h ⟨ 1 , 1 ⟩ ⟨ 1 , - 1 ⟩ hp2.symm ▸ rfl
                          rw [ ← norm_eq_one_iff , ← norm_eq_one_iff ] at this
                          exact absurd this by decide
        fun
          hp1
            =>
            by_contradiction
              fun
                hp3
                  : p % 4 ≠ 3
                  =>
                  by
                    have
                        hp41
                          : p % 4 = 1
                          :=
                          by
                            rw [ ← Nat.mod_mul_left_mod p 2 2 , show 2 * 2 = 4 from rfl ] at hp1
                              have := Nat.mod_lt p show 0 < 4 by decide
                              revert this hp3 hp1
                              generalize p % 4 = m
                              ;
                              decide!
                      let
                        ⟨ k , hk ⟩
                          :=
                          Zmod.exists_sq_eq_neg_one_iff . 2 <| by rw [ hp41 ] <;> exact by decide
                      obtain
                        ⟨ k , k_lt_p , rfl ⟩
                        : ∃ ( k' : ℕ ) ( h : k' < p ) , ( k' : Zmod p ) = k
                        := by refine' ⟨ k.val , k.val_lt , Zmod.nat_cast_zmod_val k ⟩
                      have
                        hpk
                          : p ∣ k ^ 2 + 1
                          :=
                          by
                            rw
                              [
                                pow_two
                                  ,
                                  ← CharP.cast_eq_zero_iff Zmod p p
                                  ,
                                  Nat.cast_add
                                  ,
                                  Nat.cast_mul
                                  ,
                                  Nat.cast_one
                                  ,
                                  ← hk
                                  ,
                                  add_left_neg
                                ]
                      have
                        hkmul
                          : ( k ^ 2 + 1 : ℤ[i] ) = ⟨ k , 1 ⟩ * ⟨ k , - 1 ⟩
                          :=
                          by simp [ sq , Zsqrtd.ext ]
                      have hpne1 : p ≠ 1 := ne_of_gt hp . 1 . one_lt
                      have
                        hkltp
                          : 1 + k * k < p * p
                          :=
                          calc
                            1 + k * k ≤ k + k * k
                              :=
                              add_le_add_right
                                Nat.pos_of_ne_zero
                                    fun hk0 => by clear_aux_decl <;> simp_all [ pow_succ' ]
                                  _
                            _ = k * k + 1 := by simp [ add_comm , mul_add ]
                              _ < p * p := mul_lt_mul k_lt_p k_lt_p Nat.succ_pos _ Nat.zero_le _
                      have
                        hpk₁
                          : ¬ ( p : ℤ[i] ) ∣ ⟨ k , - 1 ⟩
                          :=
                          fun
                            ⟨ x , hx ⟩
                              =>
                              lt_irrefl ( p * x : ℤ[i] ) . norm . natAbs
                                <|
                                calc
                                  norm ( p * x : ℤ[i] ) . natAbs = Zsqrtd.norm ⟨ k , - 1 ⟩ . natAbs
                                    :=
                                    by rw [ hx ]
                                  _ < norm ( p : ℤ[i] ) . natAbs
                                      :=
                                      by simpa [ add_comm , Zsqrtd.norm ] using hkltp
                                    _ ≤ norm ( p * x : ℤ[i] ) . natAbs
                                      :=
                                      norm_le_norm_mul_left
                                        _
                                          fun
                                            hx0
                                              =>
                                              show ( - 1 : ℤ ) ≠ 0 by decide
                                                <|
                                                by simpa [ hx0 ] using congr_arg Zsqrtd.im hx
                      have
                        hpk₂
                          : ¬ ( p : ℤ[i] ) ∣ ⟨ k , 1 ⟩
                          :=
                          fun
                            ⟨ x , hx ⟩
                              =>
                              lt_irrefl ( p * x : ℤ[i] ) . norm . natAbs
                                <|
                                calc
                                  norm ( p * x : ℤ[i] ) . natAbs = Zsqrtd.norm ⟨ k , 1 ⟩ . natAbs
                                    :=
                                    by rw [ hx ]
                                  _ < norm ( p : ℤ[i] ) . natAbs
                                      :=
                                      by simpa [ add_comm , Zsqrtd.norm ] using hkltp
                                    _ ≤ norm ( p * x : ℤ[i] ) . natAbs
                                      :=
                                      norm_le_norm_mul_left
                                        _
                                          fun
                                            hx0
                                              =>
                                              show ( 1 : ℤ ) ≠ 0 by decide
                                                <|
                                                by simpa [ hx0 ] using congr_arg Zsqrtd.im hx
                      have
                        hpu
                          : ¬ IsUnit ( p : ℤ[i] )
                          :=
                          mt
                            norm_eq_one_iff . 2
                              by
                                rw [ norm_nat_cast , Int.natAbs_mul , Nat.mul_eq_one_iff ]
                                  <;>
                                  exact fun h => ne_of_lt hp . 1 . one_lt . symm h . 1
                      obtain ⟨ y , hy ⟩ := hpk
                      have
                        :=
                          hpi . 2 . 2
                            ⟨ k , 1 ⟩
                              ⟨ k , - 1 ⟩
                              ⟨ y , by rw [ ← hkmul , ← Nat.cast_mul p , ← hy ] <;> simp ⟩
                      clear_aux_decl
                      tauto
#align
  gaussian_int.mod_four_eq_three_of_nat_prime_of_prime GaussianInt.mod_four_eq_three_of_nat_prime_of_prime

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `sq_add_sq_of_nat_prime_of_not_irreducible [])
      (Command.declSig
       [(Term.explicitBinder "(" [`p] [":" (termℕ "ℕ")] [] ")")
        (Term.instBinder "[" [`hp ":"] (Term.app `Fact [(Term.proj `p "." `Prime)]) "]")
        (Term.explicitBinder
         "("
         [`hpi]
         [":"
          («term¬_»
           "¬"
           (Term.app
            `Irreducible
            [(Term.typeAscription
              "("
              `p
              ":"
              [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
              ")")]))]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term∃_,_»
         "∃"
         (Lean.explicitBinders
          (Lean.unbracketedExplicitBinders [(Lean.binderIdent `a) (Lean.binderIdent `b)] []))
         ","
         («term_=_»
          («term_+_» («term_^_» `a "^" (num "2")) "+" («term_^_» `b "^" (num "2")))
          "="
          `p))))
      (Command.declValSimple
       ":="
       (Term.have
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`hpu []]
          [(Term.typeSpec
            ":"
            («term¬_»
             "¬"
             (Term.app
              `IsUnit
              [(Term.typeAscription
                "("
                `p
                ":"
                [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
                ")")])))]
          ":="
          («term_<|_»
           (Term.app `mt [(Term.proj `norm_eq_one_iff "." (fieldIdx "2"))])
           "<|"
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.«tactic_<;>_»
                (Tactic.rwSeq
                 "rw"
                 []
                 (Tactic.rwRuleSeq
                  "["
                  [(Tactic.rwRule [] `norm_nat_cast)
                   ","
                   (Tactic.rwRule [] `Int.natAbs_mul)
                   ","
                   (Tactic.rwRule [] `Nat.mul_eq_one_iff)]
                  "]")
                 [])
                "<;>"
                (Tactic.exact
                 "exact"
                 (Term.fun
                  "fun"
                  (Term.basicFun
                   [`h]
                   []
                   "=>"
                   (Term.app
                    (Term.proj
                     (Term.app
                      `ne_of_lt
                      [(Term.proj (Term.proj `hp "." (fieldIdx "1")) "." `one_lt)])
                     "."
                     `symm)
                    [(Term.proj `h "." (fieldIdx "1"))])))))]))))))
        []
        (Term.have
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`hab []]
           [(Term.typeSpec
             ":"
             («term∃_,_»
              "∃"
              (Lean.explicitBinders
               (Lean.unbracketedExplicitBinders [(Lean.binderIdent `a) (Lean.binderIdent `b)] []))
              ","
              («term_∧_»
               («term_=_»
                (Term.typeAscription
                 "("
                 `p
                 ":"
                 [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
                 ")")
                "="
                («term_*_» `a "*" `b))
               "∧"
               («term_∧_»
                («term¬_» "¬" (Term.app `IsUnit [`a]))
                "∧"
                («term¬_» "¬" (Term.app `IsUnit [`b]))))))]
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Std.Tactic.Simpa.simpa
                "simpa"
                []
                []
                (Std.Tactic.Simpa.simpaArgsRest
                 []
                 []
                 []
                 [(Tactic.simpArgs
                   "["
                   [(Tactic.simpLemma [] [] `irreducible_iff)
                    ","
                    (Tactic.simpLemma [] [] `hpu)
                    ","
                    (Tactic.simpLemma [] [] `not_forall)
                    ","
                    (Tactic.simpLemma [] [] `not_or)]
                   "]")]
                 ["using" `hpi]))])))))
         []
         (Term.let
          "let"
          (Term.letDecl
           (Term.letPatDecl
            (Term.anonymousCtor "⟨" [`a "," `b "," `hpab "," `hau "," `hbu] "⟩")
            []
            []
            ":="
            `hab))
          []
          (Term.have
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`hnap []]
             [(Term.typeSpec ":" («term_=_» (Term.proj (Term.app `norm [`a]) "." `natAbs) "=" `p))]
             ":="
             (Term.proj
              («term_<|_»
               (Term.proj
                (Term.app
                 (Term.proj (Term.proj `hp "." (fieldIdx "1")) "." `mul_eq_prime_sq_iff)
                 [(Term.app `mt [(Term.proj `norm_eq_one_iff "." (fieldIdx "1")) `hau])
                  (Term.app `mt [(Term.proj `norm_eq_one_iff "." (fieldIdx "1")) `hbu])])
                "."
                (fieldIdx "1"))
               "<|"
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(Tactic.«tactic_<;>_»
                    (Tactic.rwSeq
                     "rw"
                     []
                     (Tactic.rwRuleSeq
                      "["
                      [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Int.coe_nat_inj')
                       ","
                       (Tactic.rwRule [] `Int.coe_nat_pow)
                       ","
                       (Tactic.rwRule [] `sq)
                       ","
                       (Tactic.rwRule
                        [(patternIgnore (token.«← » "←"))]
                        (Term.app (Term.explicit "@" `norm_nat_cast) [(«term-_» "-" (num "1"))]))
                       ","
                       (Tactic.rwRule [] `hpab)]
                      "]")
                     [])
                    "<;>"
                    (Tactic.simp "simp" [] [] [] [] []))]))))
              "."
              (fieldIdx "1"))))
           []
           (Term.anonymousCtor
            "⟨"
            [(Term.proj (Term.proj `a "." `re) "." `natAbs)
             ","
             (Term.proj (Term.proj `a "." `im) "." `natAbs)
             ","
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Std.Tactic.Simpa.simpa
                  "simpa"
                  []
                  []
                  (Std.Tactic.Simpa.simpaArgsRest
                   []
                   []
                   []
                   [(Tactic.simpArgs
                     "["
                     [(Tactic.simpLemma [] [] `nat_abs_norm_eq) "," (Tactic.simpLemma [] [] `sq)]
                     "]")]
                   ["using" `hnap]))])))]
            "⟩")))))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.have
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`hpu []]
         [(Term.typeSpec
           ":"
           («term¬_»
            "¬"
            (Term.app
             `IsUnit
             [(Term.typeAscription
               "("
               `p
               ":"
               [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
               ")")])))]
         ":="
         («term_<|_»
          (Term.app `mt [(Term.proj `norm_eq_one_iff "." (fieldIdx "2"))])
          "<|"
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(Tactic.«tactic_<;>_»
               (Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule [] `norm_nat_cast)
                  ","
                  (Tactic.rwRule [] `Int.natAbs_mul)
                  ","
                  (Tactic.rwRule [] `Nat.mul_eq_one_iff)]
                 "]")
                [])
               "<;>"
               (Tactic.exact
                "exact"
                (Term.fun
                 "fun"
                 (Term.basicFun
                  [`h]
                  []
                  "=>"
                  (Term.app
                   (Term.proj
                    (Term.app
                     `ne_of_lt
                     [(Term.proj (Term.proj `hp "." (fieldIdx "1")) "." `one_lt)])
                    "."
                    `symm)
                   [(Term.proj `h "." (fieldIdx "1"))])))))]))))))
       []
       (Term.have
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`hab []]
          [(Term.typeSpec
            ":"
            («term∃_,_»
             "∃"
             (Lean.explicitBinders
              (Lean.unbracketedExplicitBinders [(Lean.binderIdent `a) (Lean.binderIdent `b)] []))
             ","
             («term_∧_»
              («term_=_»
               (Term.typeAscription
                "("
                `p
                ":"
                [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
                ")")
               "="
               («term_*_» `a "*" `b))
              "∧"
              («term_∧_»
               («term¬_» "¬" (Term.app `IsUnit [`a]))
               "∧"
               («term¬_» "¬" (Term.app `IsUnit [`b]))))))]
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(Std.Tactic.Simpa.simpa
               "simpa"
               []
               []
               (Std.Tactic.Simpa.simpaArgsRest
                []
                []
                []
                [(Tactic.simpArgs
                  "["
                  [(Tactic.simpLemma [] [] `irreducible_iff)
                   ","
                   (Tactic.simpLemma [] [] `hpu)
                   ","
                   (Tactic.simpLemma [] [] `not_forall)
                   ","
                   (Tactic.simpLemma [] [] `not_or)]
                  "]")]
                ["using" `hpi]))])))))
        []
        (Term.let
         "let"
         (Term.letDecl
          (Term.letPatDecl
           (Term.anonymousCtor "⟨" [`a "," `b "," `hpab "," `hau "," `hbu] "⟩")
           []
           []
           ":="
           `hab))
         []
         (Term.have
          "have"
          (Term.haveDecl
           (Term.haveIdDecl
            [`hnap []]
            [(Term.typeSpec ":" («term_=_» (Term.proj (Term.app `norm [`a]) "." `natAbs) "=" `p))]
            ":="
            (Term.proj
             («term_<|_»
              (Term.proj
               (Term.app
                (Term.proj (Term.proj `hp "." (fieldIdx "1")) "." `mul_eq_prime_sq_iff)
                [(Term.app `mt [(Term.proj `norm_eq_one_iff "." (fieldIdx "1")) `hau])
                 (Term.app `mt [(Term.proj `norm_eq_one_iff "." (fieldIdx "1")) `hbu])])
               "."
               (fieldIdx "1"))
              "<|"
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Tactic.«tactic_<;>_»
                   (Tactic.rwSeq
                    "rw"
                    []
                    (Tactic.rwRuleSeq
                     "["
                     [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Int.coe_nat_inj')
                      ","
                      (Tactic.rwRule [] `Int.coe_nat_pow)
                      ","
                      (Tactic.rwRule [] `sq)
                      ","
                      (Tactic.rwRule
                       [(patternIgnore (token.«← » "←"))]
                       (Term.app (Term.explicit "@" `norm_nat_cast) [(«term-_» "-" (num "1"))]))
                      ","
                      (Tactic.rwRule [] `hpab)]
                     "]")
                    [])
                   "<;>"
                   (Tactic.simp "simp" [] [] [] [] []))]))))
             "."
             (fieldIdx "1"))))
          []
          (Term.anonymousCtor
           "⟨"
           [(Term.proj (Term.proj `a "." `re) "." `natAbs)
            ","
            (Term.proj (Term.proj `a "." `im) "." `natAbs)
            ","
            (Term.byTactic
             "by"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(Std.Tactic.Simpa.simpa
                 "simpa"
                 []
                 []
                 (Std.Tactic.Simpa.simpaArgsRest
                  []
                  []
                  []
                  [(Tactic.simpArgs
                    "["
                    [(Tactic.simpLemma [] [] `nat_abs_norm_eq) "," (Tactic.simpLemma [] [] `sq)]
                    "]")]
                  ["using" `hnap]))])))]
           "⟩")))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.have
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`hab []]
         [(Term.typeSpec
           ":"
           («term∃_,_»
            "∃"
            (Lean.explicitBinders
             (Lean.unbracketedExplicitBinders [(Lean.binderIdent `a) (Lean.binderIdent `b)] []))
            ","
            («term_∧_»
             («term_=_»
              (Term.typeAscription
               "("
               `p
               ":"
               [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
               ")")
              "="
              («term_*_» `a "*" `b))
             "∧"
             («term_∧_»
              («term¬_» "¬" (Term.app `IsUnit [`a]))
              "∧"
              («term¬_» "¬" (Term.app `IsUnit [`b]))))))]
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Std.Tactic.Simpa.simpa
              "simpa"
              []
              []
              (Std.Tactic.Simpa.simpaArgsRest
               []
               []
               []
               [(Tactic.simpArgs
                 "["
                 [(Tactic.simpLemma [] [] `irreducible_iff)
                  ","
                  (Tactic.simpLemma [] [] `hpu)
                  ","
                  (Tactic.simpLemma [] [] `not_forall)
                  ","
                  (Tactic.simpLemma [] [] `not_or)]
                 "]")]
               ["using" `hpi]))])))))
       []
       (Term.let
        "let"
        (Term.letDecl
         (Term.letPatDecl
          (Term.anonymousCtor "⟨" [`a "," `b "," `hpab "," `hau "," `hbu] "⟩")
          []
          []
          ":="
          `hab))
        []
        (Term.have
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`hnap []]
           [(Term.typeSpec ":" («term_=_» (Term.proj (Term.app `norm [`a]) "." `natAbs) "=" `p))]
           ":="
           (Term.proj
            («term_<|_»
             (Term.proj
              (Term.app
               (Term.proj (Term.proj `hp "." (fieldIdx "1")) "." `mul_eq_prime_sq_iff)
               [(Term.app `mt [(Term.proj `norm_eq_one_iff "." (fieldIdx "1")) `hau])
                (Term.app `mt [(Term.proj `norm_eq_one_iff "." (fieldIdx "1")) `hbu])])
              "."
              (fieldIdx "1"))
             "<|"
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.«tactic_<;>_»
                  (Tactic.rwSeq
                   "rw"
                   []
                   (Tactic.rwRuleSeq
                    "["
                    [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Int.coe_nat_inj')
                     ","
                     (Tactic.rwRule [] `Int.coe_nat_pow)
                     ","
                     (Tactic.rwRule [] `sq)
                     ","
                     (Tactic.rwRule
                      [(patternIgnore (token.«← » "←"))]
                      (Term.app (Term.explicit "@" `norm_nat_cast) [(«term-_» "-" (num "1"))]))
                     ","
                     (Tactic.rwRule [] `hpab)]
                    "]")
                   [])
                  "<;>"
                  (Tactic.simp "simp" [] [] [] [] []))]))))
            "."
            (fieldIdx "1"))))
         []
         (Term.anonymousCtor
          "⟨"
          [(Term.proj (Term.proj `a "." `re) "." `natAbs)
           ","
           (Term.proj (Term.proj `a "." `im) "." `natAbs)
           ","
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Std.Tactic.Simpa.simpa
                "simpa"
                []
                []
                (Std.Tactic.Simpa.simpaArgsRest
                 []
                 []
                 []
                 [(Tactic.simpArgs
                   "["
                   [(Tactic.simpLemma [] [] `nat_abs_norm_eq) "," (Tactic.simpLemma [] [] `sq)]
                   "]")]
                 ["using" `hnap]))])))]
          "⟩"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.let
       "let"
       (Term.letDecl
        (Term.letPatDecl
         (Term.anonymousCtor "⟨" [`a "," `b "," `hpab "," `hau "," `hbu] "⟩")
         []
         []
         ":="
         `hab))
       []
       (Term.have
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`hnap []]
          [(Term.typeSpec ":" («term_=_» (Term.proj (Term.app `norm [`a]) "." `natAbs) "=" `p))]
          ":="
          (Term.proj
           («term_<|_»
            (Term.proj
             (Term.app
              (Term.proj (Term.proj `hp "." (fieldIdx "1")) "." `mul_eq_prime_sq_iff)
              [(Term.app `mt [(Term.proj `norm_eq_one_iff "." (fieldIdx "1")) `hau])
               (Term.app `mt [(Term.proj `norm_eq_one_iff "." (fieldIdx "1")) `hbu])])
             "."
             (fieldIdx "1"))
            "<|"
            (Term.byTactic
             "by"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(Tactic.«tactic_<;>_»
                 (Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Int.coe_nat_inj')
                    ","
                    (Tactic.rwRule [] `Int.coe_nat_pow)
                    ","
                    (Tactic.rwRule [] `sq)
                    ","
                    (Tactic.rwRule
                     [(patternIgnore (token.«← » "←"))]
                     (Term.app (Term.explicit "@" `norm_nat_cast) [(«term-_» "-" (num "1"))]))
                    ","
                    (Tactic.rwRule [] `hpab)]
                   "]")
                  [])
                 "<;>"
                 (Tactic.simp "simp" [] [] [] [] []))]))))
           "."
           (fieldIdx "1"))))
        []
        (Term.anonymousCtor
         "⟨"
         [(Term.proj (Term.proj `a "." `re) "." `natAbs)
          ","
          (Term.proj (Term.proj `a "." `im) "." `natAbs)
          ","
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(Std.Tactic.Simpa.simpa
               "simpa"
               []
               []
               (Std.Tactic.Simpa.simpaArgsRest
                []
                []
                []
                [(Tactic.simpArgs
                  "["
                  [(Tactic.simpLemma [] [] `nat_abs_norm_eq) "," (Tactic.simpLemma [] [] `sq)]
                  "]")]
                ["using" `hnap]))])))]
         "⟩")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.have
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`hnap []]
         [(Term.typeSpec ":" («term_=_» (Term.proj (Term.app `norm [`a]) "." `natAbs) "=" `p))]
         ":="
         (Term.proj
          («term_<|_»
           (Term.proj
            (Term.app
             (Term.proj (Term.proj `hp "." (fieldIdx "1")) "." `mul_eq_prime_sq_iff)
             [(Term.app `mt [(Term.proj `norm_eq_one_iff "." (fieldIdx "1")) `hau])
              (Term.app `mt [(Term.proj `norm_eq_one_iff "." (fieldIdx "1")) `hbu])])
            "."
            (fieldIdx "1"))
           "<|"
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.«tactic_<;>_»
                (Tactic.rwSeq
                 "rw"
                 []
                 (Tactic.rwRuleSeq
                  "["
                  [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Int.coe_nat_inj')
                   ","
                   (Tactic.rwRule [] `Int.coe_nat_pow)
                   ","
                   (Tactic.rwRule [] `sq)
                   ","
                   (Tactic.rwRule
                    [(patternIgnore (token.«← » "←"))]
                    (Term.app (Term.explicit "@" `norm_nat_cast) [(«term-_» "-" (num "1"))]))
                   ","
                   (Tactic.rwRule [] `hpab)]
                  "]")
                 [])
                "<;>"
                (Tactic.simp "simp" [] [] [] [] []))]))))
          "."
          (fieldIdx "1"))))
       []
       (Term.anonymousCtor
        "⟨"
        [(Term.proj (Term.proj `a "." `re) "." `natAbs)
         ","
         (Term.proj (Term.proj `a "." `im) "." `natAbs)
         ","
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Std.Tactic.Simpa.simpa
              "simpa"
              []
              []
              (Std.Tactic.Simpa.simpaArgsRest
               []
               []
               []
               [(Tactic.simpArgs
                 "["
                 [(Tactic.simpLemma [] [] `nat_abs_norm_eq) "," (Tactic.simpLemma [] [] `sq)]
                 "]")]
               ["using" `hnap]))])))]
        "⟩"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.proj (Term.proj `a "." `re) "." `natAbs)
        ","
        (Term.proj (Term.proj `a "." `im) "." `natAbs)
        ","
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Std.Tactic.Simpa.simpa
             "simpa"
             []
             []
             (Std.Tactic.Simpa.simpaArgsRest
              []
              []
              []
              [(Tactic.simpArgs
                "["
                [(Tactic.simpLemma [] [] `nat_abs_norm_eq) "," (Tactic.simpLemma [] [] `sq)]
                "]")]
              ["using" `hnap]))])))]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Std.Tactic.Simpa.simpa
           "simpa"
           []
           []
           (Std.Tactic.Simpa.simpaArgsRest
            []
            []
            []
            [(Tactic.simpArgs
              "["
              [(Tactic.simpLemma [] [] `nat_abs_norm_eq) "," (Tactic.simpLemma [] [] `sq)]
              "]")]
            ["using" `hnap]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Simpa.simpa
       "simpa"
       []
       []
       (Std.Tactic.Simpa.simpaArgsRest
        []
        []
        []
        [(Tactic.simpArgs
          "["
          [(Tactic.simpLemma [] [] `nat_abs_norm_eq) "," (Tactic.simpLemma [] [] `sq)]
          "]")]
        ["using" `hnap]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hnap
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `sq
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `nat_abs_norm_eq
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.proj `a "." `im) "." `natAbs)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj `a "." `im)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.proj `a "." `re) "." `natAbs)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj `a "." `re)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj
       («term_<|_»
        (Term.proj
         (Term.app
          (Term.proj (Term.proj `hp "." (fieldIdx "1")) "." `mul_eq_prime_sq_iff)
          [(Term.app `mt [(Term.proj `norm_eq_one_iff "." (fieldIdx "1")) `hau])
           (Term.app `mt [(Term.proj `norm_eq_one_iff "." (fieldIdx "1")) `hbu])])
         "."
         (fieldIdx "1"))
        "<|"
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Tactic.«tactic_<;>_»
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Int.coe_nat_inj')
                ","
                (Tactic.rwRule [] `Int.coe_nat_pow)
                ","
                (Tactic.rwRule [] `sq)
                ","
                (Tactic.rwRule
                 [(patternIgnore (token.«← » "←"))]
                 (Term.app (Term.explicit "@" `norm_nat_cast) [(«term-_» "-" (num "1"))]))
                ","
                (Tactic.rwRule [] `hpab)]
               "]")
              [])
             "<;>"
             (Tactic.simp "simp" [] [] [] [] []))]))))
       "."
       (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      («term_<|_»
       (Term.proj
        (Term.app
         (Term.proj (Term.proj `hp "." (fieldIdx "1")) "." `mul_eq_prime_sq_iff)
         [(Term.app `mt [(Term.proj `norm_eq_one_iff "." (fieldIdx "1")) `hau])
          (Term.app `mt [(Term.proj `norm_eq_one_iff "." (fieldIdx "1")) `hbu])])
        "."
        (fieldIdx "1"))
       "<|"
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.«tactic_<;>_»
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Int.coe_nat_inj')
               ","
               (Tactic.rwRule [] `Int.coe_nat_pow)
               ","
               (Tactic.rwRule [] `sq)
               ","
               (Tactic.rwRule
                [(patternIgnore (token.«← » "←"))]
                (Term.app (Term.explicit "@" `norm_nat_cast) [(«term-_» "-" (num "1"))]))
               ","
               (Tactic.rwRule [] `hpab)]
              "]")
             [])
            "<;>"
            (Tactic.simp "simp" [] [] [] [] []))]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.«tactic_<;>_»
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Int.coe_nat_inj')
              ","
              (Tactic.rwRule [] `Int.coe_nat_pow)
              ","
              (Tactic.rwRule [] `sq)
              ","
              (Tactic.rwRule
               [(patternIgnore (token.«← » "←"))]
               (Term.app (Term.explicit "@" `norm_nat_cast) [(«term-_» "-" (num "1"))]))
              ","
              (Tactic.rwRule [] `hpab)]
             "]")
            [])
           "<;>"
           (Tactic.simp "simp" [] [] [] [] []))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.«tactic_<;>_»
       (Tactic.rwSeq
        "rw"
        []
        (Tactic.rwRuleSeq
         "["
         [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Int.coe_nat_inj')
          ","
          (Tactic.rwRule [] `Int.coe_nat_pow)
          ","
          (Tactic.rwRule [] `sq)
          ","
          (Tactic.rwRule
           [(patternIgnore (token.«← » "←"))]
           (Term.app (Term.explicit "@" `norm_nat_cast) [(«term-_» "-" (num "1"))]))
          ","
          (Tactic.rwRule [] `hpab)]
         "]")
        [])
       "<;>"
       (Tactic.simp "simp" [] [] [] [] []))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] [] [] [])
[PrettyPrinter.parenthesize] ...precedences are 2 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Int.coe_nat_inj')
         ","
         (Tactic.rwRule [] `Int.coe_nat_pow)
         ","
         (Tactic.rwRule [] `sq)
         ","
         (Tactic.rwRule
          [(patternIgnore (token.«← » "←"))]
          (Term.app (Term.explicit "@" `norm_nat_cast) [(«term-_» "-" (num "1"))]))
         ","
         (Tactic.rwRule [] `hpab)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hpab
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.explicit "@" `norm_nat_cast) [(«term-_» "-" (num "1"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term-_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term-_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term-_» "-" (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 75 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 75, (some 75, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term-_» "-" (num "1")) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.explicit "@" `norm_nat_cast)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `norm_nat_cast
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (some 1024,
     term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `sq
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Int.coe_nat_pow
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Int.coe_nat_inj'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      (Term.proj
       (Term.app
        (Term.proj (Term.proj `hp "." (fieldIdx "1")) "." `mul_eq_prime_sq_iff)
        [(Term.app `mt [(Term.proj `norm_eq_one_iff "." (fieldIdx "1")) `hau])
         (Term.app `mt [(Term.proj `norm_eq_one_iff "." (fieldIdx "1")) `hbu])])
       "."
       (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       (Term.proj (Term.proj `hp "." (fieldIdx "1")) "." `mul_eq_prime_sq_iff)
       [(Term.app `mt [(Term.proj `norm_eq_one_iff "." (fieldIdx "1")) `hau])
        (Term.app `mt [(Term.proj `norm_eq_one_iff "." (fieldIdx "1")) `hbu])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `mt [(Term.proj `norm_eq_one_iff "." (fieldIdx "1")) `hbu])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hbu
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj `norm_eq_one_iff "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `norm_eq_one_iff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `mt
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `mt [(Term.proj `norm_eq_one_iff "." (fieldIdx "1")) `hbu])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `mt [(Term.proj `norm_eq_one_iff "." (fieldIdx "1")) `hau])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hau
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj `norm_eq_one_iff "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `norm_eq_one_iff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `mt
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `mt [(Term.proj `norm_eq_one_iff "." (fieldIdx "1")) `hau])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.proj `hp "." (fieldIdx "1")) "." `mul_eq_prime_sq_iff)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj `hp "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hp
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      (Term.proj (Term.proj `hp "." (fieldIdx "1")) "." `mul_eq_prime_sq_iff)
      [(Term.paren "(" (Term.app `mt [(Term.proj `norm_eq_one_iff "." (fieldIdx "1")) `hau]) ")")
       (Term.paren "(" (Term.app `mt [(Term.proj `norm_eq_one_iff "." (fieldIdx "1")) `hbu]) ")")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_<|_»
      (Term.proj
       (Term.paren
        "("
        (Term.app
         (Term.proj (Term.proj `hp "." (fieldIdx "1")) "." `mul_eq_prime_sq_iff)
         [(Term.paren "(" (Term.app `mt [(Term.proj `norm_eq_one_iff "." (fieldIdx "1")) `hau]) ")")
          (Term.paren
           "("
           (Term.app `mt [(Term.proj `norm_eq_one_iff "." (fieldIdx "1")) `hbu])
           ")")])
        ")")
       "."
       (fieldIdx "1"))
      "<|"
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.«tactic_<;>_»
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Int.coe_nat_inj')
              ","
              (Tactic.rwRule [] `Int.coe_nat_pow)
              ","
              (Tactic.rwRule [] `sq)
              ","
              (Tactic.rwRule
               [(patternIgnore (token.«← » "←"))]
               (Term.app
                (Term.explicit "@" `norm_nat_cast)
                [(Term.paren "(" («term-_» "-" (num "1")) ")")]))
              ","
              (Tactic.rwRule [] `hpab)]
             "]")
            [])
           "<;>"
           (Tactic.simp "simp" [] [] [] [] []))]))))
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_» (Term.proj (Term.app `norm [`a]) "." `natAbs) "=" `p)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.proj (Term.app `norm [`a]) "." `natAbs)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `norm [`a])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `norm
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `norm [`a]) ")")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letPatDecl', expected 'Lean.Parser.Term.letIdDecl'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hab
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [`a "," `b "," `hpab "," `hau "," `hbu] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hbu
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hau
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hpab
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `b
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Std.Tactic.Simpa.simpa
           "simpa"
           []
           []
           (Std.Tactic.Simpa.simpaArgsRest
            []
            []
            []
            [(Tactic.simpArgs
              "["
              [(Tactic.simpLemma [] [] `irreducible_iff)
               ","
               (Tactic.simpLemma [] [] `hpu)
               ","
               (Tactic.simpLemma [] [] `not_forall)
               ","
               (Tactic.simpLemma [] [] `not_or)]
              "]")]
            ["using" `hpi]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Simpa.simpa
       "simpa"
       []
       []
       (Std.Tactic.Simpa.simpaArgsRest
        []
        []
        []
        [(Tactic.simpArgs
          "["
          [(Tactic.simpLemma [] [] `irreducible_iff)
           ","
           (Tactic.simpLemma [] [] `hpu)
           ","
           (Tactic.simpLemma [] [] `not_forall)
           ","
           (Tactic.simpLemma [] [] `not_or)]
          "]")]
        ["using" `hpi]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hpi
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `not_or
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `not_forall
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hpu
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `irreducible_iff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term∃_,_»
       "∃"
       (Lean.explicitBinders
        (Lean.unbracketedExplicitBinders [(Lean.binderIdent `a) (Lean.binderIdent `b)] []))
       ","
       («term_∧_»
        («term_=_»
         (Term.typeAscription "(" `p ":" [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")] ")")
         "="
         («term_*_» `a "*" `b))
        "∧"
        («term_∧_»
         («term¬_» "¬" (Term.app `IsUnit [`a]))
         "∧"
         («term¬_» "¬" (Term.app `IsUnit [`b])))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∧_»
       («term_=_»
        (Term.typeAscription "(" `p ":" [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")] ")")
        "="
        («term_*_» `a "*" `b))
       "∧"
       («term_∧_»
        («term¬_» "¬" (Term.app `IsUnit [`a]))
        "∧"
        («term¬_» "¬" (Term.app `IsUnit [`b]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∧_» («term¬_» "¬" (Term.app `IsUnit [`a])) "∧" («term¬_» "¬" (Term.app `IsUnit [`b])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term¬_» "¬" (Term.app `IsUnit [`b]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `IsUnit [`b])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `b
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `IsUnit
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 40 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 35 >? 1024, (some 40, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 35, term))
      («term¬_» "¬" (Term.app `IsUnit [`a]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `IsUnit [`a])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `IsUnit
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 40 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 36 >? 1024, (some 40, term) <=? (some 35, term)
[PrettyPrinter.parenthesize] ...precedences are 35 >? 35, (some 35, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 35, term))
      («term_=_»
       (Term.typeAscription "(" `p ":" [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")] ")")
       "="
       («term_*_» `a "*" `b))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_» `a "*" `b)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `b
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `a
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.typeAscription "(" `p ":" [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]»', expected 'NumberTheory.Zsqrtd.GaussianInt.termℤ[i]._@.NumberTheory.Zsqrtd.GaussianInt._hyg.6'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.letPatDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveEqnsDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  sq_add_sq_of_nat_prime_of_not_irreducible
  ( p : ℕ ) [ hp : Fact p . Prime ] ( hpi : ¬ Irreducible ( p : ℤ[i] ) ) : ∃ a b , a ^ 2 + b ^ 2 = p
  :=
    have
      hpu
        : ¬ IsUnit ( p : ℤ[i] )
        :=
        mt norm_eq_one_iff . 2
          <|
          by
            rw [ norm_nat_cast , Int.natAbs_mul , Nat.mul_eq_one_iff ]
              <;>
              exact fun h => ne_of_lt hp . 1 . one_lt . symm h . 1
      have
        hab
          : ∃ a b , ( p : ℤ[i] ) = a * b ∧ ¬ IsUnit a ∧ ¬ IsUnit b
          :=
          by simpa [ irreducible_iff , hpu , not_forall , not_or ] using hpi
        let
          ⟨ a , b , hpab , hau , hbu ⟩ := hab
          have
            hnap
              : norm a . natAbs = p
              :=
              hp . 1 . mul_eq_prime_sq_iff mt norm_eq_one_iff . 1 hau mt norm_eq_one_iff . 1 hbu . 1
                  <|
                  by
                    rw [ ← Int.coe_nat_inj' , Int.coe_nat_pow , sq , ← @ norm_nat_cast - 1 , hpab ]
                      <;>
                      simp
                .
                1
            ⟨ a . re . natAbs , a . im . natAbs , by simpa [ nat_abs_norm_eq , sq ] using hnap ⟩
#align
  gaussian_int.sq_add_sq_of_nat_prime_of_not_irreducible GaussianInt.sq_add_sq_of_nat_prime_of_not_irreducible

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `prime_of_nat_prime_of_mod_four_eq_three [])
      (Command.declSig
       [(Term.explicitBinder "(" [`p] [":" (termℕ "ℕ")] [] ")")
        (Term.instBinder "[" [`hp ":"] (Term.app `Fact [(Term.proj `p "." `Prime)]) "]")
        (Term.explicitBinder
         "("
         [`hp3]
         [":" («term_=_» («term_%_» `p "%" (num "4")) "=" (num "3"))]
         []
         ")")]
       (Term.typeSpec
        ":"
        (Term.app
         `Prime
         [(Term.typeAscription
           "("
           `p
           ":"
           [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
           ")")])))
      (Command.declValSimple
       ":="
       («term_<|_»
        (Term.proj `irreducible_iff_prime "." (fieldIdx "1"))
        "<|"
        (Term.app
         `by_contradiction
         [(Term.fun
           "fun"
           (Term.basicFun
            [`hpi]
            []
            "=>"
            (Term.let
             "let"
             (Term.letDecl
              (Term.letPatDecl
               (Term.anonymousCtor "⟨" [`a "," `b "," `hab] "⟩")
               []
               []
               ":="
               (Term.app `sq_add_sq_of_nat_prime_of_not_irreducible [`p `hpi])))
             []
             (Term.have
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                []
                [(Term.typeSpec
                  ":"
                  (Term.forall
                   "∀"
                   [`a `b]
                   [(Term.typeSpec ":" (Term.app `Zmod [(num "4")]))]
                   ","
                   («term_≠_»
                    («term_+_» («term_^_» `a "^" (num "2")) "+" («term_^_» `b "^" (num "2")))
                    "≠"
                    `p)))]
                ":="
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(Tactic.«tactic_<;>_»
                     (Tactic.tacticErw__
                      "erw"
                      (Tactic.rwRuleSeq
                       "["
                       [(Tactic.rwRule
                         [(patternIgnore (token.«← » "←"))]
                         (Term.app `Zmod.nat_cast_mod [`p (num "4")]))
                        ","
                        (Tactic.rwRule [] `hp3)]
                       "]")
                      [])
                     "<;>"
                     (Tactic.exact
                      "exact"
                      (Term.byTactic
                       "by"
                       (Tactic.tacticSeq
                        (Tactic.tacticSeq1Indented [(Tactic.decide "decide")])))))])))))
              []
              (Term.app
               `this
               [`a
                `b
                (Term.subst
                 `hab
                 "▸"
                 [(Term.byTactic
                   "by"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])])))])])))))]))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_»
       (Term.proj `irreducible_iff_prime "." (fieldIdx "1"))
       "<|"
       (Term.app
        `by_contradiction
        [(Term.fun
          "fun"
          (Term.basicFun
           [`hpi]
           []
           "=>"
           (Term.let
            "let"
            (Term.letDecl
             (Term.letPatDecl
              (Term.anonymousCtor "⟨" [`a "," `b "," `hab] "⟩")
              []
              []
              ":="
              (Term.app `sq_add_sq_of_nat_prime_of_not_irreducible [`p `hpi])))
            []
            (Term.have
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               []
               [(Term.typeSpec
                 ":"
                 (Term.forall
                  "∀"
                  [`a `b]
                  [(Term.typeSpec ":" (Term.app `Zmod [(num "4")]))]
                  ","
                  («term_≠_»
                   («term_+_» («term_^_» `a "^" (num "2")) "+" («term_^_» `b "^" (num "2")))
                   "≠"
                   `p)))]
               ":="
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(Tactic.«tactic_<;>_»
                    (Tactic.tacticErw__
                     "erw"
                     (Tactic.rwRuleSeq
                      "["
                      [(Tactic.rwRule
                        [(patternIgnore (token.«← » "←"))]
                        (Term.app `Zmod.nat_cast_mod [`p (num "4")]))
                       ","
                       (Tactic.rwRule [] `hp3)]
                      "]")
                     [])
                    "<;>"
                    (Tactic.exact
                     "exact"
                     (Term.byTactic
                      "by"
                      (Tactic.tacticSeq
                       (Tactic.tacticSeq1Indented [(Tactic.decide "decide")])))))])))))
             []
             (Term.app
              `this
              [`a
               `b
               (Term.subst
                `hab
                "▸"
                [(Term.byTactic
                  "by"
                  (Tactic.tacticSeq
                   (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])])))])])))))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `by_contradiction
       [(Term.fun
         "fun"
         (Term.basicFun
          [`hpi]
          []
          "=>"
          (Term.let
           "let"
           (Term.letDecl
            (Term.letPatDecl
             (Term.anonymousCtor "⟨" [`a "," `b "," `hab] "⟩")
             []
             []
             ":="
             (Term.app `sq_add_sq_of_nat_prime_of_not_irreducible [`p `hpi])))
           []
           (Term.have
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              []
              [(Term.typeSpec
                ":"
                (Term.forall
                 "∀"
                 [`a `b]
                 [(Term.typeSpec ":" (Term.app `Zmod [(num "4")]))]
                 ","
                 («term_≠_»
                  («term_+_» («term_^_» `a "^" (num "2")) "+" («term_^_» `b "^" (num "2")))
                  "≠"
                  `p)))]
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Tactic.«tactic_<;>_»
                   (Tactic.tacticErw__
                    "erw"
                    (Tactic.rwRuleSeq
                     "["
                     [(Tactic.rwRule
                       [(patternIgnore (token.«← » "←"))]
                       (Term.app `Zmod.nat_cast_mod [`p (num "4")]))
                      ","
                      (Tactic.rwRule [] `hp3)]
                     "]")
                    [])
                   "<;>"
                   (Tactic.exact
                    "exact"
                    (Term.byTactic
                     "by"
                     (Tactic.tacticSeq
                      (Tactic.tacticSeq1Indented [(Tactic.decide "decide")])))))])))))
            []
            (Term.app
             `this
             [`a
              `b
              (Term.subst
               `hab
               "▸"
               [(Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])])))])])))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`hpi]
        []
        "=>"
        (Term.let
         "let"
         (Term.letDecl
          (Term.letPatDecl
           (Term.anonymousCtor "⟨" [`a "," `b "," `hab] "⟩")
           []
           []
           ":="
           (Term.app `sq_add_sq_of_nat_prime_of_not_irreducible [`p `hpi])))
         []
         (Term.have
          "have"
          (Term.haveDecl
           (Term.haveIdDecl
            []
            [(Term.typeSpec
              ":"
              (Term.forall
               "∀"
               [`a `b]
               [(Term.typeSpec ":" (Term.app `Zmod [(num "4")]))]
               ","
               («term_≠_»
                («term_+_» («term_^_» `a "^" (num "2")) "+" («term_^_» `b "^" (num "2")))
                "≠"
                `p)))]
            ":="
            (Term.byTactic
             "by"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(Tactic.«tactic_<;>_»
                 (Tactic.tacticErw__
                  "erw"
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule
                     [(patternIgnore (token.«← » "←"))]
                     (Term.app `Zmod.nat_cast_mod [`p (num "4")]))
                    ","
                    (Tactic.rwRule [] `hp3)]
                   "]")
                  [])
                 "<;>"
                 (Tactic.exact
                  "exact"
                  (Term.byTactic
                   "by"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented [(Tactic.decide "decide")])))))])))))
          []
          (Term.app
           `this
           [`a
            `b
            (Term.subst
             `hab
             "▸"
             [(Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])])))])])))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.let
       "let"
       (Term.letDecl
        (Term.letPatDecl
         (Term.anonymousCtor "⟨" [`a "," `b "," `hab] "⟩")
         []
         []
         ":="
         (Term.app `sq_add_sq_of_nat_prime_of_not_irreducible [`p `hpi])))
       []
       (Term.have
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          []
          [(Term.typeSpec
            ":"
            (Term.forall
             "∀"
             [`a `b]
             [(Term.typeSpec ":" (Term.app `Zmod [(num "4")]))]
             ","
             («term_≠_»
              («term_+_» («term_^_» `a "^" (num "2")) "+" («term_^_» `b "^" (num "2")))
              "≠"
              `p)))]
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(Tactic.«tactic_<;>_»
               (Tactic.tacticErw__
                "erw"
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule
                   [(patternIgnore (token.«← » "←"))]
                   (Term.app `Zmod.nat_cast_mod [`p (num "4")]))
                  ","
                  (Tactic.rwRule [] `hp3)]
                 "]")
                [])
               "<;>"
               (Tactic.exact
                "exact"
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.decide "decide")])))))])))))
        []
        (Term.app
         `this
         [`a
          `b
          (Term.subst
           `hab
           "▸"
           [(Term.byTactic
             "by"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])])))])])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.have
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         []
         [(Term.typeSpec
           ":"
           (Term.forall
            "∀"
            [`a `b]
            [(Term.typeSpec ":" (Term.app `Zmod [(num "4")]))]
            ","
            («term_≠_»
             («term_+_» («term_^_» `a "^" (num "2")) "+" («term_^_» `b "^" (num "2")))
             "≠"
             `p)))]
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.«tactic_<;>_»
              (Tactic.tacticErw__
               "erw"
               (Tactic.rwRuleSeq
                "["
                [(Tactic.rwRule
                  [(patternIgnore (token.«← » "←"))]
                  (Term.app `Zmod.nat_cast_mod [`p (num "4")]))
                 ","
                 (Tactic.rwRule [] `hp3)]
                "]")
               [])
              "<;>"
              (Tactic.exact
               "exact"
               (Term.byTactic
                "by"
                (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.decide "decide")])))))])))))
       []
       (Term.app
        `this
        [`a
         `b
         (Term.subst
          `hab
          "▸"
          [(Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])])))])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `this
       [`a
        `b
        (Term.subst
         `hab
         "▸"
         [(Term.byTactic
           "by"
           (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])])))])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.subst', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.subst', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.subst
       `hab
       "▸"
       [(Term.byTactic
         "by"
         (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])])))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] [] [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 75 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 75, term))
      `hab
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 75, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 75, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.subst
      `hab
      "▸"
      [(Term.byTactic
        "by"
        (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])])))])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `b
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `this
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.«tactic_<;>_»
           (Tactic.tacticErw__
            "erw"
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule
               [(patternIgnore (token.«← » "←"))]
               (Term.app `Zmod.nat_cast_mod [`p (num "4")]))
              ","
              (Tactic.rwRule [] `hp3)]
             "]")
            [])
           "<;>"
           (Tactic.exact
            "exact"
            (Term.byTactic
             "by"
             (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.decide "decide")])))))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.«tactic_<;>_»
       (Tactic.tacticErw__
        "erw"
        (Tactic.rwRuleSeq
         "["
         [(Tactic.rwRule
           [(patternIgnore (token.«← » "←"))]
           (Term.app `Zmod.nat_cast_mod [`p (num "4")]))
          ","
          (Tactic.rwRule [] `hp3)]
         "]")
        [])
       "<;>"
       (Tactic.exact
        "exact"
        (Term.byTactic
         "by"
         (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.decide "decide")])))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.byTactic
        "by"
        (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.decide "decide")]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.decide "decide")])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.decide "decide")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 2 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
      (Tactic.tacticErw__
       "erw"
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule
          [(patternIgnore (token.«← » "←"))]
          (Term.app `Zmod.nat_cast_mod [`p (num "4")]))
         ","
         (Tactic.rwRule [] `hp3)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hp3
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Zmod.nat_cast_mod [`p (num "4")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "4")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Zmod.nat_cast_mod
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.forall
       "∀"
       [`a `b]
       [(Term.typeSpec ":" (Term.app `Zmod [(num "4")]))]
       ","
       («term_≠_» («term_+_» («term_^_» `a "^" (num "2")) "+" («term_^_» `b "^" (num "2"))) "≠" `p))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≠_» («term_+_» («term_^_» `a "^" (num "2")) "+" («term_^_» `b "^" (num "2"))) "≠" `p)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      («term_+_» («term_^_» `a "^" (num "2")) "+" («term_^_» `b "^" (num "2")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_» `b "^" (num "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      `b
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      («term_^_» `a "^" (num "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      `a
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 65 >? 80, (some 80, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 65, (some 66, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Zmod [(num "4")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "4")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Zmod
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letPatDecl', expected 'Lean.Parser.Term.letIdDecl'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `sq_add_sq_of_nat_prime_of_not_irreducible [`p `hpi])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hpi
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `sq_add_sq_of_nat_prime_of_not_irreducible
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [`a "," `b "," `hab] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hab
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `b
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hpi
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `by_contradiction
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      (Term.proj `irreducible_iff_prime "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `irreducible_iff_prime
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app
       `Prime
       [(Term.typeAscription "(" `p ":" [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")] ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription "(" `p ":" [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]»', expected 'NumberTheory.Zsqrtd.GaussianInt.termℤ[i]._@.NumberTheory.Zsqrtd.GaussianInt._hyg.6'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  prime_of_nat_prime_of_mod_four_eq_three
  ( p : ℕ ) [ hp : Fact p . Prime ] ( hp3 : p % 4 = 3 ) : Prime ( p : ℤ[i] )
  :=
    irreducible_iff_prime . 1
      <|
      by_contradiction
        fun
          hpi
            =>
            let
              ⟨ a , b , hab ⟩ := sq_add_sq_of_nat_prime_of_not_irreducible p hpi
              have
                : ∀ a b : Zmod 4 , a ^ 2 + b ^ 2 ≠ p
                  :=
                  by erw [ ← Zmod.nat_cast_mod p 4 , hp3 ] <;> exact by decide
                this a b hab ▸ by simp
#align
  gaussian_int.prime_of_nat_prime_of_mod_four_eq_three GaussianInt.prime_of_nat_prime_of_mod_four_eq_three

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "A prime natural number is prime in `ℤ[i]` if and only if it is `3` mod `4` -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `prime_iff_mod_four_eq_three_of_nat_prime [])
      (Command.declSig
       [(Term.explicitBinder "(" [`p] [":" (termℕ "ℕ")] [] ")")
        (Term.instBinder "[" [`hp ":"] (Term.app `Fact [(Term.proj `p "." `Prime)]) "]")]
       (Term.typeSpec
        ":"
        («term_↔_»
         (Term.app
          `Prime
          [(Term.typeAscription
            "("
            `p
            ":"
            [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
            ")")])
         "↔"
         («term_=_» («term_%_» `p "%" (num "4")) "=" (num "3")))))
      (Command.declValSimple
       ":="
       (Term.anonymousCtor
        "⟨"
        [(Term.app `mod_four_eq_three_of_nat_prime_of_prime [`p])
         ","
         (Term.app `prime_of_nat_prime_of_mod_four_eq_three [`p])]
        "⟩")
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.app `mod_four_eq_three_of_nat_prime_of_prime [`p])
        ","
        (Term.app `prime_of_nat_prime_of_mod_four_eq_three [`p])]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `prime_of_nat_prime_of_mod_four_eq_three [`p])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `prime_of_nat_prime_of_mod_four_eq_three
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `mod_four_eq_three_of_nat_prime_of_prime [`p])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `mod_four_eq_three_of_nat_prime_of_prime
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_↔_»
       (Term.app
        `Prime
        [(Term.typeAscription
          "("
          `p
          ":"
          [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")]
          ")")])
       "↔"
       («term_=_» («term_%_» `p "%" (num "4")) "=" (num "3")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_» («term_%_» `p "%" (num "4")) "=" (num "3"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "3")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      («term_%_» `p "%" (num "4"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "4")
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 70, (some 71, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 21 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 20, term))
      (Term.app
       `Prime
       [(Term.typeAscription "(" `p ":" [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")] ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription "(" `p ":" [(NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]» "ℤ[i]")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.Zsqrtd.GaussianInt.«termℤ[i]»', expected 'NumberTheory.Zsqrtd.GaussianInt.termℤ[i]._@.NumberTheory.Zsqrtd.GaussianInt._hyg.6'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/-- A prime natural number is prime in `ℤ[i]` if and only if it is `3` mod `4` -/
  theorem
    prime_iff_mod_four_eq_three_of_nat_prime
    ( p : ℕ ) [ hp : Fact p . Prime ] : Prime ( p : ℤ[i] ) ↔ p % 4 = 3
    := ⟨ mod_four_eq_three_of_nat_prime_of_prime p , prime_of_nat_prime_of_mod_four_eq_three p ⟩
#align
  gaussian_int.prime_iff_mod_four_eq_three_of_nat_prime GaussianInt.prime_iff_mod_four_eq_three_of_nat_prime

end GaussianInt

