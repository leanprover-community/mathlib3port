/-
Copyright (c) 2020 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon

! This file was ported from Lean 3 source module control.random
! leanprover-community/mathlib commit 26f081a2fb920140ed5bc5cc5344e84bcc7cb2b2
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Control.Uliftable
import Mathbin.Data.Bitvec.Basic
import Mathbin.Data.Stream.Defs
import Mathbin.Tactic.NormNum

/-!
# Rand Monad and Random Class

This module provides tools for formulating computations guided by randomness and for
defining objects that can be created randomly.

## Main definitions
  * `rand` monad for computations guided by randomness;
  * `random` class for objects that can be generated randomly;
    * `random` to generate one object;
    * `random_r` to generate one object inside a range;
    * `random_series` to generate an infinite series of objects;
    * `random_series_r` to generate an infinite series of objects inside a range;
  * `io.mk_generator` to create a new random number generator;
  * `io.run_rand` to run a randomized computation inside the `io` monad;
  * `tactic.run_rand` to run a randomized computation inside the `tactic` monad

## Local notation

 * `i .. j` : `Icc i j`, the set of values between `i` and `j` inclusively;

## Tags

random monad io

## References

  * Similar library in Haskell: https://hackage.haskell.org/package/MonadRandom

-/


open List Io Applicative

universe u v w

#print RandG /-
/-- A monad to generate random objects using the generator type `g` -/
@[reducible]
def RandG (g : Type) (α : Type u) : Type u :=
  StateM (ULift.{u} g) α
#align rand_g RandG
-/

#print Rand /-
/-- A monad to generate random objects using the generator type `std_gen` -/
@[reducible]
def Rand :=
  RandG StdGen
#align rand Rand
-/

instance (g : Type) : Uliftable (RandG.{u} g) (RandG.{v} g) :=
  @StateT.uliftable' _ _ _ _ _ (Equiv.ulift.trans Equiv.ulift.symm)

open ULift hiding Inhabited

/-- Generate one more `ℕ` -/
def RandG.next {g : Type} [RandomGen g] : RandG g ℕ :=
  ⟨Prod.map id up ∘ RandomGen.next ∘ down⟩
#align rand_g.next RandG.next

-- mathport name: «expr .. »
local infixl:41 " .. " => Set.Icc

open Stream'

#print BoundedRandom /-
/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "`bounded_random α` gives us machinery to generate values of type `α` between certain bounds -/")]
      []
      []
      []
      []
      [])
     (Command.structure
      (Command.classTk "class")
      (Command.declId `BoundedRandom [])
      [(Term.explicitBinder "(" [`α] [":" (Term.type "Type" [`u])] [] ")")
       (Term.instBinder "[" [] (Term.app `Preorder [`α]) "]")]
      []
      []
      ["where"
       []
       (Command.structFields
        [(Command.structSimpleBinder
          (Command.declModifiers [] [] [] [] [] [])
          `randomR
          (Command.optDeclSig
           []
           [(Term.typeSpec
             ":"
             (Term.forall
              "∀"
              [(Term.explicitBinder "(" [`g] [] [] ")")
               (Term.instBinder "[" [] (Term.app `RandomGen [`g]) "]")
               (Term.explicitBinder "(" [`x `y] [":" `α] [] ")")]
              []
              ","
              (Term.arrow
               («term_≤_» `x "≤" `y)
               "→"
               (Term.app `RandG [`g (Control.Random.«term_.._» `x " .. " `y)]))))])
          [])])]
      (Command.optDeriving [])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.structure', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.structure', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.structure', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.structure', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.structure', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.structure', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.structure', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.structure', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.structure', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.structSimpleBinder', expected 'Lean.Parser.Command.structExplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.structSimpleBinder', expected 'Lean.Parser.Command.structImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.structSimpleBinder', expected 'Lean.Parser.Command.structInstBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.forall
       "∀"
       [(Term.explicitBinder "(" [`g] [] [] ")")
        (Term.instBinder "[" [] (Term.app `RandomGen [`g]) "]")
        (Term.explicitBinder "(" [`x `y] [":" `α] [] ")")]
       []
       ","
       (Term.arrow
        («term_≤_» `x "≤" `y)
        "→"
        (Term.app `RandG [`g (Control.Random.«term_.._» `x " .. " `y)])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.arrow
       («term_≤_» `x "≤" `y)
       "→"
       (Term.app `RandG [`g (Control.Random.«term_.._» `x " .. " `y)]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `RandG [`g (Control.Random.«term_.._» `x " .. " `y)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Control.Random.«term_.._»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Control.Random.«term_.._»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Control.Random.«term_.._» `x " .. " `y)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Control.Random.«term_.._»', expected 'Control.Random.term_.._._@.Control.Random._hyg.9'-/-- failed to format: format: uncaught backtrack exception
/-- `bounded_random α` gives us machinery to generate values of type `α` between certain bounds -/
  class
    BoundedRandom
    ( α : Type u ) [ Preorder α ]
    where randomR : ∀ ( g ) [ RandomGen g ] ( x y : α ) , x ≤ y → RandG g x .. y
#align bounded_random BoundedRandom
-/

#print Random /-
/- ./././Mathport/Syntax/Translate/Command.lean:379:30: infer kinds are unsupported in Lean 4: #[`Random] [] -/
/-- `random α` gives us machinery to generate values of type `α` -/
class Random (α : Type u) where
  Random : ∀ (g : Type) [RandomGen g], RandG g α
#align random Random
-/

/-- shift_31_left = 2^31; multiplying by it shifts the binary
representation of a number left by 31 bits, dividing by it shifts it
right by 31 bits -/
def shift31Left : ℕ := by apply_normed 2 ^ 31
#align shift_31_left shift31Left

namespace Rand

open Stream'

variable (α : Type u)

variable (g : Type) [RandomGen g]

#print Rand.split /-
/-- create a new random number generator distinct from the one stored in the state -/
def split : RandG g g :=
  ⟨Prod.map id up ∘ RandomGen.split ∘ down⟩
#align rand.split Rand.split
-/

variable {g}

section Random

variable [Random α]

export Random (Random)

/-- Generate a random value of type `α`. -/
def random : RandG g α :=
  Random.random α g
#align rand.random Rand.random

/-- generate an infinite series of random values of type `α` -/
def randomSeries : RandG g (Stream' α) := do
  let gen ← Uliftable.up (split g)
  pure <| Stream'.corecState (Random.random α g) gen
#align rand.random_series Rand.randomSeries

end Random

variable {α}

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment "/--" "Generate a random value between `x` and `y` inclusive. -/")]
      []
      []
      []
      []
      [])
     (Command.def
      "def"
      (Command.declId `randomR [])
      (Command.optDeclSig
       [(Term.instBinder "[" [] (Term.app `Preorder [`α]) "]")
        (Term.instBinder "[" [] (Term.app `BoundedRandom [`α]) "]")
        (Term.explicitBinder "(" [`x `y] [":" `α] [] ")")
        (Term.explicitBinder "(" [`h] [":" («term_≤_» `x "≤" `y)] [] ")")]
       [(Term.typeSpec ":" (Term.app `RandG [`g (Control.Random.«term_.._» `x " .. " `y)]))])
      (Command.declValSimple ":=" (Term.app `BoundedRandom.randomR [`g `x `y `h]) [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `BoundedRandom.randomR [`g `x `y `h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `BoundedRandom.randomR
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app `RandG [`g (Control.Random.«term_.._» `x " .. " `y)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Control.Random.«term_.._»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Control.Random.«term_.._»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Control.Random.«term_.._» `x " .. " `y)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Control.Random.«term_.._»', expected 'Control.Random.term_.._._@.Control.Random._hyg.9'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/-- Generate a random value between `x` and `y` inclusive. -/
  def
    randomR
    [ Preorder α ] [ BoundedRandom α ] ( x y : α ) ( h : x ≤ y ) : RandG g x .. y
    := BoundedRandom.randomR g x y h
#align rand.random_r Rand.randomR

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "generate an infinite series of random values of type `α` between `x` and `y` inclusive. -/")]
      []
      []
      []
      []
      [])
     (Command.def
      "def"
      (Command.declId `randomSeriesR [])
      (Command.optDeclSig
       [(Term.instBinder "[" [] (Term.app `Preorder [`α]) "]")
        (Term.instBinder "[" [] (Term.app `BoundedRandom [`α]) "]")
        (Term.explicitBinder "(" [`x `y] [":" `α] [] ")")
        (Term.explicitBinder "(" [`h] [":" («term_≤_» `x "≤" `y)] [] ")")]
       [(Term.typeSpec
         ":"
         (Term.app `RandG [`g (Term.app `Stream' [(Control.Random.«term_.._» `x " .. " `y)])]))])
      (Command.declValSimple
       ":="
       (Term.do
        "do"
        (Term.doSeqIndent
         [(Term.doSeqItem
           (Term.doLetArrow
            "let"
            []
            (Term.doIdDecl
             `gen
             []
             "←"
             (Term.doExpr (Term.app `Uliftable.up [(Term.app `split [`g])]))))
           [])
          (Term.doSeqItem
           (Term.doExpr
            («term_<|_»
             `pure
             "<|"
             (Term.app `corec_state [(Term.app `BoundedRandom.randomR [`g `x `y `h]) `gen])))
           [])]))
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.do
       "do"
       (Term.doSeqIndent
        [(Term.doSeqItem
          (Term.doLetArrow
           "let"
           []
           (Term.doIdDecl
            `gen
            []
            "←"
            (Term.doExpr (Term.app `Uliftable.up [(Term.app `split [`g])]))))
          [])
         (Term.doSeqItem
          (Term.doExpr
           («term_<|_»
            `pure
            "<|"
            (Term.app `corec_state [(Term.app `BoundedRandom.randomR [`g `x `y `h]) `gen])))
          [])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doSeqIndent', expected 'Lean.Parser.Term.doSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_»
       `pure
       "<|"
       (Term.app `corec_state [(Term.app `BoundedRandom.randomR [`g `x `y `h]) `gen]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `corec_state [(Term.app `BoundedRandom.randomR [`g `x `y `h]) `gen])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `gen
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `BoundedRandom.randomR [`g `x `y `h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `BoundedRandom.randomR
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `BoundedRandom.randomR [`g `x `y `h])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `corec_state
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      `pure
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 10, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, doElem))
      (Term.app `Uliftable.up [(Term.app `split [`g])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `split [`g])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `split
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `split [`g]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Uliftable.up
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, doElem)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1023, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app `RandG [`g (Term.app `Stream' [(Control.Random.«term_.._» `x " .. " `y)])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Stream' [(Control.Random.«term_.._» `x " .. " `y)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Control.Random.«term_.._»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Control.Random.«term_.._»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Control.Random.«term_.._» `x " .. " `y)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Control.Random.«term_.._»', expected 'Control.Random.term_.._._@.Control.Random._hyg.9'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/-- generate an infinite series of random values of type `α` between `x` and `y` inclusive. -/
  def
    randomSeriesR
    [ Preorder α ] [ BoundedRandom α ] ( x y : α ) ( h : x ≤ y ) : RandG g Stream' x .. y
    := do let gen ← Uliftable.up split g pure <| corec_state BoundedRandom.randomR g x y h gen
#align rand.random_series_r Rand.randomSeriesR

end Rand

namespace Io

private def accum_char (w : ℕ) (c : Char) : ℕ :=
  c.toNat + 256 * w
#align io.accum_char io.accum_char

/-- create and seed a random number generator -/
def mkGenerator : Io StdGen := do
  let seed ← Io.rand 0 shift31Left
  return <| mkStdGen seed
#align io.mk_generator Io.mkGenerator

variable {α : Type}

/-- Run `cmd` using a randomly seeded random number generator -/
def runRand (cmd : Rand α) : Io α := do
  let g ← Io.mkGenerator
  return <| (cmd ⟨g⟩).1
#align io.run_rand Io.runRand

/-- Run `cmd` using the provided seed. -/
def runRandWith (seed : ℕ) (cmd : Rand α) : Io α :=
  return <| (cmd.run ⟨mkStdGen seed⟩).1
#align io.run_rand_with Io.runRandWith

section Random

variable [Random α]

/-- randomly generate a value of type α -/
def random : Io α :=
  Io.runRand (Rand.random α)
#align io.random Io.random

/-- randomly generate an infinite series of value of type α -/
def randomSeries : Io (Stream' α) :=
  Io.runRand (Rand.randomSeries α)
#align io.random_series Io.randomSeries

end Random

section BoundedRandom

variable [Preorder α] [BoundedRandom α]

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment "/--" "randomly generate a value of type α between `x` and `y` -/")]
      []
      []
      []
      []
      [])
     (Command.def
      "def"
      (Command.declId `randomR [])
      (Command.optDeclSig
       [(Term.explicitBinder "(" [`x `y] [":" `α] [] ")")
        (Term.explicitBinder "(" [`p] [":" («term_≤_» `x "≤" `y)] [] ")")]
       [(Term.typeSpec ":" (Term.app `Io [(Control.Random.«term_.._» `x " .. " `y)]))])
      (Command.declValSimple
       ":="
       (Term.app `Io.runRand [(Term.app `BoundedRandom.randomR [(Term.hole "_") `x `y `p])])
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Io.runRand [(Term.app `BoundedRandom.randomR [(Term.hole "_") `x `y `p])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `BoundedRandom.randomR [(Term.hole "_") `x `y `p])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `BoundedRandom.randomR
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `BoundedRandom.randomR [(Term.hole "_") `x `y `p])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Io.runRand
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app `Io [(Control.Random.«term_.._» `x " .. " `y)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Control.Random.«term_.._»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Control.Random.«term_.._»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Control.Random.«term_.._» `x " .. " `y)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Control.Random.«term_.._»', expected 'Control.Random.term_.._._@.Control.Random._hyg.9'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/-- randomly generate a value of type α between `x` and `y` -/
  def randomR ( x y : α ) ( p : x ≤ y ) : Io x .. y := Io.runRand BoundedRandom.randomR _ x y p
#align io.random_r Io.randomR

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "randomly generate an infinite series of value of type α between `x` and `y` -/")]
      []
      []
      []
      []
      [])
     (Command.def
      "def"
      (Command.declId `randomSeriesR [])
      (Command.optDeclSig
       [(Term.explicitBinder "(" [`x `y] [":" `α] [] ")")
        (Term.explicitBinder "(" [`h] [":" («term_≤_» `x "≤" `y)] [] ")")]
       [(Term.typeSpec
         ":"
         (Term.app `Io [(«term_<|_» `Stream' "<|" (Control.Random.«term_.._» `x " .. " `y))]))])
      (Command.declValSimple
       ":="
       (Term.app `Io.runRand [(Term.app `Rand.randomSeriesR [`x `y `h])])
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Io.runRand [(Term.app `Rand.randomSeriesR [`x `y `h])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Rand.randomSeriesR [`x `y `h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Rand.randomSeriesR
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `Rand.randomSeriesR [`x `y `h])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Io.runRand
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app `Io [(«term_<|_» `Stream' "<|" (Control.Random.«term_.._» `x " .. " `y))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_<|_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_<|_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_» `Stream' "<|" (Control.Random.«term_.._» `x " .. " `y))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Control.Random.«term_.._» `x " .. " `y)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Control.Random.«term_.._»', expected 'Control.Random.term_.._._@.Control.Random._hyg.9'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/-- randomly generate an infinite series of value of type α between `x` and `y` -/
  def
    randomSeriesR
    ( x y : α ) ( h : x ≤ y ) : Io Stream' <| x .. y
    := Io.runRand Rand.randomSeriesR x y h
#align io.random_series_r Io.randomSeriesR

end BoundedRandom

end Io

namespace Tactic

/-- create a seeded random number generator in the `tactic` monad -/
unsafe def mk_generator : tactic StdGen := do
  tactic.unsafe_run_io @Io.mkGenerator
#align tactic.mk_generator tactic.mk_generator

/-- run `cmd` using the a randomly seeded random number generator
in the tactic monad -/
unsafe def run_rand {α : Type u} (cmd : Rand α) : tactic α := do
  let ⟨g⟩ ← tactic.up mk_generator
  return (cmd ⟨g⟩).1
#align tactic.run_rand tactic.run_rand

variable {α : Type u}

section BoundedRandom

variable [Preorder α] [BoundedRandom α]

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment "/--" "Generate a random value between `x` and `y` inclusive. -/")]
      []
      []
      []
      [(Command.unsafe "unsafe")]
      [])
     (Command.def
      "def"
      (Command.declId `random_r [])
      (Command.optDeclSig
       [(Term.explicitBinder "(" [`x `y] [":" `α] [] ")")
        (Term.explicitBinder "(" [`h] [":" («term_≤_» `x "≤" `y)] [] ")")]
       [(Term.typeSpec ":" (Term.app `tactic [(Control.Random.«term_.._» `x " .. " `y)]))])
      (Command.declValSimple ":=" (Term.app `run_rand [(Term.app `Rand.randomR [`x `y `h])]) [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `run_rand [(Term.app `Rand.randomR [`x `y `h])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Rand.randomR [`x `y `h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Rand.randomR
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `Rand.randomR [`x `y `h]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `run_rand
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app `tactic [(Control.Random.«term_.._» `x " .. " `y)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Control.Random.«term_.._»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Control.Random.«term_.._»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Control.Random.«term_.._» `x " .. " `y)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Control.Random.«term_.._»', expected 'Control.Random.term_.._._@.Control.Random._hyg.9'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/-- Generate a random value between `x` and `y` inclusive. -/ unsafe
  def random_r ( x y : α ) ( h : x ≤ y ) : tactic x .. y := run_rand Rand.randomR x y h
#align tactic.random_r tactic.random_r

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "Generate an infinite series of random values of type `α` between `x` and `y` inclusive. -/")]
      []
      []
      []
      [(Command.unsafe "unsafe")]
      [])
     (Command.def
      "def"
      (Command.declId `random_series_r [])
      (Command.optDeclSig
       [(Term.explicitBinder "(" [`x `y] [":" `α] [] ")")
        (Term.explicitBinder "(" [`h] [":" («term_≤_» `x "≤" `y)] [] ")")]
       [(Term.typeSpec
         ":"
         (Term.app `tactic [(«term_<|_» `Stream' "<|" (Control.Random.«term_.._» `x " .. " `y))]))])
      (Command.declValSimple
       ":="
       (Term.app `run_rand [(Term.app `Rand.randomSeriesR [`x `y `h])])
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `run_rand [(Term.app `Rand.randomSeriesR [`x `y `h])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Rand.randomSeriesR [`x `y `h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Rand.randomSeriesR
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `Rand.randomSeriesR [`x `y `h])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `run_rand
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app `tactic [(«term_<|_» `Stream' "<|" (Control.Random.«term_.._» `x " .. " `y))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_<|_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_<|_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_» `Stream' "<|" (Control.Random.«term_.._» `x " .. " `y))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Control.Random.«term_.._» `x " .. " `y)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Control.Random.«term_.._»', expected 'Control.Random.term_.._._@.Control.Random._hyg.9'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/-- Generate an infinite series of random values of type `α` between `x` and `y` inclusive. -/
    unsafe
  def
    random_series_r
    ( x y : α ) ( h : x ≤ y ) : tactic Stream' <| x .. y
    := run_rand Rand.randomSeriesR x y h
#align tactic.random_series_r tactic.random_series_r

end BoundedRandom

section Random

variable [Random α]

/-- randomly generate a value of type α -/
unsafe def random : tactic α :=
  run_rand (Rand.random α)
#align tactic.random tactic.random

/-- randomly generate an infinite series of value of type α -/
unsafe def random_series : tactic (Stream' α) :=
  run_rand (Rand.randomSeries α)
#align tactic.random_series tactic.random_series

end Random

end Tactic

open Nat (succ one_add mod_eq_of_lt zero_lt_succ add_one succ_le_succ)

variable {g : Type} [RandomGen g]

open Nat

namespace Fin

variable {n : ℕ} [NeZero n]

/-- generate a `fin` randomly -/
protected def random : RandG g (Fin n) :=
  ⟨fun ⟨g⟩ => Prod.map ofNat' up <| randNat g 0 n⟩
#align fin.random Fin.random

end Fin

open Nat

instance natBoundedRandom : BoundedRandom ℕ
    where randomR g inst x y hxy := do
    let z ← @Fin.random g inst (succ <| y - x) _
    pure
        ⟨z + x, Nat.le_add_left _ _, by
          rw [← le_tsub_iff_right hxy] <;> apply le_of_succ_le_succ z.is_lt⟩
#align nat_bounded_random natBoundedRandom

/-- This `bounded_random` interval generates integers between `x` and
`y` by first generating a natural number between `0` and `y - x` and
shifting the result appropriately. -/
instance intBoundedRandom : BoundedRandom ℤ
    where randomR g inst x y hxy := do
    let ⟨z, h₀, h₁⟩ ← @BoundedRandom.randomR ℕ _ _ g inst 0 (Int.natAbs <| y - x) (by decide)
    pure
        ⟨z + x, Int.le_add_of_nonneg_left (Int.coe_nat_nonneg _),
          Int.add_le_of_le_sub_right <|
            le_trans (Int.ofNat_le_ofNat_of_le h₁)
              (le_of_eq <| Int.of_nat_nat_abs_eq_of_nonneg (Int.sub_nonneg_of_le hxy))⟩
#align int_bounded_random intBoundedRandom

instance finRandom (n : ℕ) [NeZero n] : Random (Fin n) where Random g inst := @Fin.random g inst _ _
#align fin_random finRandom

instance finBoundedRandom (n : ℕ) : BoundedRandom (Fin n)
    where randomR g inst (x y : Fin n) p := do
    let ⟨r, h, h'⟩ ← @Rand.randomR ℕ g inst _ _ x.val y.val p
    pure ⟨⟨r, lt_of_le_of_lt h' y⟩, h, h'⟩
#align fin_bounded_random finBoundedRandom

/-- A shortcut for creating a `random (fin n)` instance from
a proof that `0 < n` rather than on matching on `fin (succ n)`  -/
def randomFinOfPos : ∀ {n : ℕ} (h : 0 < n), Random (Fin n)
  | succ n, _ => finRandom _
  | 0, h => False.elim (Nat.not_lt_zero _ h)
#align random_fin_of_pos randomFinOfPos

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `bool_of_nat_mem_Icc_of_mem_Icc_to_nat [])
      (Command.declSig
       [(Term.explicitBinder "(" [`x `y] [":" `Bool] [] ")")
        (Term.explicitBinder "(" [`n] [":" (termℕ "ℕ")] [] ")")]
       (Term.typeSpec
        ":"
        (Term.arrow
         («term_∈_»
          `n
          "∈"
          (Control.Random.«term_.._» (Term.proj `x "." `toNat) " .. " (Term.proj `y "." `toNat)))
         "→"
         («term_∈_» (Term.app `Bool.ofNat [`n]) "∈" (Control.Random.«term_.._» `x " .. " `y)))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.simp
            "simp"
            []
            []
            ["only"]
            ["[" [(Tactic.simpLemma [] [] `and_imp) "," (Tactic.simpLemma [] [] `Set.mem_Icc)] "]"]
            [])
           ";"
           (Tactic.intro "intro" [`h₀ `h₁])
           []
           (Tactic.«tactic_<;>_»
            (Tactic.«tactic_<;>_»
             (Std.Tactic.seq_focus
              (Tactic.constructor "constructor")
              "<;>"
              "["
              [(Tactic.tacticHave_
                "have"
                (Term.haveDecl
                 (Term.haveIdDecl [`h₂ []] [] ":=" (Term.app `Bool.of_nat_le_of_nat [`h₀]))))
               ","
               (Tactic.tacticHave_
                "have"
                (Term.haveDecl
                 (Term.haveIdDecl [`h₂ []] [] ":=" (Term.app `Bool.of_nat_le_of_nat [`h₁]))))]
              "]")
             "<;>"
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Bool.of_nat_to_nat)] "]")
              [(Tactic.location "at" (Tactic.locationHyp [`h₂] []))]))
            "<;>"
            (Tactic.exact "exact" `h₂))])))
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
         [(Tactic.simp
           "simp"
           []
           []
           ["only"]
           ["[" [(Tactic.simpLemma [] [] `and_imp) "," (Tactic.simpLemma [] [] `Set.mem_Icc)] "]"]
           [])
          ";"
          (Tactic.intro "intro" [`h₀ `h₁])
          []
          (Tactic.«tactic_<;>_»
           (Tactic.«tactic_<;>_»
            (Std.Tactic.seq_focus
             (Tactic.constructor "constructor")
             "<;>"
             "["
             [(Tactic.tacticHave_
               "have"
               (Term.haveDecl
                (Term.haveIdDecl [`h₂ []] [] ":=" (Term.app `Bool.of_nat_le_of_nat [`h₀]))))
              ","
              (Tactic.tacticHave_
               "have"
               (Term.haveDecl
                (Term.haveIdDecl [`h₂ []] [] ":=" (Term.app `Bool.of_nat_le_of_nat [`h₁]))))]
             "]")
            "<;>"
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Bool.of_nat_to_nat)] "]")
             [(Tactic.location "at" (Tactic.locationHyp [`h₂] []))]))
           "<;>"
           (Tactic.exact "exact" `h₂))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.«tactic_<;>_»
       (Tactic.«tactic_<;>_»
        (Std.Tactic.seq_focus
         (Tactic.constructor "constructor")
         "<;>"
         "["
         [(Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl [`h₂ []] [] ":=" (Term.app `Bool.of_nat_le_of_nat [`h₀]))))
          ","
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl [`h₂ []] [] ":=" (Term.app `Bool.of_nat_le_of_nat [`h₁]))))]
         "]")
        "<;>"
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Bool.of_nat_to_nat)] "]")
         [(Tactic.location "at" (Tactic.locationHyp [`h₂] []))]))
       "<;>"
       (Tactic.exact "exact" `h₂))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" `h₂)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h₂
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 2 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
      (Tactic.«tactic_<;>_»
       (Std.Tactic.seq_focus
        (Tactic.constructor "constructor")
        "<;>"
        "["
        [(Tactic.tacticHave_
          "have"
          (Term.haveDecl
           (Term.haveIdDecl [`h₂ []] [] ":=" (Term.app `Bool.of_nat_le_of_nat [`h₀]))))
         ","
         (Tactic.tacticHave_
          "have"
          (Term.haveDecl
           (Term.haveIdDecl [`h₂ []] [] ":=" (Term.app `Bool.of_nat_le_of_nat [`h₁]))))]
        "]")
       "<;>"
       (Tactic.rwSeq
        "rw"
        []
        (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Bool.of_nat_to_nat)] "]")
        [(Tactic.location "at" (Tactic.locationHyp [`h₂] []))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Bool.of_nat_to_nat)] "]")
       [(Tactic.location "at" (Tactic.locationHyp [`h₂] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h₂
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Bool.of_nat_to_nat
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 2 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
      (Std.Tactic.seq_focus
       (Tactic.constructor "constructor")
       "<;>"
       "["
       [(Tactic.tacticHave_
         "have"
         (Term.haveDecl (Term.haveIdDecl [`h₂ []] [] ":=" (Term.app `Bool.of_nat_le_of_nat [`h₀]))))
        ","
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl [`h₂ []] [] ":=" (Term.app `Bool.of_nat_le_of_nat [`h₁]))))]
       "]")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl (Term.haveIdDecl [`h₂ []] [] ":=" (Term.app `Bool.of_nat_le_of_nat [`h₁]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Bool.of_nat_le_of_nat [`h₁])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Bool.of_nat_le_of_nat
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl (Term.haveIdDecl [`h₂ []] [] ":=" (Term.app `Bool.of_nat_le_of_nat [`h₀]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Bool.of_nat_le_of_nat [`h₀])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h₀
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Bool.of_nat_le_of_nat
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
      (Tactic.constructor "constructor")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.intro "intro" [`h₀ `h₁])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h₁
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `h₀
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["[" [(Tactic.simpLemma [] [] `and_imp) "," (Tactic.simpLemma [] [] `Set.mem_Icc)] "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Set.mem_Icc
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `and_imp
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.arrow
       («term_∈_»
        `n
        "∈"
        (Control.Random.«term_.._» (Term.proj `x "." `toNat) " .. " (Term.proj `y "." `toNat)))
       "→"
       («term_∈_» (Term.app `Bool.ofNat [`n]) "∈" (Control.Random.«term_.._» `x " .. " `y)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∈_» (Term.app `Bool.ofNat [`n]) "∈" (Control.Random.«term_.._» `x " .. " `y))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Control.Random.«term_.._» `x " .. " `y)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Control.Random.«term_.._»', expected 'Control.Random.term_.._._@.Control.Random._hyg.9'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  bool_of_nat_mem_Icc_of_mem_Icc_to_nat
  ( x y : Bool ) ( n : ℕ ) : n ∈ x . toNat .. y . toNat → Bool.ofNat n ∈ x .. y
  :=
    by
      simp only [ and_imp , Set.mem_Icc ]
        ;
        intro h₀ h₁
        constructor
              <;>
              [
              have h₂ := Bool.of_nat_le_of_nat h₀ , have h₂ := Bool.of_nat_le_of_nat h₁
              ]
            <;>
            rw [ Bool.of_nat_to_nat ] at h₂
          <;>
          exact h₂
#align bool_of_nat_mem_Icc_of_mem_Icc_to_nat bool_of_nat_mem_Icc_of_mem_Icc_to_nat

instance : Random Bool
    where Random g inst :=
    (Bool.ofNat ∘ Subtype.val) <$> @BoundedRandom.randomR ℕ _ _ g inst 0 1 (Nat.zero_le _)

instance : BoundedRandom Bool
    where randomR g _inst x y p :=
    Subtype.map Bool.ofNat (bool_of_nat_mem_Icc_of_mem_Icc_to_nat x y) <$>
      @BoundedRandom.randomR ℕ _ _ g _inst x.toNat y.toNat (Bool.to_nat_le_to_nat p)

/-- generate a random bit vector of length `n` -/
def Bitvec.random (n : ℕ) : RandG g (Bitvec n) :=
  Bitvec.ofFin <$> Rand.random (Fin <| 2 ^ n)
#align bitvec.random Bitvec.random

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment "/--" "generate a random bit vector of length `n` -/")]
      []
      []
      []
      []
      [])
     (Command.def
      "def"
      (Command.declId `Bitvec.randomR [])
      (Command.optDeclSig
       [(Term.implicitBinder "{" [`n] [":" (termℕ "ℕ")] "}")
        (Term.explicitBinder "(" [`x `y] [":" (Term.app `Bitvec [`n])] [] ")")
        (Term.explicitBinder "(" [`h] [":" («term_≤_» `x "≤" `y)] [] ")")]
       [(Term.typeSpec ":" (Term.app `RandG [`g (Control.Random.«term_.._» `x " .. " `y)]))])
      (Command.declValSimple
       ":="
       (Term.have
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`h' []]
          [(Term.typeSpec
            ":"
            (Term.forall
             "∀"
             [`a]
             [(Term.typeSpec ":" (Term.app `Fin [(«term_^_» (num "2") "^" `n)]))]
             ","
             (Term.arrow
              («term_∈_»
               `a
               "∈"
               (Control.Random.«term_.._»
                (Term.proj `x "." `toFin)
                " .. "
                (Term.proj `y "." `toFin)))
              "→"
              («term_∈_»
               (Term.app `Bitvec.ofFin [`a])
               "∈"
               (Control.Random.«term_.._» `x " .. " `y)))))]
          ":="
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
                [(Tactic.simpLemma [] [] `and_imp) "," (Tactic.simpLemma [] [] `Set.mem_Icc)]
                "]"]
               [])
              ";"
              (Tactic.intro "intro" [`z `h₀ `h₁])
              []
              (Mathlib.Tactic.tacticReplace_
               "replace"
               (Term.haveDecl
                (Term.haveIdDecl [`h₀ []] [] ":=" (Term.app `Bitvec.of_fin_le_of_fin_of_le [`h₀]))))
              []
              (Mathlib.Tactic.tacticReplace_
               "replace"
               (Term.haveDecl
                (Term.haveIdDecl [`h₁ []] [] ":=" (Term.app `Bitvec.of_fin_le_of_fin_of_le [`h₁]))))
              []
              (Tactic.rwSeq
               "rw"
               []
               (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Bitvec.of_fin_to_fin)] "]")
               [(Tactic.location "at" (Tactic.locationHyp [`h₀ `h₁] []))])
              ";"
              (Tactic.«tactic_<;>_»
               (Tactic.constructor "constructor")
               "<;>"
               (Tactic.assumption "assumption"))])))))
        []
        («term_<$>_»
         (Term.app `Subtype.map [`Bitvec.ofFin `h'])
         "<$>"
         (Term.app
          `Rand.randomR
          [(Term.proj `x "." `toFin)
           (Term.proj `y "." `toFin)
           (Term.app `Bitvec.to_fin_le_to_fin_of_le [`h])])))
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.have
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`h' []]
         [(Term.typeSpec
           ":"
           (Term.forall
            "∀"
            [`a]
            [(Term.typeSpec ":" (Term.app `Fin [(«term_^_» (num "2") "^" `n)]))]
            ","
            (Term.arrow
             («term_∈_»
              `a
              "∈"
              (Control.Random.«term_.._»
               (Term.proj `x "." `toFin)
               " .. "
               (Term.proj `y "." `toFin)))
             "→"
             («term_∈_»
              (Term.app `Bitvec.ofFin [`a])
              "∈"
              (Control.Random.«term_.._» `x " .. " `y)))))]
         ":="
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
               [(Tactic.simpLemma [] [] `and_imp) "," (Tactic.simpLemma [] [] `Set.mem_Icc)]
               "]"]
              [])
             ";"
             (Tactic.intro "intro" [`z `h₀ `h₁])
             []
             (Mathlib.Tactic.tacticReplace_
              "replace"
              (Term.haveDecl
               (Term.haveIdDecl [`h₀ []] [] ":=" (Term.app `Bitvec.of_fin_le_of_fin_of_le [`h₀]))))
             []
             (Mathlib.Tactic.tacticReplace_
              "replace"
              (Term.haveDecl
               (Term.haveIdDecl [`h₁ []] [] ":=" (Term.app `Bitvec.of_fin_le_of_fin_of_le [`h₁]))))
             []
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Bitvec.of_fin_to_fin)] "]")
              [(Tactic.location "at" (Tactic.locationHyp [`h₀ `h₁] []))])
             ";"
             (Tactic.«tactic_<;>_»
              (Tactic.constructor "constructor")
              "<;>"
              (Tactic.assumption "assumption"))])))))
       []
       («term_<$>_»
        (Term.app `Subtype.map [`Bitvec.ofFin `h'])
        "<$>"
        (Term.app
         `Rand.randomR
         [(Term.proj `x "." `toFin)
          (Term.proj `y "." `toFin)
          (Term.app `Bitvec.to_fin_le_to_fin_of_le [`h])])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<$>_»
       (Term.app `Subtype.map [`Bitvec.ofFin `h'])
       "<$>"
       (Term.app
        `Rand.randomR
        [(Term.proj `x "." `toFin)
         (Term.proj `y "." `toFin)
         (Term.app `Bitvec.to_fin_le_to_fin_of_le [`h])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Rand.randomR
       [(Term.proj `x "." `toFin)
        (Term.proj `y "." `toFin)
        (Term.app `Bitvec.to_fin_le_to_fin_of_le [`h])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Bitvec.to_fin_le_to_fin_of_le [`h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Bitvec.to_fin_le_to_fin_of_le
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `Bitvec.to_fin_le_to_fin_of_le [`h])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj `y "." `toFin)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `y
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj `x "." `toFin)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Rand.randomR
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 100 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 100, term))
      (Term.app `Subtype.map [`Bitvec.ofFin `h'])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `Bitvec.ofFin
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Subtype.map
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 101 >? 1022, (some 1023, term) <=? (some 100, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 100, (some 100, term) <=? (none, [anonymous])
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
           ["[" [(Tactic.simpLemma [] [] `and_imp) "," (Tactic.simpLemma [] [] `Set.mem_Icc)] "]"]
           [])
          ";"
          (Tactic.intro "intro" [`z `h₀ `h₁])
          []
          (Mathlib.Tactic.tacticReplace_
           "replace"
           (Term.haveDecl
            (Term.haveIdDecl [`h₀ []] [] ":=" (Term.app `Bitvec.of_fin_le_of_fin_of_le [`h₀]))))
          []
          (Mathlib.Tactic.tacticReplace_
           "replace"
           (Term.haveDecl
            (Term.haveIdDecl [`h₁ []] [] ":=" (Term.app `Bitvec.of_fin_le_of_fin_of_le [`h₁]))))
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Bitvec.of_fin_to_fin)] "]")
           [(Tactic.location "at" (Tactic.locationHyp [`h₀ `h₁] []))])
          ";"
          (Tactic.«tactic_<;>_»
           (Tactic.constructor "constructor")
           "<;>"
           (Tactic.assumption "assumption"))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.«tactic_<;>_»
       (Tactic.constructor "constructor")
       "<;>"
       (Tactic.assumption "assumption"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.assumption "assumption")
[PrettyPrinter.parenthesize] ...precedences are 2 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
      (Tactic.constructor "constructor")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Bitvec.of_fin_to_fin)] "]")
       [(Tactic.location "at" (Tactic.locationHyp [`h₀ `h₁] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h₁
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `h₀
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Bitvec.of_fin_to_fin
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.tacticReplace_
       "replace"
       (Term.haveDecl
        (Term.haveIdDecl [`h₁ []] [] ":=" (Term.app `Bitvec.of_fin_le_of_fin_of_le [`h₁]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Bitvec.of_fin_le_of_fin_of_le [`h₁])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Bitvec.of_fin_le_of_fin_of_le
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.tacticReplace_
       "replace"
       (Term.haveDecl
        (Term.haveIdDecl [`h₀ []] [] ":=" (Term.app `Bitvec.of_fin_le_of_fin_of_le [`h₀]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Bitvec.of_fin_le_of_fin_of_le [`h₀])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h₀
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Bitvec.of_fin_le_of_fin_of_le
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.intro "intro" [`z `h₀ `h₁])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h₁
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `h₀
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `z
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["[" [(Tactic.simpLemma [] [] `and_imp) "," (Tactic.simpLemma [] [] `Set.mem_Icc)] "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Set.mem_Icc
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `and_imp
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.forall
       "∀"
       [`a]
       [(Term.typeSpec ":" (Term.app `Fin [(«term_^_» (num "2") "^" `n)]))]
       ","
       (Term.arrow
        («term_∈_»
         `a
         "∈"
         (Control.Random.«term_.._» (Term.proj `x "." `toFin) " .. " (Term.proj `y "." `toFin)))
        "→"
        («term_∈_» (Term.app `Bitvec.ofFin [`a]) "∈" (Control.Random.«term_.._» `x " .. " `y))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.arrow
       («term_∈_»
        `a
        "∈"
        (Control.Random.«term_.._» (Term.proj `x "." `toFin) " .. " (Term.proj `y "." `toFin)))
       "→"
       («term_∈_» (Term.app `Bitvec.ofFin [`a]) "∈" (Control.Random.«term_.._» `x " .. " `y)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∈_» (Term.app `Bitvec.ofFin [`a]) "∈" (Control.Random.«term_.._» `x " .. " `y))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Control.Random.«term_.._» `x " .. " `y)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Control.Random.«term_.._»', expected 'Control.Random.term_.._._@.Control.Random._hyg.9'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.letPatDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveEqnsDecl'
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
/-- generate a random bit vector of length `n` -/
  def
    Bitvec.randomR
    { n : ℕ } ( x y : Bitvec n ) ( h : x ≤ y ) : RandG g x .. y
    :=
      have
        h'
          : ∀ a : Fin 2 ^ n , a ∈ x . toFin .. y . toFin → Bitvec.ofFin a ∈ x .. y
          :=
          by
            simp only [ and_imp , Set.mem_Icc ]
              ;
              intro z h₀ h₁
              replace h₀ := Bitvec.of_fin_le_of_fin_of_le h₀
              replace h₁ := Bitvec.of_fin_le_of_fin_of_le h₁
              rw [ Bitvec.of_fin_to_fin ] at h₀ h₁
              ;
              constructor <;> assumption
        Subtype.map Bitvec.ofFin h'
          <$>
          Rand.randomR x . toFin y . toFin Bitvec.to_fin_le_to_fin_of_le h
#align bitvec.random_r Bitvec.randomR

open Nat

instance randomBitvec (n : ℕ) : Random (Bitvec n) where Random _ inst := @Bitvec.random _ inst n
#align random_bitvec randomBitvec

instance boundedRandomBitvec (n : ℕ) : BoundedRandom (Bitvec n)
    where randomR _ inst x y p := @Bitvec.randomR _ inst _ _ _ p
#align bounded_random_bitvec boundedRandomBitvec

