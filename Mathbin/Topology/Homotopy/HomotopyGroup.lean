/-
Copyright (c) 2021 Roberto Alvarez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Roberto Alvarez

! This file was ported from Lean 3 source module topology.homotopy.homotopy_group
! leanprover-community/mathlib commit 6d0adfa76594f304b4650d098273d4366edeb61b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup

/-!
# `n`th homotopy group

We define the `n`th homotopy group at `x`, `π n x`, as the equivalence classes
of functions from the nth dimensional cube to the topological space `X`
that send the boundary to the base point `x`, up to homotopic equivalence.
Note that such functions are generalized loops `gen_loop n x`, in particular
`gen_loop 1 x ≃ path x x`

We show that `π 0 x` is equivalent to the path-conected components, and
that `π 1 x` is equivalent to the fundamental group at `x`.

## definitions

* `gen_loop n x` is the type of continous fuctions `I^n → X` that send the boundary to `x`
* `homotopy_group n x` denoted `π n x` is the quotient of `gen_loop n x` by homotopy relative
  to the boundary

TODO: show that `π n x` is a group when `n > 0` and abelian when `n > 1`. Show that
`pi1_equiv_fundamental_group` is an isomorphism of groups.

-/


open unitInterval TopologicalSpace

noncomputable section

universe u

variable {X : Type u} [TopologicalSpace X]

variable {n : ℕ} {x : X}

/-- The `n`-dimensional cube.
-/
def Cube (n : ℕ) : Type :=
  Fin n → I deriving Zero, One, TopologicalSpace
#align cube Cube

-- mathport name: «exprI^»
local notation "I^" => Cube

namespace Cube

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      []
      [(Term.attributes
        "@["
        [(Term.attrInstance (Term.attrKind []) (Attr.simple `continuity []))]
        "]")]
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `proj_continuous [])
      (Command.declSig
       [(Term.explicitBinder "(" [`i] [":" (Term.app `Fin [`n])] [] ")")]
       (Term.typeSpec
        ":"
        (Term.app
         `Continuous
         [(Term.fun
           "fun"
           (Term.basicFun
            [`f]
            [(Term.typeSpec ":" (Term.app (Topology.Homotopy.HomotopyGroup.«termI^» "I^") [`n]))]
            "=>"
            (Term.app `f [`i])))])))
      (Command.declValSimple ":=" (Term.app `continuous_apply [`i]) [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `continuous_apply [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `continuous_apply
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app
       `Continuous
       [(Term.fun
         "fun"
         (Term.basicFun
          [`f]
          [(Term.typeSpec ":" (Term.app (Topology.Homotopy.HomotopyGroup.«termI^» "I^") [`n]))]
          "=>"
          (Term.app `f [`i])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`f]
        [(Term.typeSpec ":" (Term.app (Topology.Homotopy.HomotopyGroup.«termI^» "I^") [`n]))]
        "=>"
        (Term.app `f [`i])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `f [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Topology.Homotopy.HomotopyGroup.«termI^» "I^") [`n])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Topology.Homotopy.HomotopyGroup.«termI^» "I^")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Topology.Homotopy.HomotopyGroup.«termI^»', expected 'Topology.Homotopy.HomotopyGroup.termI^._@.Topology.Homotopy.HomotopyGroup._hyg.5'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ continuity ]
  theorem proj_continuous ( i : Fin n ) : Continuous fun f : I^ n => f i := continuous_apply i
#align cube.proj_continuous Cube.proj_continuous

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "The points of the `n`-dimensional cube with at least one projection equal to 0 or 1.\n-/")]
      []
      []
      []
      []
      [])
     (Command.def
      "def"
      (Command.declId `boundary [])
      (Command.optDeclSig
       [(Term.explicitBinder "(" [`n] [":" (termℕ "ℕ")] [] ")")]
       [(Term.typeSpec
         ":"
         (Term.app `Set [(Term.app (Topology.Homotopy.HomotopyGroup.«termI^» "I^") [`n])]))])
      (Command.declValSimple
       ":="
       (Set.«term{_|_}»
        "{"
        (Std.ExtendedBinder.extBinder (Lean.binderIdent `y) [])
        "|"
        («term∃_,_»
         "∃"
         (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
         ","
         («term_∨_»
          («term_=_» (Term.app `y [`i]) "=" (num "0"))
          "∨"
          («term_=_» (Term.app `y [`i]) "=" (num "1"))))
        "}")
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Set.«term{_|_}»
       "{"
       (Std.ExtendedBinder.extBinder (Lean.binderIdent `y) [])
       "|"
       («term∃_,_»
        "∃"
        (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
        ","
        («term_∨_»
         («term_=_» (Term.app `y [`i]) "=" (num "0"))
         "∨"
         («term_=_» (Term.app `y [`i]) "=" (num "1"))))
       "}")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term∃_,_»
       "∃"
       (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
       ","
       («term_∨_»
        («term_=_» (Term.app `y [`i]) "=" (num "0"))
        "∨"
        («term_=_» (Term.app `y [`i]) "=" (num "1"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∨_»
       («term_=_» (Term.app `y [`i]) "=" (num "0"))
       "∨"
       («term_=_» (Term.app `y [`i]) "=" (num "1")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_» (Term.app `y [`i]) "=" (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app `y [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 30 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 30, term))
      («term_=_» (Term.app `y [`i]) "=" (num "0"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app `y [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 31 >? 50, (some 51, term) <=? (some 30, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 30, (some 30, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'Lean.bracketedExplicitBinders'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app `Set [(Term.app (Topology.Homotopy.HomotopyGroup.«termI^» "I^") [`n])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Topology.Homotopy.HomotopyGroup.«termI^» "I^") [`n])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Topology.Homotopy.HomotopyGroup.«termI^» "I^")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Topology.Homotopy.HomotopyGroup.«termI^»', expected 'Topology.Homotopy.HomotopyGroup.termI^._@.Topology.Homotopy.HomotopyGroup._hyg.5'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    The points of the `n`-dimensional cube with at least one projection equal to 0 or 1.
    -/
  def boundary ( n : ℕ ) : Set I^ n := { y | ∃ i , y i = 0 ∨ y i = 1 }
#align cube.boundary Cube.boundary

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment "/--" "The first projection of a positive-dimensional cube.\n-/")]
      [(Term.attributes "@[" [(Term.attrInstance (Term.attrKind []) (Attr.simp "simp" [] []))] "]")]
      []
      []
      []
      [])
     (Command.def
      "def"
      (Command.declId `head [])
      (Command.optDeclSig
       [(Term.implicitBinder "{" [`n] [] "}")]
       [(Term.typeSpec
         ":"
         (Term.arrow
          (Term.app (Topology.Homotopy.HomotopyGroup.«termI^» "I^") [(«term_+_» `n "+" (num "1"))])
          "→"
          (unitInterval.Topology.UnitInterval.unit_interval "I")))])
      (Command.declValSimple
       ":="
       (Term.fun "fun" (Term.basicFun [`c] [] "=>" (Term.app `c [(num "0")])))
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun "fun" (Term.basicFun [`c] [] "=>" (Term.app `c [(num "0")])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `c [(num "0")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `c
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `c
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.arrow
       (Term.app (Topology.Homotopy.HomotopyGroup.«termI^» "I^") [(«term_+_» `n "+" (num "1"))])
       "→"
       (unitInterval.Topology.UnitInterval.unit_interval "I"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (unitInterval.Topology.UnitInterval.unit_interval "I")
[PrettyPrinter.parenthesize] ...precedences are 25 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
      (Term.app (Topology.Homotopy.HomotopyGroup.«termI^» "I^") [(«term_+_» `n "+" (num "1"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_+_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_+_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_» `n "+" (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `n
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_+_» `n "+" (num "1")) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Topology.Homotopy.HomotopyGroup.«termI^» "I^")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Topology.Homotopy.HomotopyGroup.«termI^»', expected 'Topology.Homotopy.HomotopyGroup.termI^._@.Topology.Homotopy.HomotopyGroup._hyg.5'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
      The first projection of a positive-dimensional cube.
      -/
    @[ simp ]
  def head { n } : I^ n + 1 → I := fun c => c 0
#align cube.head Cube.head

@[continuity]
theorem head.continuous {n} : Continuous (@head n) :=
  proj_continuous 0
#align cube.head.continuous Cube.head.continuous

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "The projection to the last `n` coordinates from an `n+1` dimensional cube.\n-/")]
      [(Term.attributes "@[" [(Term.attrInstance (Term.attrKind []) (Attr.simp "simp" [] []))] "]")]
      []
      []
      []
      [])
     (Command.def
      "def"
      (Command.declId `tail [])
      (Command.optDeclSig
       [(Term.implicitBinder "{" [`n] [] "}")]
       [(Term.typeSpec
         ":"
         (Term.arrow
          (Term.app (Topology.Homotopy.HomotopyGroup.«termI^» "I^") [(«term_+_» `n "+" (num "1"))])
          "→"
          (Term.app (Topology.Homotopy.HomotopyGroup.«termI^» "I^") [`n])))])
      (Command.declValSimple
       ":="
       (Term.fun "fun" (Term.basicFun [`c] [] "=>" (Term.app `Fin.tail [`c])))
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun "fun" (Term.basicFun [`c] [] "=>" (Term.app `Fin.tail [`c])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Fin.tail [`c])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `c
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Fin.tail
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `c
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.arrow
       (Term.app (Topology.Homotopy.HomotopyGroup.«termI^» "I^") [(«term_+_» `n "+" (num "1"))])
       "→"
       (Term.app (Topology.Homotopy.HomotopyGroup.«termI^» "I^") [`n]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Topology.Homotopy.HomotopyGroup.«termI^» "I^") [`n])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Topology.Homotopy.HomotopyGroup.«termI^» "I^")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Topology.Homotopy.HomotopyGroup.«termI^»', expected 'Topology.Homotopy.HomotopyGroup.termI^._@.Topology.Homotopy.HomotopyGroup._hyg.5'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
      The projection to the last `n` coordinates from an `n+1` dimensional cube.
      -/
    @[ simp ]
  def tail { n } : I^ n + 1 → I^ n := fun c => Fin.tail c
#align cube.tail Cube.tail

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.instance
      (Term.attrKind [])
      "instance"
      []
      [(Command.declId `uniqueCube0 [])]
      (Command.declSig
       []
       (Term.typeSpec
        ":"
        (Term.app
         `Unique
         [(Term.app (Topology.Homotopy.HomotopyGroup.«termI^» "I^") [(num "0")])])))
      (Command.declValSimple ":=" (Term.app `Pi.uniqueOfIsEmpty [(Term.hole "_")]) [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Pi.uniqueOfIsEmpty [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Pi.uniqueOfIsEmpty
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app `Unique [(Term.app (Topology.Homotopy.HomotopyGroup.«termI^» "I^") [(num "0")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Topology.Homotopy.HomotopyGroup.«termI^» "I^") [(num "0")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Topology.Homotopy.HomotopyGroup.«termI^» "I^")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Topology.Homotopy.HomotopyGroup.«termI^»', expected 'Topology.Homotopy.HomotopyGroup.termI^._@.Topology.Homotopy.HomotopyGroup._hyg.5'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
instance uniqueCube0 : Unique I^ 0 := Pi.uniqueOfIsEmpty _
#align cube.unique_cube0 Cube.uniqueCube0

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `one_char [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`f]
         [":" (Term.app (Topology.Homotopy.HomotopyGroup.«termI^» "I^") [(num "1")])]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         `f
         "="
         (Term.fun "fun" (Term.basicFun [(Term.hole "_")] [] "=>" (Term.app `f [(num "0")]))))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(convert "convert" [] (Term.app `eq_const_of_unique [`f]) [])])))
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
         [(convert "convert" [] (Term.app `eq_const_of_unique [`f]) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (convert "convert" [] (Term.app `eq_const_of_unique [`f]) [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `eq_const_of_unique [`f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `eq_const_of_unique
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       `f
       "="
       (Term.fun "fun" (Term.basicFun [(Term.hole "_")] [] "=>" (Term.app `f [(num "0")]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun "fun" (Term.basicFun [(Term.hole "_")] [] "=>" (Term.app `f [(num "0")])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `f [(num "0")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 0, term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Topology.Homotopy.HomotopyGroup.«termI^» "I^") [(num "1")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Topology.Homotopy.HomotopyGroup.«termI^» "I^")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Topology.Homotopy.HomotopyGroup.«termI^»', expected 'Topology.Homotopy.HomotopyGroup.termI^._@.Topology.Homotopy.HomotopyGroup._hyg.5'
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
theorem one_char ( f : I^ 1 ) : f = fun _ => f 0 := by convert eq_const_of_unique f
#align cube.one_char Cube.one_char

end Cube

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "The `n`-dimensional generalized loops; functions `I^n → X` that send the boundary to the base point.\n-/")]
      []
      []
      []
      []
      [])
     (Command.structure
      (Command.structureTk "structure")
      (Command.declId `GenLoop [])
      [(Term.explicitBinder "(" [`n] [":" (termℕ "ℕ")] [] ")")
       (Term.explicitBinder "(" [`x] [":" `X] [] ")")]
      [(Command.extends
        "extends"
        [(Topology.ContinuousFunction.Basic.«termC(_,_)»
          "C("
          (Term.app (Topology.Homotopy.HomotopyGroup.«termI^» "I^") [`n])
          ", "
          `X
          ")")])]
      []
      ["where"
       []
       (Command.structFields
        [(Command.structSimpleBinder
          (Command.declModifiers [] [] [] [] [] [])
          `boundary
          (Command.optDeclSig
           []
           [(Term.typeSpec
             ":"
             (Std.ExtendedBinder.«term∀__,_»
              "∀"
              (Lean.binderIdent `y)
              («binderTerm∈_» "∈" (Term.app `Cube.boundary [`n]))
              ","
              («term_=_» (Term.app `to_fun [`y]) "=" `x)))])
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
      (Std.ExtendedBinder.«term∀__,_»
       "∀"
       (Lean.binderIdent `y)
       («binderTerm∈_» "∈" (Term.app `Cube.boundary [`n]))
       ","
       («term_=_» (Term.app `to_fun [`y]) "=" `x))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_» (Term.app `to_fun [`y]) "=" `x)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app `to_fun [`y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `to_fun
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Cube.boundary [`n])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Cube.boundary
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Topology.ContinuousFunction.Basic.«termC(_,_)»
       "C("
       (Term.app (Topology.Homotopy.HomotopyGroup.«termI^» "I^") [`n])
       ", "
       `X
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `X
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Topology.Homotopy.HomotopyGroup.«termI^» "I^") [`n])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Topology.Homotopy.HomotopyGroup.«termI^» "I^")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Topology.Homotopy.HomotopyGroup.«termI^»', expected 'Topology.Homotopy.HomotopyGroup.termI^._@.Topology.Homotopy.HomotopyGroup._hyg.5'-/-- failed to format: format: uncaught backtrack exception
/--
    The `n`-dimensional generalized loops; functions `I^n → X` that send the boundary to the base point.
    -/
  structure
    GenLoop
    ( n : ℕ ) ( x : X )
    extends C( I^ n , X )
    where boundary : ∀ y ∈ Cube.boundary n , to_fun y = x
#align gen_loop GenLoop

namespace GenLoop

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.instance
      (Term.attrKind [])
      "instance"
      []
      [(Command.declId `funLike [])]
      (Command.declSig
       []
       (Term.typeSpec
        ":"
        (Term.app
         `FunLike
         [(Term.app `GenLoop [`n `x])
          (Term.app (Topology.Homotopy.HomotopyGroup.«termI^» "I^") [`n])
          (Term.fun "fun" (Term.basicFun [(Term.hole "_")] [] "=>" `X))])))
      (Command.whereStructInst
       "where"
       [(Command.whereStructField
         (Term.letDecl (Term.letIdDecl `coe [`f] [] ":=" (Term.proj `f "." (fieldIdx "1")))))
        []
        (Command.whereStructField
         (Term.letDecl
          (Term.letIdDecl
           `coe_injective'
           []
           []
           ":="
           (Term.fun
            "fun"
            (Term.basicFun
             [(Term.anonymousCtor
               "⟨"
               [(Term.anonymousCtor "⟨" [`f "," (Term.hole "_")] "⟩") "," (Term.hole "_")]
               "⟩")
              (Term.anonymousCtor
               "⟨"
               [(Term.anonymousCtor "⟨" [`g "," (Term.hole "_")] "⟩") "," (Term.hole "_")]
               "⟩")
              `h]
             []
             "=>"
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.congr "congr" []) [] (Tactic.exact "exact" `h)]))))))))]
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
      (Term.fun
       "fun"
       (Term.basicFun
        [(Term.anonymousCtor
          "⟨"
          [(Term.anonymousCtor "⟨" [`f "," (Term.hole "_")] "⟩") "," (Term.hole "_")]
          "⟩")
         (Term.anonymousCtor
          "⟨"
          [(Term.anonymousCtor "⟨" [`g "," (Term.hole "_")] "⟩") "," (Term.hole "_")]
          "⟩")
         `h]
        []
        "=>"
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented [(Tactic.congr "congr" []) [] (Tactic.exact "exact" `h)])))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented [(Tactic.congr "congr" []) [] (Tactic.exact "exact" `h)])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" `h)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.congr "congr" [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.anonymousCtor
       "⟨"
       [(Term.anonymousCtor "⟨" [`g "," (Term.hole "_")] "⟩") "," (Term.hole "_")]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [`g "," (Term.hole "_")] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.anonymousCtor
       "⟨"
       [(Term.anonymousCtor "⟨" [`f "," (Term.hole "_")] "⟩") "," (Term.hole "_")]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [`f "," (Term.hole "_")] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `f "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app
       `FunLike
       [(Term.app `GenLoop [`n `x])
        (Term.app (Topology.Homotopy.HomotopyGroup.«termI^» "I^") [`n])
        (Term.fun "fun" (Term.basicFun [(Term.hole "_")] [] "=>" `X))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun "fun" (Term.basicFun [(Term.hole "_")] [] "=>" `X))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `X
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.app (Topology.Homotopy.HomotopyGroup.«termI^» "I^") [`n])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Topology.Homotopy.HomotopyGroup.«termI^» "I^")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Topology.Homotopy.HomotopyGroup.«termI^»', expected 'Topology.Homotopy.HomotopyGroup.termI^._@.Topology.Homotopy.HomotopyGroup._hyg.5'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
instance
  funLike
  : FunLike GenLoop n x I^ n fun _ => X
  where
    coe f := f . 1 coe_injective' := fun ⟨ ⟨ f , _ ⟩ , _ ⟩ ⟨ ⟨ g , _ ⟩ , _ ⟩ h => by congr exact h
#align gen_loop.fun_like GenLoop.funLike

@[ext]
theorem ext (f g : GenLoop n x) (H : ∀ y, f y = g y) : f = g :=
  FunLike.ext f g H
#align gen_loop.ext GenLoop.ext

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
      (Command.declId `mk_apply [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`f]
         [":"
          (Topology.ContinuousFunction.Basic.«termC(_,_)»
           "C("
           (Term.app (Topology.Homotopy.HomotopyGroup.«termI^» "I^") [`n])
           ", "
           `X
           ")")]
         []
         ")")
        (Term.explicitBinder "(" [`H `y] [] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app
          (Term.typeAscription
           "("
           (Term.anonymousCtor "⟨" [`f "," `H] "⟩")
           ":"
           [(Term.app `GenLoop [`n `x])]
           ")")
          [`y])
         "="
         (Term.app `f [`y]))))
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
        (Term.typeAscription
         "("
         (Term.anonymousCtor "⟨" [`f "," `H] "⟩")
         ":"
         [(Term.app `GenLoop [`n `x])]
         ")")
        [`y])
       "="
       (Term.app `f [`y]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `f [`y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app
       (Term.typeAscription
        "("
        (Term.anonymousCtor "⟨" [`f "," `H] "⟩")
        ":"
        [(Term.app `GenLoop [`n `x])]
        ")")
       [`y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.typeAscription
       "("
       (Term.anonymousCtor "⟨" [`f "," `H] "⟩")
       ":"
       [(Term.app `GenLoop [`n `x])]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `GenLoop [`n `x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `GenLoop
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [`f "," `H] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `H
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
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
      (Topology.ContinuousFunction.Basic.«termC(_,_)»
       "C("
       (Term.app (Topology.Homotopy.HomotopyGroup.«termI^» "I^") [`n])
       ", "
       `X
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `X
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Topology.Homotopy.HomotopyGroup.«termI^» "I^") [`n])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Topology.Homotopy.HomotopyGroup.«termI^» "I^")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Topology.Homotopy.HomotopyGroup.«termI^»', expected 'Topology.Homotopy.HomotopyGroup.termI^._@.Topology.Homotopy.HomotopyGroup._hyg.5'
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
  theorem mk_apply ( f : C( I^ n , X ) ) ( H y ) : ( ⟨ f , H ⟩ : GenLoop n x ) y = f y := rfl
#align gen_loop.mk_apply GenLoop.mk_apply

/-- The constant `gen_loop` at `x`.
-/
def const : GenLoop n x :=
  ⟨ContinuousMap.const _ x, fun _ _ => rfl⟩
#align gen_loop.const GenLoop.const

instance inhabited : Inhabited (GenLoop n x) where default := const
#align gen_loop.inhabited GenLoop.inhabited

/-- The "homotopy relative to boundary" relation between `gen_loop`s.
-/
def Homotopic (f g : GenLoop n x) : Prop :=
  f.toContinuousMap.HomotopicRel g.toContinuousMap (Cube.boundary n)
#align gen_loop.homotopic GenLoop.Homotopic

namespace Homotopic

section

variable {f g h : GenLoop n x}

@[refl]
theorem refl (f : GenLoop n x) : Homotopic f f :=
  ContinuousMap.HomotopicRel.refl _
#align gen_loop.homotopic.refl GenLoop.Homotopic.refl

@[symm]
theorem symm (H : f.Homotopic g) : g.Homotopic f :=
  H.symm
#align gen_loop.homotopic.symm GenLoop.Homotopic.symm

@[trans]
theorem trans (H0 : f.Homotopic g) (H1 : g.Homotopic h) : f.Homotopic h :=
  H0.trans H1
#align gen_loop.homotopic.trans GenLoop.Homotopic.trans

theorem equiv : Equivalence (@Homotopic X _ n x) :=
  ⟨Homotopic.refl, fun _ _ => Homotopic.symm, fun _ _ _ => Homotopic.trans⟩
#align gen_loop.homotopic.equiv GenLoop.Homotopic.equiv

instance setoid (n : ℕ) (x : X) : Setoid (GenLoop n x) :=
  ⟨Homotopic, equiv⟩
#align gen_loop.homotopic.setoid GenLoop.Homotopic.setoid

end

end Homotopic

end GenLoop

/-- The `n`th homotopy group at `x` defined as the quotient of `gen_loop n x` by the
`homotopic` relation.
-/
def HomotopyGroup (n : ℕ) (x : X) : Type _ :=
  Quotient (GenLoop.Homotopic.setoid n x)deriving Inhabited
#align homotopy_group HomotopyGroup

-- mathport name: exprπ
local notation "π" => HomotopyGroup

/-- The 0-dimensional generalized loops based at `x` are in 1-1 correspondence with `X`. -/
def genLoopZeroEquiv : GenLoop 0 x ≃ X where
  toFun f := f 0
  invFun x := ⟨ContinuousMap.const _ x, fun _ ⟨f0, _⟩ => f0.elim0⟩
  left_inv f := by
    ext1
    exact congr_arg f (Subsingleton.elim _ _)
  right_inv _ := rfl
#align gen_loop_zero_equiv genLoopZeroEquiv

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "The 0th homotopy \"group\" is equivalent to the path components of `X`, aka the `zeroth_homotopy`.\n-/")]
      []
      []
      []
      []
      [])
     (Command.def
      "def"
      (Command.declId `pi0EquivPathComponents [])
      (Command.optDeclSig
       []
       [(Term.typeSpec
         ":"
         (Logic.Equiv.Defs.«term_≃_»
          (Term.app (Topology.Homotopy.HomotopyGroup.termπ "π") [(num "0") `x])
          " ≃ "
          (Term.app `ZerothHomotopy [`X])))])
      (Command.declValSimple
       ":="
       (Term.app
        `Quotient.congr
        [`genLoopZeroEquiv
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.intros "intros" [])
             ";"
             (Tactic.«tactic_<;>_»
              (Tactic.constructor "constructor")
              "<;>"
              (Std.Tactic.rintro
               "rintro"
               [(Std.Tactic.RCases.rintroPat.one
                 (Std.Tactic.RCases.rcasesPat.tuple
                  "⟨"
                  [(Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `H)])
                    [])]
                  "⟩"))]
               []))
             []
             (Std.Tactic.exacts
              "exacts"
              "["
              [(Term.anonymousCtor
                "⟨"
                [(Term.structInst
                  "{"
                  []
                  [(Term.structInstField
                    (Term.structInstLVal `toFun [])
                    ":="
                    (Term.fun
                     "fun"
                     (Term.basicFun
                      [`t]
                      []
                      "=>"
                      (Term.app `H [(Term.anonymousCtor "⟨" [`t "," `Fin.elim0] "⟩")]))))
                   []
                   (Term.structInstField
                    (Term.structInstLVal `source' [])
                    ":="
                    (Term.app
                     (Term.proj (Term.app `H.apply_zero [(Term.hole "_")]) "." `trans)
                     [(Term.app `congr_arg [`a₁ `matrix.zero_empty.symm])]))
                   []
                   (Term.structInstField
                    (Term.structInstLVal `target' [])
                    ":="
                    (Term.app
                     (Term.proj (Term.app `H.apply_one [(Term.hole "_")]) "." `trans)
                     [(Term.app `congr_arg [`a₂ `matrix.zero_empty.symm])]))]
                  (Term.optEllipsis [])
                  []
                  "}")]
                "⟩")
               ","
               (Term.anonymousCtor
                "⟨"
                [(Term.structInst
                  "{"
                  []
                  [(Term.structInstField
                    (Term.structInstLVal `toFun [])
                    ":="
                    (Term.fun
                     "fun"
                     (Term.basicFun [`t0] [] "=>" (Term.app `H [(Term.proj `t0 "." `fst)]))))
                   []
                   (Term.structInstField
                    (Term.structInstLVal `map_zero_left' [])
                    ":="
                    (Term.fun
                     "fun"
                     (Term.basicFun
                      [(Term.hole "_")]
                      []
                      "=>"
                      (Term.byTactic
                       "by"
                       (Tactic.tacticSeq
                        (Tactic.tacticSeq1Indented [(convert "convert" [] `H.source [])]))))))
                   []
                   (Term.structInstField
                    (Term.structInstLVal `map_one_left' [])
                    ":="
                    (Term.fun
                     "fun"
                     (Term.basicFun
                      [(Term.hole "_")]
                      []
                      "=>"
                      (Term.byTactic
                       "by"
                       (Tactic.tacticSeq
                        (Tactic.tacticSeq1Indented [(convert "convert" [] `H.target [])]))))))
                   []
                   (Term.structInstField
                    (Term.structInstLVal `prop' [])
                    ":="
                    (Term.fun
                     "fun"
                     (Term.basicFun
                      [(Term.hole "_")
                       (Term.hole "_")
                       (Term.anonymousCtor "⟨" [`i "," (Term.hole "_")] "⟩")]
                      []
                      "=>"
                      (Term.proj `i "." `elim0))))]
                  (Term.optEllipsis [])
                  []
                  "}")]
                "⟩")]
              "]")])))])
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Quotient.congr
       [`genLoopZeroEquiv
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Tactic.intros "intros" [])
            ";"
            (Tactic.«tactic_<;>_»
             (Tactic.constructor "constructor")
             "<;>"
             (Std.Tactic.rintro
              "rintro"
              [(Std.Tactic.RCases.rintroPat.one
                (Std.Tactic.RCases.rcasesPat.tuple
                 "⟨"
                 [(Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `H)])
                   [])]
                 "⟩"))]
              []))
            []
            (Std.Tactic.exacts
             "exacts"
             "["
             [(Term.anonymousCtor
               "⟨"
               [(Term.structInst
                 "{"
                 []
                 [(Term.structInstField
                   (Term.structInstLVal `toFun [])
                   ":="
                   (Term.fun
                    "fun"
                    (Term.basicFun
                     [`t]
                     []
                     "=>"
                     (Term.app `H [(Term.anonymousCtor "⟨" [`t "," `Fin.elim0] "⟩")]))))
                  []
                  (Term.structInstField
                   (Term.structInstLVal `source' [])
                   ":="
                   (Term.app
                    (Term.proj (Term.app `H.apply_zero [(Term.hole "_")]) "." `trans)
                    [(Term.app `congr_arg [`a₁ `matrix.zero_empty.symm])]))
                  []
                  (Term.structInstField
                   (Term.structInstLVal `target' [])
                   ":="
                   (Term.app
                    (Term.proj (Term.app `H.apply_one [(Term.hole "_")]) "." `trans)
                    [(Term.app `congr_arg [`a₂ `matrix.zero_empty.symm])]))]
                 (Term.optEllipsis [])
                 []
                 "}")]
               "⟩")
              ","
              (Term.anonymousCtor
               "⟨"
               [(Term.structInst
                 "{"
                 []
                 [(Term.structInstField
                   (Term.structInstLVal `toFun [])
                   ":="
                   (Term.fun
                    "fun"
                    (Term.basicFun [`t0] [] "=>" (Term.app `H [(Term.proj `t0 "." `fst)]))))
                  []
                  (Term.structInstField
                   (Term.structInstLVal `map_zero_left' [])
                   ":="
                   (Term.fun
                    "fun"
                    (Term.basicFun
                     [(Term.hole "_")]
                     []
                     "=>"
                     (Term.byTactic
                      "by"
                      (Tactic.tacticSeq
                       (Tactic.tacticSeq1Indented [(convert "convert" [] `H.source [])]))))))
                  []
                  (Term.structInstField
                   (Term.structInstLVal `map_one_left' [])
                   ":="
                   (Term.fun
                    "fun"
                    (Term.basicFun
                     [(Term.hole "_")]
                     []
                     "=>"
                     (Term.byTactic
                      "by"
                      (Tactic.tacticSeq
                       (Tactic.tacticSeq1Indented [(convert "convert" [] `H.target [])]))))))
                  []
                  (Term.structInstField
                   (Term.structInstLVal `prop' [])
                   ":="
                   (Term.fun
                    "fun"
                    (Term.basicFun
                     [(Term.hole "_")
                      (Term.hole "_")
                      (Term.anonymousCtor "⟨" [`i "," (Term.hole "_")] "⟩")]
                     []
                     "=>"
                     (Term.proj `i "." `elim0))))]
                 (Term.optEllipsis [])
                 []
                 "}")]
               "⟩")]
             "]")])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.intros "intros" [])
          ";"
          (Tactic.«tactic_<;>_»
           (Tactic.constructor "constructor")
           "<;>"
           (Std.Tactic.rintro
            "rintro"
            [(Std.Tactic.RCases.rintroPat.one
              (Std.Tactic.RCases.rcasesPat.tuple
               "⟨"
               [(Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `H)])
                 [])]
               "⟩"))]
            []))
          []
          (Std.Tactic.exacts
           "exacts"
           "["
           [(Term.anonymousCtor
             "⟨"
             [(Term.structInst
               "{"
               []
               [(Term.structInstField
                 (Term.structInstLVal `toFun [])
                 ":="
                 (Term.fun
                  "fun"
                  (Term.basicFun
                   [`t]
                   []
                   "=>"
                   (Term.app `H [(Term.anonymousCtor "⟨" [`t "," `Fin.elim0] "⟩")]))))
                []
                (Term.structInstField
                 (Term.structInstLVal `source' [])
                 ":="
                 (Term.app
                  (Term.proj (Term.app `H.apply_zero [(Term.hole "_")]) "." `trans)
                  [(Term.app `congr_arg [`a₁ `matrix.zero_empty.symm])]))
                []
                (Term.structInstField
                 (Term.structInstLVal `target' [])
                 ":="
                 (Term.app
                  (Term.proj (Term.app `H.apply_one [(Term.hole "_")]) "." `trans)
                  [(Term.app `congr_arg [`a₂ `matrix.zero_empty.symm])]))]
               (Term.optEllipsis [])
               []
               "}")]
             "⟩")
            ","
            (Term.anonymousCtor
             "⟨"
             [(Term.structInst
               "{"
               []
               [(Term.structInstField
                 (Term.structInstLVal `toFun [])
                 ":="
                 (Term.fun
                  "fun"
                  (Term.basicFun [`t0] [] "=>" (Term.app `H [(Term.proj `t0 "." `fst)]))))
                []
                (Term.structInstField
                 (Term.structInstLVal `map_zero_left' [])
                 ":="
                 (Term.fun
                  "fun"
                  (Term.basicFun
                   [(Term.hole "_")]
                   []
                   "=>"
                   (Term.byTactic
                    "by"
                    (Tactic.tacticSeq
                     (Tactic.tacticSeq1Indented [(convert "convert" [] `H.source [])]))))))
                []
                (Term.structInstField
                 (Term.structInstLVal `map_one_left' [])
                 ":="
                 (Term.fun
                  "fun"
                  (Term.basicFun
                   [(Term.hole "_")]
                   []
                   "=>"
                   (Term.byTactic
                    "by"
                    (Tactic.tacticSeq
                     (Tactic.tacticSeq1Indented [(convert "convert" [] `H.target [])]))))))
                []
                (Term.structInstField
                 (Term.structInstLVal `prop' [])
                 ":="
                 (Term.fun
                  "fun"
                  (Term.basicFun
                   [(Term.hole "_")
                    (Term.hole "_")
                    (Term.anonymousCtor "⟨" [`i "," (Term.hole "_")] "⟩")]
                   []
                   "=>"
                   (Term.proj `i "." `elim0))))]
               (Term.optEllipsis [])
               []
               "}")]
             "⟩")]
           "]")])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.exacts
       "exacts"
       "["
       [(Term.anonymousCtor
         "⟨"
         [(Term.structInst
           "{"
           []
           [(Term.structInstField
             (Term.structInstLVal `toFun [])
             ":="
             (Term.fun
              "fun"
              (Term.basicFun
               [`t]
               []
               "=>"
               (Term.app `H [(Term.anonymousCtor "⟨" [`t "," `Fin.elim0] "⟩")]))))
            []
            (Term.structInstField
             (Term.structInstLVal `source' [])
             ":="
             (Term.app
              (Term.proj (Term.app `H.apply_zero [(Term.hole "_")]) "." `trans)
              [(Term.app `congr_arg [`a₁ `matrix.zero_empty.symm])]))
            []
            (Term.structInstField
             (Term.structInstLVal `target' [])
             ":="
             (Term.app
              (Term.proj (Term.app `H.apply_one [(Term.hole "_")]) "." `trans)
              [(Term.app `congr_arg [`a₂ `matrix.zero_empty.symm])]))]
           (Term.optEllipsis [])
           []
           "}")]
         "⟩")
        ","
        (Term.anonymousCtor
         "⟨"
         [(Term.structInst
           "{"
           []
           [(Term.structInstField
             (Term.structInstLVal `toFun [])
             ":="
             (Term.fun
              "fun"
              (Term.basicFun [`t0] [] "=>" (Term.app `H [(Term.proj `t0 "." `fst)]))))
            []
            (Term.structInstField
             (Term.structInstLVal `map_zero_left' [])
             ":="
             (Term.fun
              "fun"
              (Term.basicFun
               [(Term.hole "_")]
               []
               "=>"
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented [(convert "convert" [] `H.source [])]))))))
            []
            (Term.structInstField
             (Term.structInstLVal `map_one_left' [])
             ":="
             (Term.fun
              "fun"
              (Term.basicFun
               [(Term.hole "_")]
               []
               "=>"
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented [(convert "convert" [] `H.target [])]))))))
            []
            (Term.structInstField
             (Term.structInstLVal `prop' [])
             ":="
             (Term.fun
              "fun"
              (Term.basicFun
               [(Term.hole "_")
                (Term.hole "_")
                (Term.anonymousCtor "⟨" [`i "," (Term.hole "_")] "⟩")]
               []
               "=>"
               (Term.proj `i "." `elim0))))]
           (Term.optEllipsis [])
           []
           "}")]
         "⟩")]
       "]")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.structInst
         "{"
         []
         [(Term.structInstField
           (Term.structInstLVal `toFun [])
           ":="
           (Term.fun "fun" (Term.basicFun [`t0] [] "=>" (Term.app `H [(Term.proj `t0 "." `fst)]))))
          []
          (Term.structInstField
           (Term.structInstLVal `map_zero_left' [])
           ":="
           (Term.fun
            "fun"
            (Term.basicFun
             [(Term.hole "_")]
             []
             "=>"
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented [(convert "convert" [] `H.source [])]))))))
          []
          (Term.structInstField
           (Term.structInstLVal `map_one_left' [])
           ":="
           (Term.fun
            "fun"
            (Term.basicFun
             [(Term.hole "_")]
             []
             "=>"
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented [(convert "convert" [] `H.target [])]))))))
          []
          (Term.structInstField
           (Term.structInstLVal `prop' [])
           ":="
           (Term.fun
            "fun"
            (Term.basicFun
             [(Term.hole "_") (Term.hole "_") (Term.anonymousCtor "⟨" [`i "," (Term.hole "_")] "⟩")]
             []
             "=>"
             (Term.proj `i "." `elim0))))]
         (Term.optEllipsis [])
         []
         "}")]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.structInst
       "{"
       []
       [(Term.structInstField
         (Term.structInstLVal `toFun [])
         ":="
         (Term.fun "fun" (Term.basicFun [`t0] [] "=>" (Term.app `H [(Term.proj `t0 "." `fst)]))))
        []
        (Term.structInstField
         (Term.structInstLVal `map_zero_left' [])
         ":="
         (Term.fun
          "fun"
          (Term.basicFun
           [(Term.hole "_")]
           []
           "=>"
           (Term.byTactic
            "by"
            (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(convert "convert" [] `H.source [])]))))))
        []
        (Term.structInstField
         (Term.structInstLVal `map_one_left' [])
         ":="
         (Term.fun
          "fun"
          (Term.basicFun
           [(Term.hole "_")]
           []
           "=>"
           (Term.byTactic
            "by"
            (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(convert "convert" [] `H.target [])]))))))
        []
        (Term.structInstField
         (Term.structInstLVal `prop' [])
         ":="
         (Term.fun
          "fun"
          (Term.basicFun
           [(Term.hole "_") (Term.hole "_") (Term.anonymousCtor "⟨" [`i "," (Term.hole "_")] "⟩")]
           []
           "=>"
           (Term.proj `i "." `elim0))))]
       (Term.optEllipsis [])
       []
       "}")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [(Term.hole "_") (Term.hole "_") (Term.anonymousCtor "⟨" [`i "," (Term.hole "_")] "⟩")]
        []
        "=>"
        (Term.proj `i "." `elim0)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `i "." `elim0)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `i
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [`i "," (Term.hole "_")] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
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
      (Term.fun
       "fun"
       (Term.basicFun
        [(Term.hole "_")]
        []
        "=>"
        (Term.byTactic
         "by"
         (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(convert "convert" [] `H.target [])])))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(convert "convert" [] `H.target [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (convert "convert" [] `H.target [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `H.target
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
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [(Term.hole "_")]
        []
        "=>"
        (Term.byTactic
         "by"
         (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(convert "convert" [] `H.source [])])))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(convert "convert" [] `H.source [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (convert "convert" [] `H.source [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `H.source
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
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun "fun" (Term.basicFun [`t0] [] "=>" (Term.app `H [(Term.proj `t0 "." `fst)])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `H [(Term.proj `t0 "." `fst)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `t0 "." `fst)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `t0
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `H
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `t0
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.structInst
         "{"
         []
         [(Term.structInstField
           (Term.structInstLVal `toFun [])
           ":="
           (Term.fun
            "fun"
            (Term.basicFun
             [`t]
             []
             "=>"
             (Term.app `H [(Term.anonymousCtor "⟨" [`t "," `Fin.elim0] "⟩")]))))
          []
          (Term.structInstField
           (Term.structInstLVal `source' [])
           ":="
           (Term.app
            (Term.proj (Term.app `H.apply_zero [(Term.hole "_")]) "." `trans)
            [(Term.app `congr_arg [`a₁ `matrix.zero_empty.symm])]))
          []
          (Term.structInstField
           (Term.structInstLVal `target' [])
           ":="
           (Term.app
            (Term.proj (Term.app `H.apply_one [(Term.hole "_")]) "." `trans)
            [(Term.app `congr_arg [`a₂ `matrix.zero_empty.symm])]))]
         (Term.optEllipsis [])
         []
         "}")]
       "⟩")
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
           [`t]
           []
           "=>"
           (Term.app `H [(Term.anonymousCtor "⟨" [`t "," `Fin.elim0] "⟩")]))))
        []
        (Term.structInstField
         (Term.structInstLVal `source' [])
         ":="
         (Term.app
          (Term.proj (Term.app `H.apply_zero [(Term.hole "_")]) "." `trans)
          [(Term.app `congr_arg [`a₁ `matrix.zero_empty.symm])]))
        []
        (Term.structInstField
         (Term.structInstLVal `target' [])
         ":="
         (Term.app
          (Term.proj (Term.app `H.apply_one [(Term.hole "_")]) "." `trans)
          [(Term.app `congr_arg [`a₂ `matrix.zero_empty.symm])]))]
       (Term.optEllipsis [])
       []
       "}")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj (Term.app `H.apply_one [(Term.hole "_")]) "." `trans)
       [(Term.app `congr_arg [`a₂ `matrix.zero_empty.symm])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `congr_arg [`a₂ `matrix.zero_empty.symm])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `matrix.zero_empty.symm
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a₂
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `congr_arg
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `congr_arg [`a₂ `matrix.zero_empty.symm])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app `H.apply_one [(Term.hole "_")]) "." `trans)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `H.apply_one [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `H.apply_one
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `H.apply_one [(Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj (Term.app `H.apply_zero [(Term.hole "_")]) "." `trans)
       [(Term.app `congr_arg [`a₁ `matrix.zero_empty.symm])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `congr_arg [`a₁ `matrix.zero_empty.symm])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `matrix.zero_empty.symm
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `congr_arg
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `congr_arg [`a₁ `matrix.zero_empty.symm])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app `H.apply_zero [(Term.hole "_")]) "." `trans)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `H.apply_zero [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `H.apply_zero
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `H.apply_zero [(Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`t]
        []
        "=>"
        (Term.app `H [(Term.anonymousCtor "⟨" [`t "," `Fin.elim0] "⟩")])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `H [(Term.anonymousCtor "⟨" [`t "," `Fin.elim0] "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [`t "," `Fin.elim0] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Fin.elim0
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `t
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `H
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `t
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.«tactic_<;>_»
       (Tactic.constructor "constructor")
       "<;>"
       (Std.Tactic.rintro
        "rintro"
        [(Std.Tactic.RCases.rintroPat.one
          (Std.Tactic.RCases.rcasesPat.tuple
           "⟨"
           [(Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `H)])
             [])]
           "⟩"))]
        []))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.rintro
       "rintro"
       [(Std.Tactic.RCases.rintroPat.one
         (Std.Tactic.RCases.rcasesPat.tuple
          "⟨"
          [(Std.Tactic.RCases.rcasesPatLo
            (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `H)])
            [])]
          "⟩"))]
       [])
[PrettyPrinter.parenthesize] ...precedences are 2 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
      (Tactic.constructor "constructor")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.intros "intros" [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0,
     tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(Tactic.intros "intros" [])
         ";"
         (Tactic.«tactic_<;>_»
          (Tactic.constructor "constructor")
          "<;>"
          (Std.Tactic.rintro
           "rintro"
           [(Std.Tactic.RCases.rintroPat.one
             (Std.Tactic.RCases.rcasesPat.tuple
              "⟨"
              [(Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `H)])
                [])]
              "⟩"))]
           []))
         []
         (Std.Tactic.exacts
          "exacts"
          "["
          [(Term.anonymousCtor
            "⟨"
            [(Term.structInst
              "{"
              []
              [(Term.structInstField
                (Term.structInstLVal `toFun [])
                ":="
                (Term.fun
                 "fun"
                 (Term.basicFun
                  [`t]
                  []
                  "=>"
                  (Term.app `H [(Term.anonymousCtor "⟨" [`t "," `Fin.elim0] "⟩")]))))
               []
               (Term.structInstField
                (Term.structInstLVal `source' [])
                ":="
                (Term.app
                 (Term.proj
                  (Term.paren "(" (Term.app `H.apply_zero [(Term.hole "_")]) ")")
                  "."
                  `trans)
                 [(Term.paren "(" (Term.app `congr_arg [`a₁ `matrix.zero_empty.symm]) ")")]))
               []
               (Term.structInstField
                (Term.structInstLVal `target' [])
                ":="
                (Term.app
                 (Term.proj
                  (Term.paren "(" (Term.app `H.apply_one [(Term.hole "_")]) ")")
                  "."
                  `trans)
                 [(Term.paren "(" (Term.app `congr_arg [`a₂ `matrix.zero_empty.symm]) ")")]))]
              (Term.optEllipsis [])
              []
              "}")]
            "⟩")
           ","
           (Term.anonymousCtor
            "⟨"
            [(Term.structInst
              "{"
              []
              [(Term.structInstField
                (Term.structInstLVal `toFun [])
                ":="
                (Term.fun
                 "fun"
                 (Term.basicFun [`t0] [] "=>" (Term.app `H [(Term.proj `t0 "." `fst)]))))
               []
               (Term.structInstField
                (Term.structInstLVal `map_zero_left' [])
                ":="
                (Term.fun
                 "fun"
                 (Term.basicFun
                  [(Term.hole "_")]
                  []
                  "=>"
                  (Term.byTactic
                   "by"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented [(convert "convert" [] `H.source [])]))))))
               []
               (Term.structInstField
                (Term.structInstLVal `map_one_left' [])
                ":="
                (Term.fun
                 "fun"
                 (Term.basicFun
                  [(Term.hole "_")]
                  []
                  "=>"
                  (Term.byTactic
                   "by"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented [(convert "convert" [] `H.target [])]))))))
               []
               (Term.structInstField
                (Term.structInstLVal `prop' [])
                ":="
                (Term.fun
                 "fun"
                 (Term.basicFun
                  [(Term.hole "_")
                   (Term.hole "_")
                   (Term.anonymousCtor "⟨" [`i "," (Term.hole "_")] "⟩")]
                  []
                  "=>"
                  (Term.proj `i "." `elim0))))]
              (Term.optEllipsis [])
              []
              "}")]
            "⟩")]
          "]")])))
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `genLoopZeroEquiv
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Quotient.congr
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Logic.Equiv.Defs.«term_≃_»
       (Term.app (Topology.Homotopy.HomotopyGroup.termπ "π") [(num "0") `x])
       " ≃ "
       (Term.app `ZerothHomotopy [`X]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `ZerothHomotopy [`X])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `X
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `ZerothHomotopy
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 26 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
      (Term.app (Topology.Homotopy.HomotopyGroup.termπ "π") [(num "0") `x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Topology.Homotopy.HomotopyGroup.termπ "π")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Topology.Homotopy.HomotopyGroup.termπ', expected 'Topology.Homotopy.HomotopyGroup.termπ._@.Topology.Homotopy.HomotopyGroup._hyg.336'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    The 0th homotopy "group" is equivalent to the path components of `X`, aka the `zeroth_homotopy`.
    -/
  def
    pi0EquivPathComponents
    : π 0 x ≃ ZerothHomotopy X
    :=
      Quotient.congr
        genLoopZeroEquiv
          by
            intros
              ;
              constructor <;> rintro ⟨ H ⟩
              exacts
                [
                ⟨
                    {
                      toFun := fun t => H ⟨ t , Fin.elim0 ⟩
                        source' := H.apply_zero _ . trans congr_arg a₁ matrix.zero_empty.symm
                        target' := H.apply_one _ . trans congr_arg a₂ matrix.zero_empty.symm
                      }
                    ⟩
                  ,
                  ⟨
                    {
                      toFun := fun t0 => H t0 . fst
                        map_zero_left' := fun _ => by convert H.source
                        map_one_left' := fun _ => by convert H.target
                        prop' := fun _ _ ⟨ i , _ ⟩ => i . elim0
                      }
                    ⟩
                ]
#align pi0_equiv_path_components pi0EquivPathComponents

/-- The 1-dimensional generalized loops based at `x` are in 1-1 correspondence with
  paths from `x` to itself. -/
@[simps]
def genLoopOneEquivPathSelf : GenLoop 1 x ≃ Path x x
    where
  toFun p :=
    Path.mk
      ⟨fun t => p fun _ => t, by
        continuity
        exact p.1.2⟩
      (p.boundary (fun _ => 0) ⟨0, Or.inl rfl⟩) (p.boundary (fun _ => 1) ⟨1, Or.inr rfl⟩)
  invFun p :=
    { toFun := fun c => p c.head
      boundary :=
        by
        rintro y ⟨i, iH | iH⟩ <;> cases Unique.eq_default i <;> apply (congr_arg p iH).trans
        exacts[p.source, p.target] }
  left_inv p := by
    ext1
    exact congr_arg p y.one_char.symm
  right_inv p := by
    ext
    rfl
#align gen_loop_one_equiv_path_self genLoopOneEquivPathSelf

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "The first homotopy group at `x` is equivalent to the fundamental group,\ni.e. the loops based at `x` up to homotopy.\n-/")]
      []
      []
      []
      []
      [])
     (Command.def
      "def"
      (Command.declId `pi1EquivFundamentalGroup [])
      (Command.optDeclSig
       []
       [(Term.typeSpec
         ":"
         (Logic.Equiv.Defs.«term_≃_»
          (Term.app (Topology.Homotopy.HomotopyGroup.termπ "π") [(num "1") `x])
          " ≃ "
          (Term.app `FundamentalGroup [`X `x])))])
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.refine'
            "refine'"
            (Term.app
             `Equiv.trans
             [(Term.hole "_")
              (Term.proj
               (Term.app `CategoryTheory.Groupoid.isoEquivHom [(Term.hole "_") (Term.hole "_")])
               "."
               `symm)]))
           []
           (Tactic.refine'
            "refine'"
            (Term.app `Quotient.congr [`genLoopOneEquivPathSelf (Term.hole "_")]))
           []
           (Tactic.intros "intros" [])
           ";"
           (Tactic.«tactic_<;>_»
            (Tactic.constructor "constructor")
            "<;>"
            (Std.Tactic.rintro
             "rintro"
             [(Std.Tactic.RCases.rintroPat.one
               (Std.Tactic.RCases.rcasesPat.tuple
                "⟨"
                [(Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `H)])
                  [])]
                "⟩"))]
             []))
           []
           (Std.Tactic.exacts
            "exacts"
            "["
            [(Term.anonymousCtor
              "⟨"
              [(Term.structInst
                "{"
                []
                [(Term.structInstField
                  (Term.structInstLVal `toFun [])
                  ":="
                  (Term.fun
                   "fun"
                   (Term.basicFun
                    [`tx]
                    []
                    "=>"
                    (Term.app
                     `H
                     [(Term.tuple
                       "("
                       [(Term.proj `tx "." `fst)
                        ","
                        [(Term.fun
                          "fun"
                          (Term.basicFun [(Term.hole "_")] [] "=>" (Term.proj `tx "." `snd)))]]
                       ")")]))))
                 []
                 (Term.structInstField
                  (Term.structInstLVal `map_zero_left' [])
                  ":="
                  (Term.fun
                   "fun"
                   (Term.basicFun
                    [(Term.hole "_")]
                    []
                    "=>"
                    (Term.byTactic
                     "by"
                     (Tactic.tacticSeq
                      (Tactic.tacticSeq1Indented
                       [(convert "convert" [] (Term.app `H.apply_zero [(Term.hole "_")]) [])]))))))
                 []
                 (Term.structInstField
                  (Term.structInstLVal `map_one_left' [])
                  ":="
                  (Term.fun
                   "fun"
                   (Term.basicFun
                    [(Term.hole "_")]
                    []
                    "=>"
                    (Term.byTactic
                     "by"
                     (Tactic.tacticSeq
                      (Tactic.tacticSeq1Indented
                       [(convert "convert" [] (Term.app `H.apply_one [(Term.hole "_")]) [])]))))))
                 []
                 (Term.structInstField
                  (Term.structInstLVal `prop' [])
                  ":="
                  (Term.fun
                   "fun"
                   (Term.basicFun
                    [`t `y `iH]
                    []
                    "=>"
                    (Term.app
                     `H.prop'
                     [(Term.hole "_")
                      (Term.hole "_")
                      (Term.anonymousCtor "⟨" [(num "0") "," `iH] "⟩")]))))]
                (Term.optEllipsis [])
                []
                "}")]
              "⟩")
             ","
             (Term.anonymousCtor
              "⟨"
              [(Term.structInst
                "{"
                []
                [(Term.structInstField
                  (Term.structInstLVal `toFun [])
                  ":="
                  (Term.fun
                   "fun"
                   (Term.basicFun
                    [`tx]
                    []
                    "=>"
                    (Term.app
                     `H
                     [(Term.tuple "(" [(Term.proj `tx "." `fst) "," [`tx.snd.head]] ")")]))))
                 []
                 (Term.structInstField
                  (Term.structInstLVal `map_zero_left' [])
                  ":="
                  (Term.fun
                   "fun"
                   (Term.basicFun
                    [`y]
                    []
                    "=>"
                    (Term.byTactic
                     "by"
                     (Tactic.tacticSeq
                      (Tactic.tacticSeq1Indented
                       [(convert "convert" [] (Term.app `H.apply_zero [(Term.hole "_")]) [])
                        []
                        (Tactic.exact "exact" `y.one_char)]))))))
                 []
                 (Term.structInstField
                  (Term.structInstLVal `map_one_left' [])
                  ":="
                  (Term.fun
                   "fun"
                   (Term.basicFun
                    [`y]
                    []
                    "=>"
                    (Term.byTactic
                     "by"
                     (Tactic.tacticSeq
                      (Tactic.tacticSeq1Indented
                       [(convert "convert" [] (Term.app `H.apply_one [(Term.hole "_")]) [])
                        []
                        (Tactic.exact "exact" `y.one_char)]))))))
                 []
                 (Term.structInstField
                  (Term.structInstLVal `prop' [])
                  ":="
                  (Term.fun
                   "fun"
                   (Term.basicFun
                    [`t `y (Term.anonymousCtor "⟨" [`i "," `iH] "⟩")]
                    []
                    "=>"
                    (Term.byTactic
                     "by"
                     (Tactic.tacticSeq
                      (Tactic.tacticSeq1Indented
                       [(Tactic.cases
                         "cases"
                         [(Tactic.casesTarget [] (Term.app `Unique.eq_default [`i]))]
                         []
                         [])
                        ";"
                        (Tactic.constructor "constructor")
                        []
                        (tactic__
                         (cdotTk (patternIgnore (token.«· » "·")))
                         [(convert
                           "convert"
                           []
                           (Term.app `H.eq_fst [(Term.hole "_") (Term.hole "_")])
                           [])
                          []
                          (Std.Tactic.exacts "exacts" "[" [`y.one_char "," `iH] "]")])
                        []
                        (tactic__
                         (cdotTk (patternIgnore (token.«· » "·")))
                         [(convert
                           "convert"
                           []
                           (Term.app `H.eq_snd [(Term.hole "_") (Term.hole "_")])
                           [])
                          []
                          (Std.Tactic.exacts "exacts" "[" [`y.one_char "," `iH] "]")])]))))))]
                (Term.optEllipsis [])
                []
                "}")]
              "⟩")]
            "]")])))
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
         [(Tactic.refine'
           "refine'"
           (Term.app
            `Equiv.trans
            [(Term.hole "_")
             (Term.proj
              (Term.app `CategoryTheory.Groupoid.isoEquivHom [(Term.hole "_") (Term.hole "_")])
              "."
              `symm)]))
          []
          (Tactic.refine'
           "refine'"
           (Term.app `Quotient.congr [`genLoopOneEquivPathSelf (Term.hole "_")]))
          []
          (Tactic.intros "intros" [])
          ";"
          (Tactic.«tactic_<;>_»
           (Tactic.constructor "constructor")
           "<;>"
           (Std.Tactic.rintro
            "rintro"
            [(Std.Tactic.RCases.rintroPat.one
              (Std.Tactic.RCases.rcasesPat.tuple
               "⟨"
               [(Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `H)])
                 [])]
               "⟩"))]
            []))
          []
          (Std.Tactic.exacts
           "exacts"
           "["
           [(Term.anonymousCtor
             "⟨"
             [(Term.structInst
               "{"
               []
               [(Term.structInstField
                 (Term.structInstLVal `toFun [])
                 ":="
                 (Term.fun
                  "fun"
                  (Term.basicFun
                   [`tx]
                   []
                   "=>"
                   (Term.app
                    `H
                    [(Term.tuple
                      "("
                      [(Term.proj `tx "." `fst)
                       ","
                       [(Term.fun
                         "fun"
                         (Term.basicFun [(Term.hole "_")] [] "=>" (Term.proj `tx "." `snd)))]]
                      ")")]))))
                []
                (Term.structInstField
                 (Term.structInstLVal `map_zero_left' [])
                 ":="
                 (Term.fun
                  "fun"
                  (Term.basicFun
                   [(Term.hole "_")]
                   []
                   "=>"
                   (Term.byTactic
                    "by"
                    (Tactic.tacticSeq
                     (Tactic.tacticSeq1Indented
                      [(convert "convert" [] (Term.app `H.apply_zero [(Term.hole "_")]) [])]))))))
                []
                (Term.structInstField
                 (Term.structInstLVal `map_one_left' [])
                 ":="
                 (Term.fun
                  "fun"
                  (Term.basicFun
                   [(Term.hole "_")]
                   []
                   "=>"
                   (Term.byTactic
                    "by"
                    (Tactic.tacticSeq
                     (Tactic.tacticSeq1Indented
                      [(convert "convert" [] (Term.app `H.apply_one [(Term.hole "_")]) [])]))))))
                []
                (Term.structInstField
                 (Term.structInstLVal `prop' [])
                 ":="
                 (Term.fun
                  "fun"
                  (Term.basicFun
                   [`t `y `iH]
                   []
                   "=>"
                   (Term.app
                    `H.prop'
                    [(Term.hole "_")
                     (Term.hole "_")
                     (Term.anonymousCtor "⟨" [(num "0") "," `iH] "⟩")]))))]
               (Term.optEllipsis [])
               []
               "}")]
             "⟩")
            ","
            (Term.anonymousCtor
             "⟨"
             [(Term.structInst
               "{"
               []
               [(Term.structInstField
                 (Term.structInstLVal `toFun [])
                 ":="
                 (Term.fun
                  "fun"
                  (Term.basicFun
                   [`tx]
                   []
                   "=>"
                   (Term.app
                    `H
                    [(Term.tuple "(" [(Term.proj `tx "." `fst) "," [`tx.snd.head]] ")")]))))
                []
                (Term.structInstField
                 (Term.structInstLVal `map_zero_left' [])
                 ":="
                 (Term.fun
                  "fun"
                  (Term.basicFun
                   [`y]
                   []
                   "=>"
                   (Term.byTactic
                    "by"
                    (Tactic.tacticSeq
                     (Tactic.tacticSeq1Indented
                      [(convert "convert" [] (Term.app `H.apply_zero [(Term.hole "_")]) [])
                       []
                       (Tactic.exact "exact" `y.one_char)]))))))
                []
                (Term.structInstField
                 (Term.structInstLVal `map_one_left' [])
                 ":="
                 (Term.fun
                  "fun"
                  (Term.basicFun
                   [`y]
                   []
                   "=>"
                   (Term.byTactic
                    "by"
                    (Tactic.tacticSeq
                     (Tactic.tacticSeq1Indented
                      [(convert "convert" [] (Term.app `H.apply_one [(Term.hole "_")]) [])
                       []
                       (Tactic.exact "exact" `y.one_char)]))))))
                []
                (Term.structInstField
                 (Term.structInstLVal `prop' [])
                 ":="
                 (Term.fun
                  "fun"
                  (Term.basicFun
                   [`t `y (Term.anonymousCtor "⟨" [`i "," `iH] "⟩")]
                   []
                   "=>"
                   (Term.byTactic
                    "by"
                    (Tactic.tacticSeq
                     (Tactic.tacticSeq1Indented
                      [(Tactic.cases
                        "cases"
                        [(Tactic.casesTarget [] (Term.app `Unique.eq_default [`i]))]
                        []
                        [])
                       ";"
                       (Tactic.constructor "constructor")
                       []
                       (tactic__
                        (cdotTk (patternIgnore (token.«· » "·")))
                        [(convert
                          "convert"
                          []
                          (Term.app `H.eq_fst [(Term.hole "_") (Term.hole "_")])
                          [])
                         []
                         (Std.Tactic.exacts "exacts" "[" [`y.one_char "," `iH] "]")])
                       []
                       (tactic__
                        (cdotTk (patternIgnore (token.«· » "·")))
                        [(convert
                          "convert"
                          []
                          (Term.app `H.eq_snd [(Term.hole "_") (Term.hole "_")])
                          [])
                         []
                         (Std.Tactic.exacts "exacts" "[" [`y.one_char "," `iH] "]")])]))))))]
               (Term.optEllipsis [])
               []
               "}")]
             "⟩")]
           "]")])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.exacts
       "exacts"
       "["
       [(Term.anonymousCtor
         "⟨"
         [(Term.structInst
           "{"
           []
           [(Term.structInstField
             (Term.structInstLVal `toFun [])
             ":="
             (Term.fun
              "fun"
              (Term.basicFun
               [`tx]
               []
               "=>"
               (Term.app
                `H
                [(Term.tuple
                  "("
                  [(Term.proj `tx "." `fst)
                   ","
                   [(Term.fun
                     "fun"
                     (Term.basicFun [(Term.hole "_")] [] "=>" (Term.proj `tx "." `snd)))]]
                  ")")]))))
            []
            (Term.structInstField
             (Term.structInstLVal `map_zero_left' [])
             ":="
             (Term.fun
              "fun"
              (Term.basicFun
               [(Term.hole "_")]
               []
               "=>"
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(convert "convert" [] (Term.app `H.apply_zero [(Term.hole "_")]) [])]))))))
            []
            (Term.structInstField
             (Term.structInstLVal `map_one_left' [])
             ":="
             (Term.fun
              "fun"
              (Term.basicFun
               [(Term.hole "_")]
               []
               "=>"
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(convert "convert" [] (Term.app `H.apply_one [(Term.hole "_")]) [])]))))))
            []
            (Term.structInstField
             (Term.structInstLVal `prop' [])
             ":="
             (Term.fun
              "fun"
              (Term.basicFun
               [`t `y `iH]
               []
               "=>"
               (Term.app
                `H.prop'
                [(Term.hole "_")
                 (Term.hole "_")
                 (Term.anonymousCtor "⟨" [(num "0") "," `iH] "⟩")]))))]
           (Term.optEllipsis [])
           []
           "}")]
         "⟩")
        ","
        (Term.anonymousCtor
         "⟨"
         [(Term.structInst
           "{"
           []
           [(Term.structInstField
             (Term.structInstLVal `toFun [])
             ":="
             (Term.fun
              "fun"
              (Term.basicFun
               [`tx]
               []
               "=>"
               (Term.app `H [(Term.tuple "(" [(Term.proj `tx "." `fst) "," [`tx.snd.head]] ")")]))))
            []
            (Term.structInstField
             (Term.structInstLVal `map_zero_left' [])
             ":="
             (Term.fun
              "fun"
              (Term.basicFun
               [`y]
               []
               "=>"
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(convert "convert" [] (Term.app `H.apply_zero [(Term.hole "_")]) [])
                   []
                   (Tactic.exact "exact" `y.one_char)]))))))
            []
            (Term.structInstField
             (Term.structInstLVal `map_one_left' [])
             ":="
             (Term.fun
              "fun"
              (Term.basicFun
               [`y]
               []
               "=>"
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(convert "convert" [] (Term.app `H.apply_one [(Term.hole "_")]) [])
                   []
                   (Tactic.exact "exact" `y.one_char)]))))))
            []
            (Term.structInstField
             (Term.structInstLVal `prop' [])
             ":="
             (Term.fun
              "fun"
              (Term.basicFun
               [`t `y (Term.anonymousCtor "⟨" [`i "," `iH] "⟩")]
               []
               "=>"
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(Tactic.cases
                    "cases"
                    [(Tactic.casesTarget [] (Term.app `Unique.eq_default [`i]))]
                    []
                    [])
                   ";"
                   (Tactic.constructor "constructor")
                   []
                   (tactic__
                    (cdotTk (patternIgnore (token.«· » "·")))
                    [(convert
                      "convert"
                      []
                      (Term.app `H.eq_fst [(Term.hole "_") (Term.hole "_")])
                      [])
                     []
                     (Std.Tactic.exacts "exacts" "[" [`y.one_char "," `iH] "]")])
                   []
                   (tactic__
                    (cdotTk (patternIgnore (token.«· » "·")))
                    [(convert
                      "convert"
                      []
                      (Term.app `H.eq_snd [(Term.hole "_") (Term.hole "_")])
                      [])
                     []
                     (Std.Tactic.exacts "exacts" "[" [`y.one_char "," `iH] "]")])]))))))]
           (Term.optEllipsis [])
           []
           "}")]
         "⟩")]
       "]")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.structInst
         "{"
         []
         [(Term.structInstField
           (Term.structInstLVal `toFun [])
           ":="
           (Term.fun
            "fun"
            (Term.basicFun
             [`tx]
             []
             "=>"
             (Term.app `H [(Term.tuple "(" [(Term.proj `tx "." `fst) "," [`tx.snd.head]] ")")]))))
          []
          (Term.structInstField
           (Term.structInstLVal `map_zero_left' [])
           ":="
           (Term.fun
            "fun"
            (Term.basicFun
             [`y]
             []
             "=>"
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(convert "convert" [] (Term.app `H.apply_zero [(Term.hole "_")]) [])
                 []
                 (Tactic.exact "exact" `y.one_char)]))))))
          []
          (Term.structInstField
           (Term.structInstLVal `map_one_left' [])
           ":="
           (Term.fun
            "fun"
            (Term.basicFun
             [`y]
             []
             "=>"
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(convert "convert" [] (Term.app `H.apply_one [(Term.hole "_")]) [])
                 []
                 (Tactic.exact "exact" `y.one_char)]))))))
          []
          (Term.structInstField
           (Term.structInstLVal `prop' [])
           ":="
           (Term.fun
            "fun"
            (Term.basicFun
             [`t `y (Term.anonymousCtor "⟨" [`i "," `iH] "⟩")]
             []
             "=>"
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.cases
                  "cases"
                  [(Tactic.casesTarget [] (Term.app `Unique.eq_default [`i]))]
                  []
                  [])
                 ";"
                 (Tactic.constructor "constructor")
                 []
                 (tactic__
                  (cdotTk (patternIgnore (token.«· » "·")))
                  [(convert "convert" [] (Term.app `H.eq_fst [(Term.hole "_") (Term.hole "_")]) [])
                   []
                   (Std.Tactic.exacts "exacts" "[" [`y.one_char "," `iH] "]")])
                 []
                 (tactic__
                  (cdotTk (patternIgnore (token.«· » "·")))
                  [(convert "convert" [] (Term.app `H.eq_snd [(Term.hole "_") (Term.hole "_")]) [])
                   []
                   (Std.Tactic.exacts "exacts" "[" [`y.one_char "," `iH] "]")])]))))))]
         (Term.optEllipsis [])
         []
         "}")]
       "⟩")
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
           [`tx]
           []
           "=>"
           (Term.app `H [(Term.tuple "(" [(Term.proj `tx "." `fst) "," [`tx.snd.head]] ")")]))))
        []
        (Term.structInstField
         (Term.structInstLVal `map_zero_left' [])
         ":="
         (Term.fun
          "fun"
          (Term.basicFun
           [`y]
           []
           "=>"
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(convert "convert" [] (Term.app `H.apply_zero [(Term.hole "_")]) [])
               []
               (Tactic.exact "exact" `y.one_char)]))))))
        []
        (Term.structInstField
         (Term.structInstLVal `map_one_left' [])
         ":="
         (Term.fun
          "fun"
          (Term.basicFun
           [`y]
           []
           "=>"
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(convert "convert" [] (Term.app `H.apply_one [(Term.hole "_")]) [])
               []
               (Tactic.exact "exact" `y.one_char)]))))))
        []
        (Term.structInstField
         (Term.structInstLVal `prop' [])
         ":="
         (Term.fun
          "fun"
          (Term.basicFun
           [`t `y (Term.anonymousCtor "⟨" [`i "," `iH] "⟩")]
           []
           "=>"
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.cases
                "cases"
                [(Tactic.casesTarget [] (Term.app `Unique.eq_default [`i]))]
                []
                [])
               ";"
               (Tactic.constructor "constructor")
               []
               (tactic__
                (cdotTk (patternIgnore (token.«· » "·")))
                [(convert "convert" [] (Term.app `H.eq_fst [(Term.hole "_") (Term.hole "_")]) [])
                 []
                 (Std.Tactic.exacts "exacts" "[" [`y.one_char "," `iH] "]")])
               []
               (tactic__
                (cdotTk (patternIgnore (token.«· » "·")))
                [(convert "convert" [] (Term.app `H.eq_snd [(Term.hole "_") (Term.hole "_")]) [])
                 []
                 (Std.Tactic.exacts "exacts" "[" [`y.one_char "," `iH] "]")])]))))))]
       (Term.optEllipsis [])
       []
       "}")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`t `y (Term.anonymousCtor "⟨" [`i "," `iH] "⟩")]
        []
        "=>"
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Tactic.cases
             "cases"
             [(Tactic.casesTarget [] (Term.app `Unique.eq_default [`i]))]
             []
             [])
            ";"
            (Tactic.constructor "constructor")
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(convert "convert" [] (Term.app `H.eq_fst [(Term.hole "_") (Term.hole "_")]) [])
              []
              (Std.Tactic.exacts "exacts" "[" [`y.one_char "," `iH] "]")])
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(convert "convert" [] (Term.app `H.eq_snd [(Term.hole "_") (Term.hole "_")]) [])
              []
              (Std.Tactic.exacts "exacts" "[" [`y.one_char "," `iH] "]")])])))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.cases "cases" [(Tactic.casesTarget [] (Term.app `Unique.eq_default [`i]))] [] [])
          ";"
          (Tactic.constructor "constructor")
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(convert "convert" [] (Term.app `H.eq_fst [(Term.hole "_") (Term.hole "_")]) [])
            []
            (Std.Tactic.exacts "exacts" "[" [`y.one_char "," `iH] "]")])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(convert "convert" [] (Term.app `H.eq_snd [(Term.hole "_") (Term.hole "_")]) [])
            []
            (Std.Tactic.exacts "exacts" "[" [`y.one_char "," `iH] "]")])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(convert "convert" [] (Term.app `H.eq_snd [(Term.hole "_") (Term.hole "_")]) [])
        []
        (Std.Tactic.exacts "exacts" "[" [`y.one_char "," `iH] "]")])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.exacts "exacts" "[" [`y.one_char "," `iH] "]")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `iH
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y.one_char
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (convert "convert" [] (Term.app `H.eq_snd [(Term.hole "_") (Term.hole "_")]) [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `H.eq_snd [(Term.hole "_") (Term.hole "_")])
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
      `H.eq_snd
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(convert "convert" [] (Term.app `H.eq_fst [(Term.hole "_") (Term.hole "_")]) [])
        []
        (Std.Tactic.exacts "exacts" "[" [`y.one_char "," `iH] "]")])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.exacts "exacts" "[" [`y.one_char "," `iH] "]")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `iH
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y.one_char
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (convert "convert" [] (Term.app `H.eq_fst [(Term.hole "_") (Term.hole "_")]) [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `H.eq_fst [(Term.hole "_") (Term.hole "_")])
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
      `H.eq_fst
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.constructor "constructor")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.cases "cases" [(Tactic.casesTarget [] (Term.app `Unique.eq_default [`i]))] [] [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Unique.eq_default [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Unique.eq_default
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [`i "," `iH] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `iH
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `t
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`y]
        []
        "=>"
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(convert "convert" [] (Term.app `H.apply_one [(Term.hole "_")]) [])
            []
            (Tactic.exact "exact" `y.one_char)])))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(convert "convert" [] (Term.app `H.apply_one [(Term.hole "_")]) [])
          []
          (Tactic.exact "exact" `y.one_char)])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" `y.one_char)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y.one_char
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (convert "convert" [] (Term.app `H.apply_one [(Term.hole "_")]) [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `H.apply_one [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `H.apply_one
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`y]
        []
        "=>"
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(convert "convert" [] (Term.app `H.apply_zero [(Term.hole "_")]) [])
            []
            (Tactic.exact "exact" `y.one_char)])))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(convert "convert" [] (Term.app `H.apply_zero [(Term.hole "_")]) [])
          []
          (Tactic.exact "exact" `y.one_char)])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" `y.one_char)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y.one_char
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (convert "convert" [] (Term.app `H.apply_zero [(Term.hole "_")]) [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `H.apply_zero [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `H.apply_zero
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`tx]
        []
        "=>"
        (Term.app `H [(Term.tuple "(" [(Term.proj `tx "." `fst) "," [`tx.snd.head]] ")")])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `H [(Term.tuple "(" [(Term.proj `tx "." `fst) "," [`tx.snd.head]] ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.tuple', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.tuple', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.tuple "(" [(Term.proj `tx "." `fst) "," [`tx.snd.head]] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `tx.snd.head
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `tx "." `fst)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `tx
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `H
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `tx
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.structInst
         "{"
         []
         [(Term.structInstField
           (Term.structInstLVal `toFun [])
           ":="
           (Term.fun
            "fun"
            (Term.basicFun
             [`tx]
             []
             "=>"
             (Term.app
              `H
              [(Term.tuple
                "("
                [(Term.proj `tx "." `fst)
                 ","
                 [(Term.fun
                   "fun"
                   (Term.basicFun [(Term.hole "_")] [] "=>" (Term.proj `tx "." `snd)))]]
                ")")]))))
          []
          (Term.structInstField
           (Term.structInstLVal `map_zero_left' [])
           ":="
           (Term.fun
            "fun"
            (Term.basicFun
             [(Term.hole "_")]
             []
             "=>"
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(convert "convert" [] (Term.app `H.apply_zero [(Term.hole "_")]) [])]))))))
          []
          (Term.structInstField
           (Term.structInstLVal `map_one_left' [])
           ":="
           (Term.fun
            "fun"
            (Term.basicFun
             [(Term.hole "_")]
             []
             "=>"
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(convert "convert" [] (Term.app `H.apply_one [(Term.hole "_")]) [])]))))))
          []
          (Term.structInstField
           (Term.structInstLVal `prop' [])
           ":="
           (Term.fun
            "fun"
            (Term.basicFun
             [`t `y `iH]
             []
             "=>"
             (Term.app
              `H.prop'
              [(Term.hole "_")
               (Term.hole "_")
               (Term.anonymousCtor "⟨" [(num "0") "," `iH] "⟩")]))))]
         (Term.optEllipsis [])
         []
         "}")]
       "⟩")
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
           [`tx]
           []
           "=>"
           (Term.app
            `H
            [(Term.tuple
              "("
              [(Term.proj `tx "." `fst)
               ","
               [(Term.fun
                 "fun"
                 (Term.basicFun [(Term.hole "_")] [] "=>" (Term.proj `tx "." `snd)))]]
              ")")]))))
        []
        (Term.structInstField
         (Term.structInstLVal `map_zero_left' [])
         ":="
         (Term.fun
          "fun"
          (Term.basicFun
           [(Term.hole "_")]
           []
           "=>"
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(convert "convert" [] (Term.app `H.apply_zero [(Term.hole "_")]) [])]))))))
        []
        (Term.structInstField
         (Term.structInstLVal `map_one_left' [])
         ":="
         (Term.fun
          "fun"
          (Term.basicFun
           [(Term.hole "_")]
           []
           "=>"
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(convert "convert" [] (Term.app `H.apply_one [(Term.hole "_")]) [])]))))))
        []
        (Term.structInstField
         (Term.structInstLVal `prop' [])
         ":="
         (Term.fun
          "fun"
          (Term.basicFun
           [`t `y `iH]
           []
           "=>"
           (Term.app
            `H.prop'
            [(Term.hole "_") (Term.hole "_") (Term.anonymousCtor "⟨" [(num "0") "," `iH] "⟩")]))))]
       (Term.optEllipsis [])
       []
       "}")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`t `y `iH]
        []
        "=>"
        (Term.app
         `H.prop'
         [(Term.hole "_") (Term.hole "_") (Term.anonymousCtor "⟨" [(num "0") "," `iH] "⟩")])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `H.prop'
       [(Term.hole "_") (Term.hole "_") (Term.anonymousCtor "⟨" [(num "0") "," `iH] "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [(num "0") "," `iH] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `iH
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
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
      `H.prop'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `iH
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `t
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [(Term.hole "_")]
        []
        "=>"
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(convert "convert" [] (Term.app `H.apply_one [(Term.hole "_")]) [])])))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(convert "convert" [] (Term.app `H.apply_one [(Term.hole "_")]) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (convert "convert" [] (Term.app `H.apply_one [(Term.hole "_")]) [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `H.apply_one [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `H.apply_one
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [(Term.hole "_")]
        []
        "=>"
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(convert "convert" [] (Term.app `H.apply_zero [(Term.hole "_")]) [])])))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(convert "convert" [] (Term.app `H.apply_zero [(Term.hole "_")]) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (convert "convert" [] (Term.app `H.apply_zero [(Term.hole "_")]) [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `H.apply_zero [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `H.apply_zero
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`tx]
        []
        "=>"
        (Term.app
         `H
         [(Term.tuple
           "("
           [(Term.proj `tx "." `fst)
            ","
            [(Term.fun "fun" (Term.basicFun [(Term.hole "_")] [] "=>" (Term.proj `tx "." `snd)))]]
           ")")])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `H
       [(Term.tuple
         "("
         [(Term.proj `tx "." `fst)
          ","
          [(Term.fun "fun" (Term.basicFun [(Term.hole "_")] [] "=>" (Term.proj `tx "." `snd)))]]
         ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.tuple', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.tuple', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.tuple
       "("
       [(Term.proj `tx "." `fst)
        ","
        [(Term.fun "fun" (Term.basicFun [(Term.hole "_")] [] "=>" (Term.proj `tx "." `snd)))]]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun "fun" (Term.basicFun [(Term.hole "_")] [] "=>" (Term.proj `tx "." `snd)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `tx "." `snd)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `tx
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `tx "." `fst)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `tx
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `H
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `tx
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.«tactic_<;>_»
       (Tactic.constructor "constructor")
       "<;>"
       (Std.Tactic.rintro
        "rintro"
        [(Std.Tactic.RCases.rintroPat.one
          (Std.Tactic.RCases.rcasesPat.tuple
           "⟨"
           [(Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `H)])
             [])]
           "⟩"))]
        []))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.rintro
       "rintro"
       [(Std.Tactic.RCases.rintroPat.one
         (Std.Tactic.RCases.rcasesPat.tuple
          "⟨"
          [(Std.Tactic.RCases.rcasesPatLo
            (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `H)])
            [])]
          "⟩"))]
       [])
[PrettyPrinter.parenthesize] ...precedences are 2 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
      (Tactic.constructor "constructor")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.intros "intros" [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine'
       "refine'"
       (Term.app `Quotient.congr [`genLoopOneEquivPathSelf (Term.hole "_")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Quotient.congr [`genLoopOneEquivPathSelf (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      `genLoopOneEquivPathSelf
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Quotient.congr
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine'
       "refine'"
       (Term.app
        `Equiv.trans
        [(Term.hole "_")
         (Term.proj
          (Term.app `CategoryTheory.Groupoid.isoEquivHom [(Term.hole "_") (Term.hole "_")])
          "."
          `symm)]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Equiv.trans
       [(Term.hole "_")
        (Term.proj
         (Term.app `CategoryTheory.Groupoid.isoEquivHom [(Term.hole "_") (Term.hole "_")])
         "."
         `symm)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj
       (Term.app `CategoryTheory.Groupoid.isoEquivHom [(Term.hole "_") (Term.hole "_")])
       "."
       `symm)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `CategoryTheory.Groupoid.isoEquivHom [(Term.hole "_") (Term.hole "_")])
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
      `CategoryTheory.Groupoid.isoEquivHom
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `CategoryTheory.Groupoid.isoEquivHom [(Term.hole "_") (Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Equiv.trans
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Logic.Equiv.Defs.«term_≃_»
       (Term.app (Topology.Homotopy.HomotopyGroup.termπ "π") [(num "1") `x])
       " ≃ "
       (Term.app `FundamentalGroup [`X `x]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `FundamentalGroup [`X `x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `X
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `FundamentalGroup
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 26 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
      (Term.app (Topology.Homotopy.HomotopyGroup.termπ "π") [(num "1") `x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Topology.Homotopy.HomotopyGroup.termπ "π")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Topology.Homotopy.HomotopyGroup.termπ', expected 'Topology.Homotopy.HomotopyGroup.termπ._@.Topology.Homotopy.HomotopyGroup._hyg.336'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    The first homotopy group at `x` is equivalent to the fundamental group,
    i.e. the loops based at `x` up to homotopy.
    -/
  def
    pi1EquivFundamentalGroup
    : π 1 x ≃ FundamentalGroup X x
    :=
      by
        refine' Equiv.trans _ CategoryTheory.Groupoid.isoEquivHom _ _ . symm
          refine' Quotient.congr genLoopOneEquivPathSelf _
          intros
          ;
          constructor <;> rintro ⟨ H ⟩
          exacts
            [
            ⟨
                {
                  toFun := fun tx => H ( tx . fst , fun _ => tx . snd )
                    map_zero_left' := fun _ => by convert H.apply_zero _
                    map_one_left' := fun _ => by convert H.apply_one _
                    prop' := fun t y iH => H.prop' _ _ ⟨ 0 , iH ⟩
                  }
                ⟩
              ,
              ⟨
                {
                  toFun := fun tx => H ( tx . fst , tx.snd.head )
                    map_zero_left' := fun y => by convert H.apply_zero _ exact y.one_char
                    map_one_left' := fun y => by convert H.apply_one _ exact y.one_char
                    prop'
                      :=
                      fun
                        t y ⟨ i , iH ⟩
                          =>
                          by
                            cases Unique.eq_default i
                              ;
                              constructor
                              · convert H.eq_fst _ _ exacts [ y.one_char , iH ]
                              · convert H.eq_snd _ _ exacts [ y.one_char , iH ]
                  }
                ⟩
            ]
#align pi1_equiv_fundamental_group pi1EquivFundamentalGroup

