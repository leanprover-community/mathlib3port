/-
Copyright (c) 2019 Seul Baek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seul Baek

! This file was ported from Lean 3 source module tactic.omega.find_ees
! leanprover-community/mathlib commit 18a5306c091183ac90884daa9373fa3b178e8607
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Tactic.Omega.EqElim

/-
A tactic for finding a sequence of equality
elimination rules for a given set of constraints.
-/
variable {α β : Type}

open Tactic

namespace Omega

/-- The state of equality elimination proof search. `eqs` is the list of
    equality constraints, and each `t ∈ eqs` represents the constraint `0 = t`.
    Similarly, `les` is the list of inequality constraints, and each `t ∈ eqs`
    represents the constraint `0 < t`. `ees` is the sequence of equality
    elimination steps that have been used so far to obtain the current set of
    constraints. The list `ees` grows over time until `eqs` becomes empty. -/
structure EeState where
  eqs : List Term
  les : List Term
  ees : List Ee
  deriving Inhabited
#align omega.ee_state Omega.EeState

@[reducible]
unsafe def eqelim :=
  StateT EeState tactic
#align omega.eqelim omega.eqelim

unsafe def abort {α : Type} : eqelim α :=
  ⟨fun x => failed⟩
#align omega.abort omega.abort

private unsafe def mk_eqelim_state (eqs les : List Term) : tactic EeState :=
  return (EeState.mk eqs les [])
#align omega.mk_eqelim_state omega.mk_eqelim_state

/-- Get the current list of equality constraints. -/
unsafe def get_eqs : eqelim (List Term) :=
  ee_state.eqs <$> get
#align omega.get_eqs omega.get_eqs

/-- Get the current list of inequality constraints. -/
unsafe def get_les : eqelim (List Term) :=
  ee_state.les <$> get
#align omega.get_les omega.get_les

/-- Get the current sequence of equality elimiation steps. -/
unsafe def get_ees : eqelim (List Ee) :=
  ee_state.ees <$> get
#align omega.get_ees omega.get_ees

/-- Update the list of equality constraints. -/
unsafe def set_eqs (eqs : List Term) : eqelim Unit :=
  modify fun s => { s with eqs }
#align omega.set_eqs omega.set_eqs

/-- Update the list of inequality constraints. -/
unsafe def set_les (les : List Term) : eqelim Unit :=
  modify fun s => { s with les }
#align omega.set_les omega.set_les

/-- Update the sequence of equality elimiation steps. -/
unsafe def set_ees (es : List Ee) : eqelim Unit :=
  modify fun s => { s with ees := es }
#align omega.set_ees omega.set_ees

/-- Add a new step to the sequence of equality elimination steps. -/
unsafe def add_ee (e : Ee) : eqelim Unit := do
  let es ← get_ees
  set_ees (es ++ [e])
#align omega.add_ee omega.add_ee

/-- Return the first equality constraint in the current list of
    equality constraints. The returned constraint is 'popped' and
    no longer available in the state. -/
unsafe def head_eq : eqelim Term := do
  let eqs ← get_eqs
  match eqs with
    | [] => abort
    | Eq :: eqs' => set_eqs eqs' >> pure Eq
#align omega.head_eq omega.head_eq

unsafe def run {α : Type} (eqs les : List Term) (r : eqelim α) : tactic α :=
  Prod.fst <$> (mk_eqelim_state eqs les >>= r.run)
#align omega.run omega.run

/-- If `t1` succeeds and returns a value, 'commit' to that choice and
    run `t3` with the returned value as argument. Do not backtrack
    to try `t2` even if `t3` fails. If `t1` fails outright, run `t2`. -/
unsafe def ee_commit (t1 : eqelim α) (t2 : eqelim β) (t3 : α → eqelim β) : eqelim β := do
  let x ← t1 >>= return ∘ some <|> return none
  match x with
    | none => t2
    | some a => t3 a
#align omega.ee_commit omega.ee_commit

-- mathport name: «expr !>>= ; »
local notation t1 " !>>= " t2 "; " t3 => ee_commit t1 t2 t3

private unsafe def of_tactic {α : Type} : tactic α → eqelim α :=
  StateT.lift
#align omega.of_tactic omega.of_tactic

/-- GCD of all elements of the list. -/
def gcd : List Int → Nat
  | [] => 0
  | i :: is => Nat.gcd i.natAbs (gcd is)
#align omega.gcd Omega.gcd

/-- GCD of all coefficients in a term. -/
unsafe def get_gcd (t : Term) : eqelim Int :=
  pure ↑(gcd t.snd)
#align omega.get_gcd omega.get_gcd

/-- Divide a term by an integer if the integer divides
    the constant component of the term. It is assumed that
    the integer also divides all coefficients of the term. -/
unsafe def factor (i : Int) (t : Term) : eqelim Term :=
  if i ∣ t.fst then add_ee (Ee.factor i) >> pure (t.div i) else abort
#align omega.factor omega.factor

/-- If list has a nonzero element, return the minimum element
(by absolute value) with its index. Otherwise, return none. -/
unsafe def find_min_coeff_core : List Int → eqelim (Int × Nat)
  | [] => abort
  | i :: is =>
    (do
        let (j, n) ← find_min_coeff_core is
        if i ≠ 0 ∧ i ≤ j then pure (i, 0) else pure (j, n + 1)) <|>
      if i = (0 : Int) then abort else pure (i, 0)
#align omega.find_min_coeff_core omega.find_min_coeff_core

/-- Find and return the smallest coefficient (by absolute value) in a term,
    along with the coefficient's variable index and the term itself.
    If the coefficient is negative, negate both the coefficient and the term
    before returning them. -/
unsafe def find_min_coeff (t : Term) : eqelim (Int × Nat × term) := do
  let (i, n) ← find_min_coeff_core t.snd
  if 0 < i then pure (i, n, t) else add_ee ee.neg >> pure (-i, n, t)
#align omega.find_min_coeff omega.find_min_coeff

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "Find an appropriate equality elimination step for the\n    current state and apply it. -/")]
      []
      []
      []
      [(Command.unsafe "unsafe")]
      [])
     (Command.def
      "def"
      (Command.declId `elim_eq [])
      (Command.optDeclSig [] [(Term.typeSpec ":" (Term.app `eqelim [`Unit]))])
      (Command.declValSimple
       ":="
       (Term.do
        "do"
        (Term.doSeqIndent
         [(Term.doSeqItem
           (Term.doLetArrow "let" [] (Term.doIdDecl `t [] "←" (Term.doExpr `head_eq)))
           [])
          (Term.doSeqItem
           (Term.doLetArrow
            "let"
            []
            (Term.doIdDecl `i [] "←" (Term.doExpr (Term.app `get_gcd [`t]))))
           [])
          (Term.doSeqItem
           (Term.doExpr
            (Omega.Tactic.Omega.FindEes.«term_!>>=_;_»
             (Term.app `factor [`i `t])
             " !>>= "
             («term_>>_»
              (Term.app `set_eqs [(«term[_]» "[" [] "]")])
              ">>"
              (Term.app `add_ee [(Term.app `ee.nondiv [`i])]))
             "; "
             (Term.fun
              "fun"
              (Term.basicFun
               [`s]
               []
               "=>"
               (Omega.Tactic.Omega.FindEes.«term_!>>=_;_»
                (Term.app `find_min_coeff [`s])
                " !>>= "
                (Term.app `add_ee [`ee.drop])
                "; "
                (Term.fun
                 "fun"
                 (Term.basicFun
                  [(Term.anonymousCtor "⟨" [`i "," `n "," `u] "⟩")]
                  []
                  "=>"
                  (termIfThenElse
                   "if"
                   («term_=_» `i "=" (num "1"))
                   "then"
                   (Term.do
                    "do"
                    (Term.doSeqIndent
                     [(Term.doSeqItem
                       (Term.doLetArrow "let" [] (Term.doIdDecl `eqs [] "←" (Term.doExpr `get_eqs)))
                       [])
                      (Term.doSeqItem
                       (Term.doLetArrow "let" [] (Term.doIdDecl `les [] "←" (Term.doExpr `get_les)))
                       [])
                      (Term.doSeqItem
                       (Term.doExpr
                        (Term.app `set_eqs [(Term.app `eqs [(Term.app `cancel [`n `u])])]))
                       [])
                      (Term.doSeqItem
                       (Term.doExpr
                        (Term.app `set_les [(Term.app `les [(Term.app `cancel [`n `u])])]))
                       [])
                      (Term.doSeqItem
                       (Term.doExpr (Term.app `add_ee [(Term.app `ee.cancel [`n])]))
                       [])]))
                   "else"
                   (Term.let
                    "let"
                    (Term.letDecl
                     (Term.letIdDecl
                      `v
                      []
                      [(Term.typeSpec ":" `term)]
                      ":="
                      (Term.app `coeffs_reduce [`n `u `u])))
                    []
                    (Term.let
                     "let"
                     (Term.letDecl
                      (Term.letIdDecl
                       `r
                       []
                       [(Term.typeSpec ":" `term)]
                       ":="
                       (Term.app `rhs [`n `u `u])))
                     []
                     (Term.do
                      "do"
                      (Term.doSeqIndent
                       [(Term.doSeqItem
                         (Term.doLetArrow
                          "let"
                          []
                          (Term.doIdDecl `eqs [] "←" (Term.doExpr `get_eqs)))
                         [])
                        (Term.doSeqItem
                         (Term.doLetArrow
                          "let"
                          []
                          (Term.doIdDecl `les [] "←" (Term.doExpr `get_les)))
                         [])
                        (Term.doSeqItem
                         (Term.doExpr
                          (Term.app
                           `set_eqs
                           [(«term_::_» `v "::" (Term.app `eqs [(Term.app `subst [`n `r])]))]))
                         [])
                        (Term.doSeqItem
                         (Term.doExpr
                          (Term.app `set_les [(Term.app `les [(Term.app `subst [`n `r])])]))
                         [])
                        (Term.doSeqItem
                         (Term.doExpr (Term.app `add_ee [(Term.app `ee.reduce [`n])]))
                         [])
                        (Term.doSeqItem (Term.doExpr `elim_eq) [])]))))))))))))
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
          (Term.doLetArrow "let" [] (Term.doIdDecl `t [] "←" (Term.doExpr `head_eq)))
          [])
         (Term.doSeqItem
          (Term.doLetArrow
           "let"
           []
           (Term.doIdDecl `i [] "←" (Term.doExpr (Term.app `get_gcd [`t]))))
          [])
         (Term.doSeqItem
          (Term.doExpr
           (Omega.Tactic.Omega.FindEes.«term_!>>=_;_»
            (Term.app `factor [`i `t])
            " !>>= "
            («term_>>_»
             (Term.app `set_eqs [(«term[_]» "[" [] "]")])
             ">>"
             (Term.app `add_ee [(Term.app `ee.nondiv [`i])]))
            "; "
            (Term.fun
             "fun"
             (Term.basicFun
              [`s]
              []
              "=>"
              (Omega.Tactic.Omega.FindEes.«term_!>>=_;_»
               (Term.app `find_min_coeff [`s])
               " !>>= "
               (Term.app `add_ee [`ee.drop])
               "; "
               (Term.fun
                "fun"
                (Term.basicFun
                 [(Term.anonymousCtor "⟨" [`i "," `n "," `u] "⟩")]
                 []
                 "=>"
                 (termIfThenElse
                  "if"
                  («term_=_» `i "=" (num "1"))
                  "then"
                  (Term.do
                   "do"
                   (Term.doSeqIndent
                    [(Term.doSeqItem
                      (Term.doLetArrow "let" [] (Term.doIdDecl `eqs [] "←" (Term.doExpr `get_eqs)))
                      [])
                     (Term.doSeqItem
                      (Term.doLetArrow "let" [] (Term.doIdDecl `les [] "←" (Term.doExpr `get_les)))
                      [])
                     (Term.doSeqItem
                      (Term.doExpr
                       (Term.app `set_eqs [(Term.app `eqs [(Term.app `cancel [`n `u])])]))
                      [])
                     (Term.doSeqItem
                      (Term.doExpr
                       (Term.app `set_les [(Term.app `les [(Term.app `cancel [`n `u])])]))
                      [])
                     (Term.doSeqItem
                      (Term.doExpr (Term.app `add_ee [(Term.app `ee.cancel [`n])]))
                      [])]))
                  "else"
                  (Term.let
                   "let"
                   (Term.letDecl
                    (Term.letIdDecl
                     `v
                     []
                     [(Term.typeSpec ":" `term)]
                     ":="
                     (Term.app `coeffs_reduce [`n `u `u])))
                   []
                   (Term.let
                    "let"
                    (Term.letDecl
                     (Term.letIdDecl
                      `r
                      []
                      [(Term.typeSpec ":" `term)]
                      ":="
                      (Term.app `rhs [`n `u `u])))
                    []
                    (Term.do
                     "do"
                     (Term.doSeqIndent
                      [(Term.doSeqItem
                        (Term.doLetArrow
                         "let"
                         []
                         (Term.doIdDecl `eqs [] "←" (Term.doExpr `get_eqs)))
                        [])
                       (Term.doSeqItem
                        (Term.doLetArrow
                         "let"
                         []
                         (Term.doIdDecl `les [] "←" (Term.doExpr `get_les)))
                        [])
                       (Term.doSeqItem
                        (Term.doExpr
                         (Term.app
                          `set_eqs
                          [(«term_::_» `v "::" (Term.app `eqs [(Term.app `subst [`n `r])]))]))
                        [])
                       (Term.doSeqItem
                        (Term.doExpr
                         (Term.app `set_les [(Term.app `les [(Term.app `subst [`n `r])])]))
                        [])
                       (Term.doSeqItem
                        (Term.doExpr (Term.app `add_ee [(Term.app `ee.reduce [`n])]))
                        [])
                       (Term.doSeqItem (Term.doExpr `elim_eq) [])]))))))))))))
          [])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doSeqIndent', expected 'Lean.Parser.Term.doSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Omega.Tactic.Omega.FindEes.«term_!>>=_;_»
       (Term.app `factor [`i `t])
       " !>>= "
       («term_>>_»
        (Term.app `set_eqs [(«term[_]» "[" [] "]")])
        ">>"
        (Term.app `add_ee [(Term.app `ee.nondiv [`i])]))
       "; "
       (Term.fun
        "fun"
        (Term.basicFun
         [`s]
         []
         "=>"
         (Omega.Tactic.Omega.FindEes.«term_!>>=_;_»
          (Term.app `find_min_coeff [`s])
          " !>>= "
          (Term.app `add_ee [`ee.drop])
          "; "
          (Term.fun
           "fun"
           (Term.basicFun
            [(Term.anonymousCtor "⟨" [`i "," `n "," `u] "⟩")]
            []
            "=>"
            (termIfThenElse
             "if"
             («term_=_» `i "=" (num "1"))
             "then"
             (Term.do
              "do"
              (Term.doSeqIndent
               [(Term.doSeqItem
                 (Term.doLetArrow "let" [] (Term.doIdDecl `eqs [] "←" (Term.doExpr `get_eqs)))
                 [])
                (Term.doSeqItem
                 (Term.doLetArrow "let" [] (Term.doIdDecl `les [] "←" (Term.doExpr `get_les)))
                 [])
                (Term.doSeqItem
                 (Term.doExpr (Term.app `set_eqs [(Term.app `eqs [(Term.app `cancel [`n `u])])]))
                 [])
                (Term.doSeqItem
                 (Term.doExpr (Term.app `set_les [(Term.app `les [(Term.app `cancel [`n `u])])]))
                 [])
                (Term.doSeqItem (Term.doExpr (Term.app `add_ee [(Term.app `ee.cancel [`n])])) [])]))
             "else"
             (Term.let
              "let"
              (Term.letDecl
               (Term.letIdDecl
                `v
                []
                [(Term.typeSpec ":" `term)]
                ":="
                (Term.app `coeffs_reduce [`n `u `u])))
              []
              (Term.let
               "let"
               (Term.letDecl
                (Term.letIdDecl `r [] [(Term.typeSpec ":" `term)] ":=" (Term.app `rhs [`n `u `u])))
               []
               (Term.do
                "do"
                (Term.doSeqIndent
                 [(Term.doSeqItem
                   (Term.doLetArrow "let" [] (Term.doIdDecl `eqs [] "←" (Term.doExpr `get_eqs)))
                   [])
                  (Term.doSeqItem
                   (Term.doLetArrow "let" [] (Term.doIdDecl `les [] "←" (Term.doExpr `get_les)))
                   [])
                  (Term.doSeqItem
                   (Term.doExpr
                    (Term.app
                     `set_eqs
                     [(«term_::_» `v "::" (Term.app `eqs [(Term.app `subst [`n `r])]))]))
                   [])
                  (Term.doSeqItem
                   (Term.doExpr (Term.app `set_les [(Term.app `les [(Term.app `subst [`n `r])])]))
                   [])
                  (Term.doSeqItem (Term.doExpr (Term.app `add_ee [(Term.app `ee.reduce [`n])])) [])
                  (Term.doSeqItem (Term.doExpr `elim_eq) [])])))))))))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Omega.Tactic.Omega.FindEes.«term_!>>=_;_»', expected 'Omega.Tactic.Omega.FindEes.term_!>>=_;_._@.Tactic.Omega.FindEes._hyg.7'
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
      Find an appropriate equality elimination step for the
          current state and apply it. -/
    unsafe
  def
    elim_eq
    : eqelim Unit
    :=
      do
        let t ← head_eq
          let i ← get_gcd t
          factor i t
            !>>=
            set_eqs [ ] >> add_ee ee.nondiv i
            ;
            fun
              s
                =>
                find_min_coeff s
                  !>>=
                  add_ee ee.drop
                  ;
                  fun
                    ⟨ i , n , u ⟩
                      =>
                      if
                        i = 1
                        then
                        do
                          let eqs ← get_eqs
                            let les ← get_les
                            set_eqs eqs cancel n u
                            set_les les cancel n u
                            add_ee ee.cancel n
                        else
                        let
                          v : term := coeffs_reduce n u u
                          let
                            r : term := rhs n u u
                            do
                              let eqs ← get_eqs
                                let les ← get_les
                                set_eqs v :: eqs subst n r
                                set_les les subst n r
                                add_ee ee.reduce n
                                elim_eq
#align omega.elim_eq omega.elim_eq

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "Find and return the sequence of steps for eliminating\n    all equality constraints in the current state. -/")]
      []
      []
      []
      [(Command.unsafe "unsafe")]
      [])
     (Command.def
      "def"
      (Command.declId `elim_eqs [])
      (Command.optDeclSig [] [(Term.typeSpec ":" (Term.app `eqelim [(Term.app `List [`Ee])]))])
      (Command.declValSimple
       ":="
       (Omega.Tactic.Omega.FindEes.«term_!>>=_;_»
        `elim_eq
        " !>>= "
        `get_ees
        "; "
        (Term.fun "fun" (Term.basicFun [(Term.hole "_")] [] "=>" `elim_eqs)))
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Omega.Tactic.Omega.FindEes.«term_!>>=_;_»
       `elim_eq
       " !>>= "
       `get_ees
       "; "
       (Term.fun "fun" (Term.basicFun [(Term.hole "_")] [] "=>" `elim_eqs)))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Omega.Tactic.Omega.FindEes.«term_!>>=_;_»', expected 'Omega.Tactic.Omega.FindEes.term_!>>=_;_._@.Tactic.Omega.FindEes._hyg.7'
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
      Find and return the sequence of steps for eliminating
          all equality constraints in the current state. -/
    unsafe
  def elim_eqs : eqelim List Ee := elim_eq !>>= get_ees ; fun _ => elim_eqs
#align omega.elim_eqs omega.elim_eqs

/-- Given a linear constrain clause, return a list of steps for eliminating its equality
constraints. -/
unsafe def find_ees : Clause → tactic (List Ee)
  | (eqs, les) => run eqs les elim_eqs
#align omega.find_ees omega.find_ees

end Omega

