/-
Copyright (c) 2021 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky, Chris Hughes

! This file was ported from Lean 3 source module data.list.duplicate
! leanprover-community/mathlib commit 18a5306c091183ac90884daa9373fa3b178e8607
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.List.Nodup

/-!
# List duplicates

## Main definitions

* `list.duplicate x l : Prop` is an inductive property that holds when `x` is a duplicate in `l`

## Implementation details

In this file, `x ∈+ l` notation is shorthand for `list.duplicate x l`.

-/


variable {α : Type _}

namespace List

/-- Property that an element `x : α` of `l : list α` can be found in the list more than once. -/
inductive Duplicate (x : α) : List α → Prop
  | cons_mem {l : List α} : x ∈ l → duplicate (x :: l)
  | cons_duplicate {y : α} {l : List α} : duplicate l → duplicate (y :: l)
#align list.duplicate List.Duplicate

-- mathport name: «expr ∈+ »
local infixl:50 " ∈+ " => List.Duplicate

variable {l : List α} {x : α}

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `Mem.duplicate_cons_self [])
      (Command.declSig
       [(Term.explicitBinder "(" [`h] [":" («term_∈_» `x "∈" `l)] [] ")")]
       (Term.typeSpec ":" (List.Data.List.Duplicate.«term_∈+_» `x " ∈+ " («term_::_» `x "::" `l))))
      (Command.declValSimple ":=" (Term.app `Duplicate.cons_mem [`h]) [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Duplicate.cons_mem [`h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Duplicate.cons_mem
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (List.Data.List.Duplicate.«term_∈+_» `x " ∈+ " («term_::_» `x "::" `l))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'List.Data.List.Duplicate.«term_∈+_»', expected 'List.Data.List.Duplicate.term_∈+_._@.Data.List.Duplicate._hyg.8'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem Mem.duplicate_cons_self ( h : x ∈ l ) : x ∈+ x :: l := Duplicate.cons_mem h
#align list.mem.duplicate_cons_self List.Mem.duplicate_cons_self

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `Duplicate.duplicate_cons [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`h]
         [":" (List.Data.List.Duplicate.«term_∈+_» `x " ∈+ " `l)]
         []
         ")")
        (Term.explicitBinder "(" [`y] [":" `α] [] ")")]
       (Term.typeSpec ":" (List.Data.List.Duplicate.«term_∈+_» `x " ∈+ " («term_::_» `y "::" `l))))
      (Command.declValSimple ":=" (Term.app `Duplicate.cons_duplicate [`h]) [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Duplicate.cons_duplicate [`h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Duplicate.cons_duplicate
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (List.Data.List.Duplicate.«term_∈+_» `x " ∈+ " («term_::_» `y "::" `l))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'List.Data.List.Duplicate.«term_∈+_»', expected 'List.Data.List.Duplicate.term_∈+_._@.Data.List.Duplicate._hyg.8'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  Duplicate.duplicate_cons
  ( h : x ∈+ l ) ( y : α ) : x ∈+ y :: l
  := Duplicate.cons_duplicate h
#align list.duplicate.duplicate_cons List.Duplicate.duplicate_cons

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `Duplicate.mem [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`h]
         [":" (List.Data.List.Duplicate.«term_∈+_» `x " ∈+ " `l)]
         []
         ")")]
       (Term.typeSpec ":" («term_∈_» `x "∈" `l)))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.induction'
            "induction'"
            [(Tactic.casesTarget [] `h)]
            []
            ["with"
             [(Lean.binderIdent `l')
              (Lean.binderIdent `h)
              (Lean.binderIdent `y)
              (Lean.binderIdent `l')
              (Lean.binderIdent `h)
              (Lean.binderIdent `hm)]]
            [])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.exact "exact" (Term.app `mem_cons_self [(Term.hole "_") (Term.hole "_")]))])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.exact "exact" (Term.app `mem_cons_of_mem [(Term.hole "_") `hm]))])])))
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
         [(Tactic.induction'
           "induction'"
           [(Tactic.casesTarget [] `h)]
           []
           ["with"
            [(Lean.binderIdent `l')
             (Lean.binderIdent `h)
             (Lean.binderIdent `y)
             (Lean.binderIdent `l')
             (Lean.binderIdent `h)
             (Lean.binderIdent `hm)]]
           [])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.exact "exact" (Term.app `mem_cons_self [(Term.hole "_") (Term.hole "_")]))])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.exact "exact" (Term.app `mem_cons_of_mem [(Term.hole "_") `hm]))])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.exact "exact" (Term.app `mem_cons_of_mem [(Term.hole "_") `hm]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" (Term.app `mem_cons_of_mem [(Term.hole "_") `hm]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `mem_cons_of_mem [(Term.hole "_") `hm])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hm
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `mem_cons_of_mem
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.exact "exact" (Term.app `mem_cons_self [(Term.hole "_") (Term.hole "_")]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" (Term.app `mem_cons_self [(Term.hole "_") (Term.hole "_")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `mem_cons_self [(Term.hole "_") (Term.hole "_")])
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
      `mem_cons_self
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.induction'
       "induction'"
       [(Tactic.casesTarget [] `h)]
       []
       ["with"
        [(Lean.binderIdent `l')
         (Lean.binderIdent `h)
         (Lean.binderIdent `y)
         (Lean.binderIdent `l')
         (Lean.binderIdent `h)
         (Lean.binderIdent `hm)]]
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_∈_» `x "∈" `l)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `l
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (List.Data.List.Duplicate.«term_∈+_» `x " ∈+ " `l)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'List.Data.List.Duplicate.«term_∈+_»', expected 'List.Data.List.Duplicate.term_∈+_._@.Data.List.Duplicate._hyg.8'
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
  Duplicate.mem
  ( h : x ∈+ l ) : x ∈ l
  := by induction' h with l' h y l' h hm · exact mem_cons_self _ _ · exact mem_cons_of_mem _ hm
#align list.duplicate.mem List.Duplicate.mem

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `Duplicate.mem_cons_self [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`h]
         [":" (List.Data.List.Duplicate.«term_∈+_» `x " ∈+ " («term_::_» `x "::" `l))]
         []
         ")")]
       (Term.typeSpec ":" («term_∈_» `x "∈" `l)))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.cases'
            "cases'"
            [(Tactic.casesTarget [] `h)]
            []
            ["with"
             [(Lean.binderIdent (Term.hole "_"))
              (Lean.binderIdent `h)
              (Lean.binderIdent (Term.hole "_"))
              (Lean.binderIdent (Term.hole "_"))
              (Lean.binderIdent `h)]])
           []
           (tactic__ (cdotTk (patternIgnore (token.«· » "·"))) [(Tactic.exact "exact" `h)])
           []
           (tactic__ (cdotTk (patternIgnore (token.«· » "·"))) [(Tactic.exact "exact" `h.mem)])])))
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
         [(Tactic.cases'
           "cases'"
           [(Tactic.casesTarget [] `h)]
           []
           ["with"
            [(Lean.binderIdent (Term.hole "_"))
             (Lean.binderIdent `h)
             (Lean.binderIdent (Term.hole "_"))
             (Lean.binderIdent (Term.hole "_"))
             (Lean.binderIdent `h)]])
          []
          (tactic__ (cdotTk (patternIgnore (token.«· » "·"))) [(Tactic.exact "exact" `h)])
          []
          (tactic__ (cdotTk (patternIgnore (token.«· » "·"))) [(Tactic.exact "exact" `h.mem)])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__ (cdotTk (patternIgnore (token.«· » "·"))) [(Tactic.exact "exact" `h.mem)])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" `h.mem)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h.mem
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__ (cdotTk (patternIgnore (token.«· » "·"))) [(Tactic.exact "exact" `h)])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" `h)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.cases'
       "cases'"
       [(Tactic.casesTarget [] `h)]
       []
       ["with"
        [(Lean.binderIdent (Term.hole "_"))
         (Lean.binderIdent `h)
         (Lean.binderIdent (Term.hole "_"))
         (Lean.binderIdent (Term.hole "_"))
         (Lean.binderIdent `h)]])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'ident'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_∈_» `x "∈" `l)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `l
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (List.Data.List.Duplicate.«term_∈+_» `x " ∈+ " («term_::_» `x "::" `l))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'List.Data.List.Duplicate.«term_∈+_»', expected 'List.Data.List.Duplicate.term_∈+_._@.Data.List.Duplicate._hyg.8'
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
  Duplicate.mem_cons_self
  ( h : x ∈+ x :: l ) : x ∈ l
  := by cases' h with _ h _ _ h · exact h · exact h.mem
#align list.duplicate.mem_cons_self List.Duplicate.mem_cons_self

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
      (Command.declId `duplicate_cons_self_iff [])
      (Command.declSig
       []
       (Term.typeSpec
        ":"
        («term_↔_»
         (List.Data.List.Duplicate.«term_∈+_» `x " ∈+ " («term_::_» `x "::" `l))
         "↔"
         («term_∈_» `x "∈" `l))))
      (Command.declValSimple
       ":="
       (Term.anonymousCtor "⟨" [`Duplicate.mem_cons_self "," `Mem.duplicate_cons_self] "⟩")
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [`Duplicate.mem_cons_self "," `Mem.duplicate_cons_self] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Mem.duplicate_cons_self
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Duplicate.mem_cons_self
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_↔_»
       (List.Data.List.Duplicate.«term_∈+_» `x " ∈+ " («term_::_» `x "::" `l))
       "↔"
       («term_∈_» `x "∈" `l))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∈_» `x "∈" `l)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `l
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 21 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 20, term))
      (List.Data.List.Duplicate.«term_∈+_» `x " ∈+ " («term_::_» `x "::" `l))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'List.Data.List.Duplicate.«term_∈+_»', expected 'List.Data.List.Duplicate.term_∈+_._@.Data.List.Duplicate._hyg.8'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ simp ]
  theorem
    duplicate_cons_self_iff
    : x ∈+ x :: l ↔ x ∈ l
    := ⟨ Duplicate.mem_cons_self , Mem.duplicate_cons_self ⟩
#align list.duplicate_cons_self_iff List.duplicate_cons_self_iff

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `Duplicate.ne_nil [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`h]
         [":" (List.Data.List.Duplicate.«term_∈+_» `x " ∈+ " `l)]
         []
         ")")]
       (Term.typeSpec ":" («term_≠_» `l "≠" («term[_]» "[" [] "]"))))
      (Command.declValSimple
       ":="
       (Term.fun
        "fun"
        (Term.basicFun
         [`H]
         []
         "=>"
         (Term.app
          (Term.proj (Term.app `mem_nil_iff [`x]) "." `mp)
          [(Term.subst `H "▸" [(Term.proj `h "." `Mem)])])))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`H]
        []
        "=>"
        (Term.app
         (Term.proj (Term.app `mem_nil_iff [`x]) "." `mp)
         [(Term.subst `H "▸" [(Term.proj `h "." `Mem)])])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj (Term.app `mem_nil_iff [`x]) "." `mp)
       [(Term.subst `H "▸" [(Term.proj `h "." `Mem)])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.subst', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.subst', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.subst `H "▸" [(Term.proj `h "." `Mem)])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `h "." `Mem)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `h
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 75 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 75, term))
      `H
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 75, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 75, (some 75, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.subst `H "▸" [(Term.proj `h "." `Mem)])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app `mem_nil_iff [`x]) "." `mp)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `mem_nil_iff [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `mem_nil_iff
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `mem_nil_iff [`x]) ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `H
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_≠_» `l "≠" («term[_]» "[" [] "]"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term[_]» "[" [] "]")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `l
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (List.Data.List.Duplicate.«term_∈+_» `x " ∈+ " `l)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'List.Data.List.Duplicate.«term_∈+_»', expected 'List.Data.List.Duplicate.term_∈+_._@.Data.List.Duplicate._hyg.8'
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
theorem Duplicate.ne_nil ( h : x ∈+ l ) : l ≠ [ ] := fun H => mem_nil_iff x . mp H ▸ h . Mem
#align list.duplicate.ne_nil List.Duplicate.ne_nil

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
      (Command.declId `not_duplicate_nil [])
      (Command.declSig
       [(Term.explicitBinder "(" [`x] [":" `α] [] ")")]
       (Term.typeSpec
        ":"
        («term¬_» "¬" (List.Data.List.Duplicate.«term_∈+_» `x " ∈+ " («term[_]» "[" [] "]")))))
      (Command.declValSimple
       ":="
       (Term.fun "fun" (Term.basicFun [`H] [] "=>" (Term.app (Term.proj `H "." `ne_nil) [`rfl])))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun "fun" (Term.basicFun [`H] [] "=>" (Term.app (Term.proj `H "." `ne_nil) [`rfl])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj `H "." `ne_nil) [`rfl])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rfl
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `H "." `ne_nil)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `H
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `H
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term¬_» "¬" (List.Data.List.Duplicate.«term_∈+_» `x " ∈+ " («term[_]» "[" [] "]")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (List.Data.List.Duplicate.«term_∈+_» `x " ∈+ " («term[_]» "[" [] "]"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'List.Data.List.Duplicate.«term_∈+_»', expected 'List.Data.List.Duplicate.term_∈+_._@.Data.List.Duplicate._hyg.8'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ simp ] theorem not_duplicate_nil ( x : α ) : ¬ x ∈+ [ ] := fun H => H . ne_nil rfl
#align list.not_duplicate_nil List.not_duplicate_nil

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `Duplicate.ne_singleton [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`h]
         [":" (List.Data.List.Duplicate.«term_∈+_» `x " ∈+ " `l)]
         []
         ")")
        (Term.explicitBinder "(" [`y] [":" `α] [] ")")]
       (Term.typeSpec ":" («term_≠_» `l "≠" («term[_]» "[" [`y] "]"))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.induction'
            "induction'"
            [(Tactic.casesTarget [] `h)]
            []
            ["with"
             [(Lean.binderIdent `l')
              (Lean.binderIdent `h)
              (Lean.binderIdent `z)
              (Lean.binderIdent `l')
              (Lean.binderIdent `h)
              (Lean.binderIdent `hm)]]
            [])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.simp
              "simp"
              []
              []
              []
              ["[" [(Tactic.simpLemma [] [] (Term.app `ne_nil_of_mem [`h]))] "]"]
              [])])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.simp
              "simp"
              []
              []
              []
              ["[" [(Tactic.simpLemma [] [] (Term.app `ne_nil_of_mem [`h.mem]))] "]"]
              [])])])))
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
         [(Tactic.induction'
           "induction'"
           [(Tactic.casesTarget [] `h)]
           []
           ["with"
            [(Lean.binderIdent `l')
             (Lean.binderIdent `h)
             (Lean.binderIdent `z)
             (Lean.binderIdent `l')
             (Lean.binderIdent `h)
             (Lean.binderIdent `hm)]]
           [])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.simp
             "simp"
             []
             []
             []
             ["[" [(Tactic.simpLemma [] [] (Term.app `ne_nil_of_mem [`h]))] "]"]
             [])])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.simp
             "simp"
             []
             []
             []
             ["[" [(Tactic.simpLemma [] [] (Term.app `ne_nil_of_mem [`h.mem]))] "]"]
             [])])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.simp
         "simp"
         []
         []
         []
         ["[" [(Tactic.simpLemma [] [] (Term.app `ne_nil_of_mem [`h.mem]))] "]"]
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       []
       ["[" [(Tactic.simpLemma [] [] (Term.app `ne_nil_of_mem [`h.mem]))] "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `ne_nil_of_mem [`h.mem])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h.mem
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `ne_nil_of_mem
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.simp
         "simp"
         []
         []
         []
         ["[" [(Tactic.simpLemma [] [] (Term.app `ne_nil_of_mem [`h]))] "]"]
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       []
       ["[" [(Tactic.simpLemma [] [] (Term.app `ne_nil_of_mem [`h]))] "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `ne_nil_of_mem [`h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `ne_nil_of_mem
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.induction'
       "induction'"
       [(Tactic.casesTarget [] `h)]
       []
       ["with"
        [(Lean.binderIdent `l')
         (Lean.binderIdent `h)
         (Lean.binderIdent `z)
         (Lean.binderIdent `l')
         (Lean.binderIdent `h)
         (Lean.binderIdent `hm)]]
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_≠_» `l "≠" («term[_]» "[" [`y] "]"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term[_]» "[" [`y] "]")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `l
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `α
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (List.Data.List.Duplicate.«term_∈+_» `x " ∈+ " `l)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'List.Data.List.Duplicate.«term_∈+_»', expected 'List.Data.List.Duplicate.term_∈+_._@.Data.List.Duplicate._hyg.8'
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
  Duplicate.ne_singleton
  ( h : x ∈+ l ) ( y : α ) : l ≠ [ y ]
  := by induction' h with l' h z l' h hm · simp [ ne_nil_of_mem h ] · simp [ ne_nil_of_mem h.mem ]
#align list.duplicate.ne_singleton List.Duplicate.ne_singleton

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
      (Command.declId `not_duplicate_singleton [])
      (Command.declSig
       [(Term.explicitBinder "(" [`x `y] [":" `α] [] ")")]
       (Term.typeSpec
        ":"
        («term¬_» "¬" (List.Data.List.Duplicate.«term_∈+_» `x " ∈+ " («term[_]» "[" [`y] "]")))))
      (Command.declValSimple
       ":="
       (Term.fun
        "fun"
        (Term.basicFun
         [`H]
         []
         "=>"
         (Term.app (Term.proj `H "." `ne_singleton) [(Term.hole "_") `rfl])))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`H]
        []
        "=>"
        (Term.app (Term.proj `H "." `ne_singleton) [(Term.hole "_") `rfl])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj `H "." `ne_singleton) [(Term.hole "_") `rfl])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rfl
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `H "." `ne_singleton)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `H
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `H
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term¬_» "¬" (List.Data.List.Duplicate.«term_∈+_» `x " ∈+ " («term[_]» "[" [`y] "]")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (List.Data.List.Duplicate.«term_∈+_» `x " ∈+ " («term[_]» "[" [`y] "]"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'List.Data.List.Duplicate.«term_∈+_»', expected 'List.Data.List.Duplicate.term_∈+_._@.Data.List.Duplicate._hyg.8'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ simp ]
  theorem not_duplicate_singleton ( x y : α ) : ¬ x ∈+ [ y ] := fun H => H . ne_singleton _ rfl
#align list.not_duplicate_singleton List.not_duplicate_singleton

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `Duplicate.elim_nil [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`h]
         [":" (List.Data.List.Duplicate.«term_∈+_» `x " ∈+ " («term[_]» "[" [] "]"))]
         []
         ")")]
       (Term.typeSpec ":" `False))
      (Command.declValSimple ":=" (Term.app `not_duplicate_nil [`x `h]) [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `not_duplicate_nil [`x `h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `not_duplicate_nil
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      `False
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (List.Data.List.Duplicate.«term_∈+_» `x " ∈+ " («term[_]» "[" [] "]"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'List.Data.List.Duplicate.«term_∈+_»', expected 'List.Data.List.Duplicate.term_∈+_._@.Data.List.Duplicate._hyg.8'
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
theorem Duplicate.elim_nil ( h : x ∈+ [ ] ) : False := not_duplicate_nil x h
#align list.duplicate.elim_nil List.Duplicate.elim_nil

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `Duplicate.elim_singleton [])
      (Command.declSig
       [(Term.implicitBinder "{" [`y] [":" `α] "}")
        (Term.explicitBinder
         "("
         [`h]
         [":" (List.Data.List.Duplicate.«term_∈+_» `x " ∈+ " («term[_]» "[" [`y] "]"))]
         []
         ")")]
       (Term.typeSpec ":" `False))
      (Command.declValSimple ":=" (Term.app `not_duplicate_singleton [`x `y `h]) [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `not_duplicate_singleton [`x `y `h])
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
      `not_duplicate_singleton
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      `False
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (List.Data.List.Duplicate.«term_∈+_» `x " ∈+ " («term[_]» "[" [`y] "]"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'List.Data.List.Duplicate.«term_∈+_»', expected 'List.Data.List.Duplicate.term_∈+_._@.Data.List.Duplicate._hyg.8'
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
  Duplicate.elim_singleton
  { y : α } ( h : x ∈+ [ y ] ) : False
  := not_duplicate_singleton x y h
#align list.duplicate.elim_singleton List.Duplicate.elim_singleton

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `duplicate_cons_iff [])
      (Command.declSig
       [(Term.implicitBinder "{" [`y] [":" `α] "}")]
       (Term.typeSpec
        ":"
        («term_↔_»
         (List.Data.List.Duplicate.«term_∈+_» `x " ∈+ " («term_::_» `y "::" `l))
         "↔"
         («term_∨_»
          («term_∧_» («term_=_» `y "=" `x) "∧" («term_∈_» `x "∈" `l))
          "∨"
          (List.Data.List.Duplicate.«term_∈+_» `x " ∈+ " `l)))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.refine'
            "refine'"
            (Term.anonymousCtor
             "⟨"
             [(Term.fun "fun" (Term.basicFun [`h] [] "=>" (Term.hole "_")))
              ","
              (Term.fun "fun" (Term.basicFun [`h] [] "=>" (Term.hole "_")))]
             "⟩"))
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.cases'
              "cases'"
              [(Tactic.casesTarget [] `h)]
              []
              ["with"
               [(Lean.binderIdent (Term.hole "_"))
                (Lean.binderIdent `hm)
                (Lean.binderIdent (Term.hole "_"))
                (Lean.binderIdent (Term.hole "_"))
                (Lean.binderIdent `hm)]])
             []
             (tactic__
              (cdotTk (patternIgnore (token.«· » "·")))
              [(Tactic.exact
                "exact"
                (Term.app `Or.inl [(Term.anonymousCtor "⟨" [`rfl "," `hm] "⟩")]))])
             []
             (tactic__
              (cdotTk (patternIgnore (token.«· » "·")))
              [(Tactic.exact "exact" (Term.app `Or.inr [`hm]))])])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Std.Tactic.rcases
              "rcases"
              [(Tactic.casesTarget [] `h)]
              ["with"
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed
                 [(Std.Tactic.RCases.rcasesPat.paren
                   "("
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed
                     [(Std.Tactic.RCases.rcasesPat.tuple
                       "⟨"
                       [(Std.Tactic.RCases.rcasesPatLo
                         (Std.Tactic.RCases.rcasesPatMed
                          [(Std.Tactic.RCases.rcasesPat.one `rfl)
                           "|"
                           (Std.Tactic.RCases.rcasesPat.one `h)])
                         [])]
                       "⟩")
                      "|"
                      (Std.Tactic.RCases.rcasesPat.one `h)])
                    [])
                   ")")])
                [])])
             []
             (tactic__
              (cdotTk (patternIgnore (token.«· » "·")))
              [(Std.Tactic.Simpa.simpa
                "simpa"
                []
                []
                (Std.Tactic.Simpa.simpaArgsRest [] [] [] [] []))])
             []
             (tactic__
              (cdotTk (patternIgnore (token.«· » "·")))
              [(Tactic.exact "exact" `h.cons_duplicate)])])])))
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
         [(Tactic.refine'
           "refine'"
           (Term.anonymousCtor
            "⟨"
            [(Term.fun "fun" (Term.basicFun [`h] [] "=>" (Term.hole "_")))
             ","
             (Term.fun "fun" (Term.basicFun [`h] [] "=>" (Term.hole "_")))]
            "⟩"))
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.cases'
             "cases'"
             [(Tactic.casesTarget [] `h)]
             []
             ["with"
              [(Lean.binderIdent (Term.hole "_"))
               (Lean.binderIdent `hm)
               (Lean.binderIdent (Term.hole "_"))
               (Lean.binderIdent (Term.hole "_"))
               (Lean.binderIdent `hm)]])
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(Tactic.exact
               "exact"
               (Term.app `Or.inl [(Term.anonymousCtor "⟨" [`rfl "," `hm] "⟩")]))])
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(Tactic.exact "exact" (Term.app `Or.inr [`hm]))])])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Std.Tactic.rcases
             "rcases"
             [(Tactic.casesTarget [] `h)]
             ["with"
              (Std.Tactic.RCases.rcasesPatLo
               (Std.Tactic.RCases.rcasesPatMed
                [(Std.Tactic.RCases.rcasesPat.paren
                  "("
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed
                    [(Std.Tactic.RCases.rcasesPat.tuple
                      "⟨"
                      [(Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed
                         [(Std.Tactic.RCases.rcasesPat.one `rfl)
                          "|"
                          (Std.Tactic.RCases.rcasesPat.one `h)])
                        [])]
                      "⟩")
                     "|"
                     (Std.Tactic.RCases.rcasesPat.one `h)])
                   [])
                  ")")])
               [])])
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(Std.Tactic.Simpa.simpa
               "simpa"
               []
               []
               (Std.Tactic.Simpa.simpaArgsRest [] [] [] [] []))])
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(Tactic.exact "exact" `h.cons_duplicate)])])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Std.Tactic.rcases
         "rcases"
         [(Tactic.casesTarget [] `h)]
         ["with"
          (Std.Tactic.RCases.rcasesPatLo
           (Std.Tactic.RCases.rcasesPatMed
            [(Std.Tactic.RCases.rcasesPat.paren
              "("
              (Std.Tactic.RCases.rcasesPatLo
               (Std.Tactic.RCases.rcasesPatMed
                [(Std.Tactic.RCases.rcasesPat.tuple
                  "⟨"
                  [(Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed
                     [(Std.Tactic.RCases.rcasesPat.one `rfl)
                      "|"
                      (Std.Tactic.RCases.rcasesPat.one `h)])
                    [])]
                  "⟩")
                 "|"
                 (Std.Tactic.RCases.rcasesPat.one `h)])
               [])
              ")")])
           [])])
        []
        (tactic__
         (cdotTk (patternIgnore (token.«· » "·")))
         [(Std.Tactic.Simpa.simpa "simpa" [] [] (Std.Tactic.Simpa.simpaArgsRest [] [] [] [] []))])
        []
        (tactic__
         (cdotTk (patternIgnore (token.«· » "·")))
         [(Tactic.exact "exact" `h.cons_duplicate)])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.exact "exact" `h.cons_duplicate)])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" `h.cons_duplicate)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h.cons_duplicate
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Std.Tactic.Simpa.simpa "simpa" [] [] (Std.Tactic.Simpa.simpaArgsRest [] [] [] [] []))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Simpa.simpa "simpa" [] [] (Std.Tactic.Simpa.simpaArgsRest [] [] [] [] []))
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.rcases
       "rcases"
       [(Tactic.casesTarget [] `h)]
       ["with"
        (Std.Tactic.RCases.rcasesPatLo
         (Std.Tactic.RCases.rcasesPatMed
          [(Std.Tactic.RCases.rcasesPat.paren
            "("
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed
              [(Std.Tactic.RCases.rcasesPat.tuple
                "⟨"
                [(Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed
                   [(Std.Tactic.RCases.rcasesPat.one `rfl)
                    "|"
                    (Std.Tactic.RCases.rcasesPat.one `h)])
                  [])]
                "⟩")
               "|"
               (Std.Tactic.RCases.rcasesPat.one `h)])
             [])
            ")")])
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.cases'
         "cases'"
         [(Tactic.casesTarget [] `h)]
         []
         ["with"
          [(Lean.binderIdent (Term.hole "_"))
           (Lean.binderIdent `hm)
           (Lean.binderIdent (Term.hole "_"))
           (Lean.binderIdent (Term.hole "_"))
           (Lean.binderIdent `hm)]])
        []
        (tactic__
         (cdotTk (patternIgnore (token.«· » "·")))
         [(Tactic.exact "exact" (Term.app `Or.inl [(Term.anonymousCtor "⟨" [`rfl "," `hm] "⟩")]))])
        []
        (tactic__
         (cdotTk (patternIgnore (token.«· » "·")))
         [(Tactic.exact "exact" (Term.app `Or.inr [`hm]))])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.exact "exact" (Term.app `Or.inr [`hm]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" (Term.app `Or.inr [`hm]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Or.inr [`hm])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hm
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Or.inr
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.exact "exact" (Term.app `Or.inl [(Term.anonymousCtor "⟨" [`rfl "," `hm] "⟩")]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" (Term.app `Or.inl [(Term.anonymousCtor "⟨" [`rfl "," `hm] "⟩")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Or.inl [(Term.anonymousCtor "⟨" [`rfl "," `hm] "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [`rfl "," `hm] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hm
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rfl
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Or.inl
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.cases'
       "cases'"
       [(Tactic.casesTarget [] `h)]
       []
       ["with"
        [(Lean.binderIdent (Term.hole "_"))
         (Lean.binderIdent `hm)
         (Lean.binderIdent (Term.hole "_"))
         (Lean.binderIdent (Term.hole "_"))
         (Lean.binderIdent `hm)]])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'ident'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine'
       "refine'"
       (Term.anonymousCtor
        "⟨"
        [(Term.fun "fun" (Term.basicFun [`h] [] "=>" (Term.hole "_")))
         ","
         (Term.fun "fun" (Term.basicFun [`h] [] "=>" (Term.hole "_")))]
        "⟩"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.fun "fun" (Term.basicFun [`h] [] "=>" (Term.hole "_")))
        ","
        (Term.fun "fun" (Term.basicFun [`h] [] "=>" (Term.hole "_")))]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun "fun" (Term.basicFun [`h] [] "=>" (Term.hole "_")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun "fun" (Term.basicFun [`h] [] "=>" (Term.hole "_")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_↔_»
       (List.Data.List.Duplicate.«term_∈+_» `x " ∈+ " («term_::_» `y "::" `l))
       "↔"
       («term_∨_»
        («term_∧_» («term_=_» `y "=" `x) "∧" («term_∈_» `x "∈" `l))
        "∨"
        (List.Data.List.Duplicate.«term_∈+_» `x " ∈+ " `l)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∨_»
       («term_∧_» («term_=_» `y "=" `x) "∧" («term_∈_» `x "∈" `l))
       "∨"
       (List.Data.List.Duplicate.«term_∈+_» `x " ∈+ " `l))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (List.Data.List.Duplicate.«term_∈+_» `x " ∈+ " `l)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'List.Data.List.Duplicate.«term_∈+_»', expected 'List.Data.List.Duplicate.term_∈+_._@.Data.List.Duplicate._hyg.8'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  duplicate_cons_iff
  { y : α } : x ∈+ y :: l ↔ y = x ∧ x ∈ l ∨ x ∈+ l
  :=
    by
      refine' ⟨ fun h => _ , fun h => _ ⟩
        · cases' h with _ hm _ _ hm · exact Or.inl ⟨ rfl , hm ⟩ · exact Or.inr hm
        · rcases h with ( ⟨ rfl | h ⟩ | h ) · simpa · exact h.cons_duplicate
#align list.duplicate_cons_iff List.duplicate_cons_iff

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `Duplicate.of_duplicate_cons [])
      (Command.declSig
       [(Term.implicitBinder "{" [`y] [":" `α] "}")
        (Term.explicitBinder
         "("
         [`h]
         [":" (List.Data.List.Duplicate.«term_∈+_» `x " ∈+ " («term_::_» `y "::" `l))]
         []
         ")")
        (Term.explicitBinder "(" [`hx] [":" («term_≠_» `x "≠" `y)] [] ")")]
       (Term.typeSpec ":" (List.Data.List.Duplicate.«term_∈+_» `x " ∈+ " `l)))
      (Command.declValSimple
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
               [(Tactic.simpLemma [] [] `duplicate_cons_iff) "," (Tactic.simpLemma [] [] `hx.symm)]
               "]")]
             ["using" `h]))])))
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
              [(Tactic.simpLemma [] [] `duplicate_cons_iff) "," (Tactic.simpLemma [] [] `hx.symm)]
              "]")]
            ["using" `h]))])))
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
          [(Tactic.simpLemma [] [] `duplicate_cons_iff) "," (Tactic.simpLemma [] [] `hx.symm)]
          "]")]
        ["using" `h]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hx.symm
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `duplicate_cons_iff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (List.Data.List.Duplicate.«term_∈+_» `x " ∈+ " `l)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'List.Data.List.Duplicate.«term_∈+_»', expected 'List.Data.List.Duplicate.term_∈+_._@.Data.List.Duplicate._hyg.8'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  Duplicate.of_duplicate_cons
  { y : α } ( h : x ∈+ y :: l ) ( hx : x ≠ y ) : x ∈+ l
  := by simpa [ duplicate_cons_iff , hx.symm ] using h
#align list.duplicate.of_duplicate_cons List.Duplicate.of_duplicate_cons

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `duplicate_cons_iff_of_ne [])
      (Command.declSig
       [(Term.implicitBinder "{" [`y] [":" `α] "}")
        (Term.explicitBinder "(" [`hne] [":" («term_≠_» `x "≠" `y)] [] ")")]
       (Term.typeSpec
        ":"
        («term_↔_»
         (List.Data.List.Duplicate.«term_∈+_» `x " ∈+ " («term_::_» `y "::" `l))
         "↔"
         (List.Data.List.Duplicate.«term_∈+_» `x " ∈+ " `l))))
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
            []
            ["["
             [(Tactic.simpLemma [] [] `duplicate_cons_iff) "," (Tactic.simpLemma [] [] `hne.symm)]
             "]"]
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
         [(Tactic.simp
           "simp"
           []
           []
           []
           ["["
            [(Tactic.simpLemma [] [] `duplicate_cons_iff) "," (Tactic.simpLemma [] [] `hne.symm)]
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
        [(Tactic.simpLemma [] [] `duplicate_cons_iff) "," (Tactic.simpLemma [] [] `hne.symm)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hne.symm
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `duplicate_cons_iff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_↔_»
       (List.Data.List.Duplicate.«term_∈+_» `x " ∈+ " («term_::_» `y "::" `l))
       "↔"
       (List.Data.List.Duplicate.«term_∈+_» `x " ∈+ " `l))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (List.Data.List.Duplicate.«term_∈+_» `x " ∈+ " `l)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'List.Data.List.Duplicate.«term_∈+_»', expected 'List.Data.List.Duplicate.term_∈+_._@.Data.List.Duplicate._hyg.8'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  duplicate_cons_iff_of_ne
  { y : α } ( hne : x ≠ y ) : x ∈+ y :: l ↔ x ∈+ l
  := by simp [ duplicate_cons_iff , hne.symm ]
#align list.duplicate_cons_iff_of_ne List.duplicate_cons_iff_of_ne

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `Duplicate.mono_sublist [])
      (Command.declSig
       [(Term.implicitBinder "{" [`l'] [":" (Term.app `List [`α])] "}")
        (Term.explicitBinder
         "("
         [`hx]
         [":" (List.Data.List.Duplicate.«term_∈+_» `x " ∈+ " `l)]
         []
         ")")
        (Term.explicitBinder
         "("
         [`h]
         [":" (List.Init.Data.List.Lemmas.«term_<+_» `l " <+ " `l')]
         []
         ")")]
       (Term.typeSpec ":" (List.Data.List.Duplicate.«term_∈+_» `x " ∈+ " `l')))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.induction'
            "induction'"
            [(Tactic.casesTarget [] `h)]
            []
            ["with"
             [(Lean.binderIdent `l₁)
              (Lean.binderIdent `l₂)
              (Lean.binderIdent `y)
              (Lean.binderIdent `h)
              (Lean.binderIdent `IH)
              (Lean.binderIdent `l₁)
              (Lean.binderIdent `l₂)
              (Lean.binderIdent `y)
              (Lean.binderIdent `h)
              (Lean.binderIdent `IH)]]
            [])
           []
           (tactic__ (cdotTk (patternIgnore (token.«· » "·"))) [(Tactic.exact "exact" `hx)])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.exact
              "exact"
              (Term.app (Term.proj (Term.app `IH [`hx]) "." `duplicate_cons) [(Term.hole "_")]))])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `duplicate_cons_iff)] "]")
              [(Tactic.location "at" (Tactic.locationHyp [`hx] [(patternIgnore (token.«⊢» "⊢"))]))])
             []
             (Std.Tactic.rcases
              "rcases"
              [(Tactic.casesTarget [] `hx)]
              ["with"
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed
                 [(Std.Tactic.RCases.rcasesPat.paren
                   "("
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed
                     [(Std.Tactic.RCases.rcasesPat.tuple
                       "⟨"
                       [(Std.Tactic.RCases.rcasesPatLo
                         (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                         [])
                        ","
                        (Std.Tactic.RCases.rcasesPatLo
                         (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hx)])
                         [])]
                       "⟩")
                      "|"
                      (Std.Tactic.RCases.rcasesPat.one `hx)])
                    [])
                   ")")])
                [])])
             []
             (tactic__
              (cdotTk (patternIgnore (token.«· » "·")))
              [(Tactic.simp
                "simp"
                []
                []
                []
                ["[" [(Tactic.simpLemma [] [] (Term.app `h.subset [`hx]))] "]"]
                [])])
             []
             (tactic__
              (cdotTk (patternIgnore (token.«· » "·")))
              [(Tactic.simp
                "simp"
                []
                []
                []
                ["[" [(Tactic.simpLemma [] [] (Term.app `IH [`hx]))] "]"]
                [])])])])))
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
         [(Tactic.induction'
           "induction'"
           [(Tactic.casesTarget [] `h)]
           []
           ["with"
            [(Lean.binderIdent `l₁)
             (Lean.binderIdent `l₂)
             (Lean.binderIdent `y)
             (Lean.binderIdent `h)
             (Lean.binderIdent `IH)
             (Lean.binderIdent `l₁)
             (Lean.binderIdent `l₂)
             (Lean.binderIdent `y)
             (Lean.binderIdent `h)
             (Lean.binderIdent `IH)]]
           [])
          []
          (tactic__ (cdotTk (patternIgnore (token.«· » "·"))) [(Tactic.exact "exact" `hx)])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.exact
             "exact"
             (Term.app (Term.proj (Term.app `IH [`hx]) "." `duplicate_cons) [(Term.hole "_")]))])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `duplicate_cons_iff)] "]")
             [(Tactic.location "at" (Tactic.locationHyp [`hx] [(patternIgnore (token.«⊢» "⊢"))]))])
            []
            (Std.Tactic.rcases
             "rcases"
             [(Tactic.casesTarget [] `hx)]
             ["with"
              (Std.Tactic.RCases.rcasesPatLo
               (Std.Tactic.RCases.rcasesPatMed
                [(Std.Tactic.RCases.rcasesPat.paren
                  "("
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed
                    [(Std.Tactic.RCases.rcasesPat.tuple
                      "⟨"
                      [(Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                        [])
                       ","
                       (Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hx)])
                        [])]
                      "⟩")
                     "|"
                     (Std.Tactic.RCases.rcasesPat.one `hx)])
                   [])
                  ")")])
               [])])
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(Tactic.simp
               "simp"
               []
               []
               []
               ["[" [(Tactic.simpLemma [] [] (Term.app `h.subset [`hx]))] "]"]
               [])])
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(Tactic.simp
               "simp"
               []
               []
               []
               ["[" [(Tactic.simpLemma [] [] (Term.app `IH [`hx]))] "]"]
               [])])])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `duplicate_cons_iff)] "]")
         [(Tactic.location "at" (Tactic.locationHyp [`hx] [(patternIgnore (token.«⊢» "⊢"))]))])
        []
        (Std.Tactic.rcases
         "rcases"
         [(Tactic.casesTarget [] `hx)]
         ["with"
          (Std.Tactic.RCases.rcasesPatLo
           (Std.Tactic.RCases.rcasesPatMed
            [(Std.Tactic.RCases.rcasesPat.paren
              "("
              (Std.Tactic.RCases.rcasesPatLo
               (Std.Tactic.RCases.rcasesPatMed
                [(Std.Tactic.RCases.rcasesPat.tuple
                  "⟨"
                  [(Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hx)])
                    [])]
                  "⟩")
                 "|"
                 (Std.Tactic.RCases.rcasesPat.one `hx)])
               [])
              ")")])
           [])])
        []
        (tactic__
         (cdotTk (patternIgnore (token.«· » "·")))
         [(Tactic.simp
           "simp"
           []
           []
           []
           ["[" [(Tactic.simpLemma [] [] (Term.app `h.subset [`hx]))] "]"]
           [])])
        []
        (tactic__
         (cdotTk (patternIgnore (token.«· » "·")))
         [(Tactic.simp
           "simp"
           []
           []
           []
           ["[" [(Tactic.simpLemma [] [] (Term.app `IH [`hx]))] "]"]
           [])])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] (Term.app `IH [`hx]))] "]"] [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] (Term.app `IH [`hx]))] "]"] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `IH [`hx])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hx
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `IH
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.simp
         "simp"
         []
         []
         []
         ["[" [(Tactic.simpLemma [] [] (Term.app `h.subset [`hx]))] "]"]
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       []
       ["[" [(Tactic.simpLemma [] [] (Term.app `h.subset [`hx]))] "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `h.subset [`hx])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hx
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `h.subset
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.rcases
       "rcases"
       [(Tactic.casesTarget [] `hx)]
       ["with"
        (Std.Tactic.RCases.rcasesPatLo
         (Std.Tactic.RCases.rcasesPatMed
          [(Std.Tactic.RCases.rcasesPat.paren
            "("
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed
              [(Std.Tactic.RCases.rcasesPat.tuple
                "⟨"
                [(Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hx)])
                  [])]
                "⟩")
               "|"
               (Std.Tactic.RCases.rcasesPat.one `hx)])
             [])
            ")")])
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hx
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `duplicate_cons_iff)] "]")
       [(Tactic.location "at" (Tactic.locationHyp [`hx] [(patternIgnore (token.«⊢» "⊢"))]))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hx
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `duplicate_cons_iff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.exact
         "exact"
         (Term.app (Term.proj (Term.app `IH [`hx]) "." `duplicate_cons) [(Term.hole "_")]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.app (Term.proj (Term.app `IH [`hx]) "." `duplicate_cons) [(Term.hole "_")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj (Term.app `IH [`hx]) "." `duplicate_cons) [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app `IH [`hx]) "." `duplicate_cons)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `IH [`hx])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hx
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `IH
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `IH [`hx]) ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__ (cdotTk (patternIgnore (token.«· » "·"))) [(Tactic.exact "exact" `hx)])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" `hx)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hx
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.induction'
       "induction'"
       [(Tactic.casesTarget [] `h)]
       []
       ["with"
        [(Lean.binderIdent `l₁)
         (Lean.binderIdent `l₂)
         (Lean.binderIdent `y)
         (Lean.binderIdent `h)
         (Lean.binderIdent `IH)
         (Lean.binderIdent `l₁)
         (Lean.binderIdent `l₂)
         (Lean.binderIdent `y)
         (Lean.binderIdent `h)
         (Lean.binderIdent `IH)]]
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (List.Data.List.Duplicate.«term_∈+_» `x " ∈+ " `l')
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'List.Data.List.Duplicate.«term_∈+_»', expected 'List.Data.List.Duplicate.term_∈+_._@.Data.List.Duplicate._hyg.8'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  Duplicate.mono_sublist
  { l' : List α } ( hx : x ∈+ l ) ( h : l <+ l' ) : x ∈+ l'
  :=
    by
      induction' h with l₁ l₂ y h IH l₁ l₂ y h IH
        · exact hx
        · exact IH hx . duplicate_cons _
        ·
          rw [ duplicate_cons_iff ] at hx ⊢
            rcases hx with ( ⟨ rfl , hx ⟩ | hx )
            · simp [ h.subset hx ]
            · simp [ IH hx ]
#align list.duplicate.mono_sublist List.Duplicate.mono_sublist

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment "/--" "The contrapositive of `list.nodup_iff_sublist`. -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `duplicate_iff_sublist [])
      (Command.declSig
       []
       (Term.typeSpec
        ":"
        («term_↔_»
         (List.Data.List.Duplicate.«term_∈+_» `x " ∈+ " `l)
         "↔"
         (List.Init.Data.List.Lemmas.«term_<+_» («term[_]» "[" [`x "," `x] "]") " <+ " `l))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.induction'
            "induction'"
            [(Tactic.casesTarget [] `l)]
            []
            ["with" [(Lean.binderIdent `y) (Lean.binderIdent `l) (Lean.binderIdent `IH)]]
            [])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.simp "simp" [] [] [] [] [])])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Classical.«tacticBy_cases_:_» "by_cases" [`hx ":"] («term_=_» `x "=" `y))
             []
             (tactic__
              (cdotTk (patternIgnore (token.«· » "·")))
              [(Tactic.simp
                "simp"
                []
                []
                []
                ["["
                 [(Tactic.simpLemma [] [] `hx)
                  ","
                  (Tactic.simpLemma [] [] `cons_sublist_cons_iff)
                  ","
                  (Tactic.simpLemma [] [] `singleton_sublist)]
                 "]"]
                [])])
             []
             (tactic__
              (cdotTk (patternIgnore (token.«· » "·")))
              [(Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule [] (Term.app `duplicate_cons_iff_of_ne [`hx]))
                  ","
                  (Tactic.rwRule [] `IH)]
                 "]")
                [])
               []
               (Tactic.refine'
                "refine'"
                (Term.anonymousCtor
                 "⟨"
                 [(Term.app `sublist_cons_of_sublist [`y])
                  ","
                  (Term.fun "fun" (Term.basicFun [`h] [] "=>" (Term.hole "_")))]
                 "⟩"))
               []
               (Tactic.cases "cases" [(Tactic.casesTarget [] `h)] [] [])
               []
               (tactic__
                (cdotTk (patternIgnore (token.«· » "·")))
                [(Tactic.assumption "assumption")])
               []
               (tactic__
                (cdotTk (patternIgnore (token.«· » "·")))
                [(Tactic.contradiction "contradiction")])])])])))
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
         [(Tactic.induction'
           "induction'"
           [(Tactic.casesTarget [] `l)]
           []
           ["with" [(Lean.binderIdent `y) (Lean.binderIdent `l) (Lean.binderIdent `IH)]]
           [])
          []
          (tactic__ (cdotTk (patternIgnore (token.«· » "·"))) [(Tactic.simp "simp" [] [] [] [] [])])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Classical.«tacticBy_cases_:_» "by_cases" [`hx ":"] («term_=_» `x "=" `y))
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(Tactic.simp
               "simp"
               []
               []
               []
               ["["
                [(Tactic.simpLemma [] [] `hx)
                 ","
                 (Tactic.simpLemma [] [] `cons_sublist_cons_iff)
                 ","
                 (Tactic.simpLemma [] [] `singleton_sublist)]
                "]"]
               [])])
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(Tactic.rwSeq
               "rw"
               []
               (Tactic.rwRuleSeq
                "["
                [(Tactic.rwRule [] (Term.app `duplicate_cons_iff_of_ne [`hx]))
                 ","
                 (Tactic.rwRule [] `IH)]
                "]")
               [])
              []
              (Tactic.refine'
               "refine'"
               (Term.anonymousCtor
                "⟨"
                [(Term.app `sublist_cons_of_sublist [`y])
                 ","
                 (Term.fun "fun" (Term.basicFun [`h] [] "=>" (Term.hole "_")))]
                "⟩"))
              []
              (Tactic.cases "cases" [(Tactic.casesTarget [] `h)] [] [])
              []
              (tactic__
               (cdotTk (patternIgnore (token.«· » "·")))
               [(Tactic.assumption "assumption")])
              []
              (tactic__
               (cdotTk (patternIgnore (token.«· » "·")))
               [(Tactic.contradiction "contradiction")])])])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Classical.«tacticBy_cases_:_» "by_cases" [`hx ":"] («term_=_» `x "=" `y))
        []
        (tactic__
         (cdotTk (patternIgnore (token.«· » "·")))
         [(Tactic.simp
           "simp"
           []
           []
           []
           ["["
            [(Tactic.simpLemma [] [] `hx)
             ","
             (Tactic.simpLemma [] [] `cons_sublist_cons_iff)
             ","
             (Tactic.simpLemma [] [] `singleton_sublist)]
            "]"]
           [])])
        []
        (tactic__
         (cdotTk (patternIgnore (token.«· » "·")))
         [(Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] (Term.app `duplicate_cons_iff_of_ne [`hx]))
             ","
             (Tactic.rwRule [] `IH)]
            "]")
           [])
          []
          (Tactic.refine'
           "refine'"
           (Term.anonymousCtor
            "⟨"
            [(Term.app `sublist_cons_of_sublist [`y])
             ","
             (Term.fun "fun" (Term.basicFun [`h] [] "=>" (Term.hole "_")))]
            "⟩"))
          []
          (Tactic.cases "cases" [(Tactic.casesTarget [] `h)] [] [])
          []
          (tactic__ (cdotTk (patternIgnore (token.«· » "·"))) [(Tactic.assumption "assumption")])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.contradiction "contradiction")])])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule [] (Term.app `duplicate_cons_iff_of_ne [`hx])) "," (Tactic.rwRule [] `IH)]
          "]")
         [])
        []
        (Tactic.refine'
         "refine'"
         (Term.anonymousCtor
          "⟨"
          [(Term.app `sublist_cons_of_sublist [`y])
           ","
           (Term.fun "fun" (Term.basicFun [`h] [] "=>" (Term.hole "_")))]
          "⟩"))
        []
        (Tactic.cases "cases" [(Tactic.casesTarget [] `h)] [] [])
        []
        (tactic__ (cdotTk (patternIgnore (token.«· » "·"))) [(Tactic.assumption "assumption")])
        []
        (tactic__
         (cdotTk (patternIgnore (token.«· » "·")))
         [(Tactic.contradiction "contradiction")])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__ (cdotTk (patternIgnore (token.«· » "·"))) [(Tactic.contradiction "contradiction")])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.contradiction "contradiction")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__ (cdotTk (patternIgnore (token.«· » "·"))) [(Tactic.assumption "assumption")])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.assumption "assumption")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.cases "cases" [(Tactic.casesTarget [] `h)] [] [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine'
       "refine'"
       (Term.anonymousCtor
        "⟨"
        [(Term.app `sublist_cons_of_sublist [`y])
         ","
         (Term.fun "fun" (Term.basicFun [`h] [] "=>" (Term.hole "_")))]
        "⟩"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.app `sublist_cons_of_sublist [`y])
        ","
        (Term.fun "fun" (Term.basicFun [`h] [] "=>" (Term.hole "_")))]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun "fun" (Term.basicFun [`h] [] "=>" (Term.hole "_")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `sublist_cons_of_sublist [`y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `sublist_cons_of_sublist
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] (Term.app `duplicate_cons_iff_of_ne [`hx])) "," (Tactic.rwRule [] `IH)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `IH
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `duplicate_cons_iff_of_ne [`hx])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hx
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `duplicate_cons_iff_of_ne
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.simp
         "simp"
         []
         []
         []
         ["["
          [(Tactic.simpLemma [] [] `hx)
           ","
           (Tactic.simpLemma [] [] `cons_sublist_cons_iff)
           ","
           (Tactic.simpLemma [] [] `singleton_sublist)]
          "]"]
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       []
       ["["
        [(Tactic.simpLemma [] [] `hx)
         ","
         (Tactic.simpLemma [] [] `cons_sublist_cons_iff)
         ","
         (Tactic.simpLemma [] [] `singleton_sublist)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `singleton_sublist
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `cons_sublist_cons_iff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hx
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Classical.«tacticBy_cases_:_» "by_cases" [`hx ":"] («term_=_» `x "=" `y))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_» `x "=" `y)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__ (cdotTk (patternIgnore (token.«· » "·"))) [(Tactic.simp "simp" [] [] [] [] [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] [] [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.induction'
       "induction'"
       [(Tactic.casesTarget [] `l)]
       []
       ["with" [(Lean.binderIdent `y) (Lean.binderIdent `l) (Lean.binderIdent `IH)]]
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `l
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_↔_»
       (List.Data.List.Duplicate.«term_∈+_» `x " ∈+ " `l)
       "↔"
       (List.Init.Data.List.Lemmas.«term_<+_» («term[_]» "[" [`x "," `x] "]") " <+ " `l))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (List.Init.Data.List.Lemmas.«term_<+_» («term[_]» "[" [`x "," `x] "]") " <+ " `l)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `l
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      («term[_]» "[" [`x "," `x] "]")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 50 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 21 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 20, term))
      (List.Data.List.Duplicate.«term_∈+_» `x " ∈+ " `l)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'List.Data.List.Duplicate.«term_∈+_»', expected 'List.Data.List.Duplicate.term_∈+_._@.Data.List.Duplicate._hyg.8'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/-- The contrapositive of `list.nodup_iff_sublist`. -/
  theorem
    duplicate_iff_sublist
    : x ∈+ l ↔ [ x , x ] <+ l
    :=
      by
        induction' l with y l IH
          · simp
          ·
            by_cases hx : x = y
              · simp [ hx , cons_sublist_cons_iff , singleton_sublist ]
              ·
                rw [ duplicate_cons_iff_of_ne hx , IH ]
                  refine' ⟨ sublist_cons_of_sublist y , fun h => _ ⟩
                  cases h
                  · assumption
                  · contradiction
#align list.duplicate_iff_sublist List.duplicate_iff_sublist

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `nodup_iff_forall_not_duplicate [])
      (Command.declSig
       []
       (Term.typeSpec
        ":"
        («term_↔_»
         (Term.app `Nodup [`l])
         "↔"
         (Term.forall
          "∀"
          [`x]
          [(Term.typeSpec ":" `α)]
          ","
          («term¬_» "¬" (List.Data.List.Duplicate.«term_∈+_» `x " ∈+ " `l))))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Mathlib.Tactic.tacticSimp_rw__
            "simp_rw"
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [] `nodup_iff_sublist) "," (Tactic.rwRule [] `duplicate_iff_sublist)]
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
         [(Mathlib.Tactic.tacticSimp_rw__
           "simp_rw"
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `nodup_iff_sublist) "," (Tactic.rwRule [] `duplicate_iff_sublist)]
            "]")
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.tacticSimp_rw__
       "simp_rw"
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `nodup_iff_sublist) "," (Tactic.rwRule [] `duplicate_iff_sublist)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `duplicate_iff_sublist
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `nodup_iff_sublist
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_↔_»
       (Term.app `Nodup [`l])
       "↔"
       (Term.forall
        "∀"
        [`x]
        [(Term.typeSpec ":" `α)]
        ","
        («term¬_» "¬" (List.Data.List.Duplicate.«term_∈+_» `x " ∈+ " `l))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.forall
       "∀"
       [`x]
       [(Term.typeSpec ":" `α)]
       ","
       («term¬_» "¬" (List.Data.List.Duplicate.«term_∈+_» `x " ∈+ " `l)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term¬_» "¬" (List.Data.List.Duplicate.«term_∈+_» `x " ∈+ " `l))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (List.Data.List.Duplicate.«term_∈+_» `x " ∈+ " `l)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'List.Data.List.Duplicate.«term_∈+_»', expected 'List.Data.List.Duplicate.term_∈+_._@.Data.List.Duplicate._hyg.8'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  nodup_iff_forall_not_duplicate
  : Nodup l ↔ ∀ x : α , ¬ x ∈+ l
  := by simp_rw [ nodup_iff_sublist , duplicate_iff_sublist ]
#align list.nodup_iff_forall_not_duplicate List.nodup_iff_forall_not_duplicate

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `exists_duplicate_iff_not_nodup [])
      (Command.declSig
       []
       (Term.typeSpec
        ":"
        («term_↔_»
         («term∃_,_»
          "∃"
          (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] [":" `α]))
          ","
          (List.Data.List.Duplicate.«term_∈+_» `x " ∈+ " `l))
         "↔"
         («term¬_» "¬" (Term.app `Nodup [`l])))))
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
            []
            ["[" [(Tactic.simpLemma [] [] `nodup_iff_forall_not_duplicate)] "]"]
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
         [(Tactic.simp
           "simp"
           []
           []
           []
           ["[" [(Tactic.simpLemma [] [] `nodup_iff_forall_not_duplicate)] "]"]
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       []
       ["[" [(Tactic.simpLemma [] [] `nodup_iff_forall_not_duplicate)] "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `nodup_iff_forall_not_duplicate
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_↔_»
       («term∃_,_»
        "∃"
        (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] [":" `α]))
        ","
        (List.Data.List.Duplicate.«term_∈+_» `x " ∈+ " `l))
       "↔"
       («term¬_» "¬" (Term.app `Nodup [`l])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term¬_» "¬" (Term.app `Nodup [`l]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Nodup [`l])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `l
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Nodup
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 40 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 21 >? 1024, (some 40, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 20, term))
      («term∃_,_»
       "∃"
       (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] [":" `α]))
       ","
       (List.Data.List.Duplicate.«term_∈+_» `x " ∈+ " `l))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (List.Data.List.Duplicate.«term_∈+_» `x " ∈+ " `l)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'List.Data.List.Duplicate.«term_∈+_»', expected 'List.Data.List.Duplicate.term_∈+_._@.Data.List.Duplicate._hyg.8'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  exists_duplicate_iff_not_nodup
  : ∃ x : α , x ∈+ l ↔ ¬ Nodup l
  := by simp [ nodup_iff_forall_not_duplicate ]
#align list.exists_duplicate_iff_not_nodup List.exists_duplicate_iff_not_nodup

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `Duplicate.not_nodup [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`h]
         [":" (List.Data.List.Duplicate.«term_∈+_» `x " ∈+ " `l)]
         []
         ")")]
       (Term.typeSpec ":" («term¬_» "¬" (Term.app `Nodup [`l]))))
      (Command.declValSimple
       ":="
       (Term.fun
        "fun"
        (Term.basicFun
         [`H]
         []
         "=>"
         (Term.app (Term.proj `nodup_iff_forall_not_duplicate "." `mp) [`H (Term.hole "_") `h])))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`H]
        []
        "=>"
        (Term.app (Term.proj `nodup_iff_forall_not_duplicate "." `mp) [`H (Term.hole "_") `h])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj `nodup_iff_forall_not_duplicate "." `mp) [`H (Term.hole "_") `h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      `H
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `nodup_iff_forall_not_duplicate "." `mp)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `nodup_iff_forall_not_duplicate
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `H
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term¬_» "¬" (Term.app `Nodup [`l]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Nodup [`l])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `l
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Nodup
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 40 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 40,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (List.Data.List.Duplicate.«term_∈+_» `x " ∈+ " `l)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'List.Data.List.Duplicate.«term_∈+_»', expected 'List.Data.List.Duplicate.term_∈+_._@.Data.List.Duplicate._hyg.8'
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
  Duplicate.not_nodup
  ( h : x ∈+ l ) : ¬ Nodup l
  := fun H => nodup_iff_forall_not_duplicate . mp H _ h
#align list.duplicate.not_nodup List.Duplicate.not_nodup

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `duplicate_iff_two_le_count [])
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `DecidableEq [`α]) "]")]
       (Term.typeSpec
        ":"
        («term_↔_»
         (List.Data.List.Duplicate.«term_∈+_» `x " ∈+ " `l)
         "↔"
         («term_≤_» (num "2") "≤" (Term.app `count [`x `l])))))
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
            []
            ["["
             [(Tactic.simpLemma [] [] `duplicate_iff_sublist)
              ","
              (Tactic.simpLemma [] [] `le_count_iff_repeat_sublist)]
             "]"]
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
         [(Tactic.simp
           "simp"
           []
           []
           []
           ["["
            [(Tactic.simpLemma [] [] `duplicate_iff_sublist)
             ","
             (Tactic.simpLemma [] [] `le_count_iff_repeat_sublist)]
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
        [(Tactic.simpLemma [] [] `duplicate_iff_sublist)
         ","
         (Tactic.simpLemma [] [] `le_count_iff_repeat_sublist)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `le_count_iff_repeat_sublist
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `duplicate_iff_sublist
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_↔_»
       (List.Data.List.Duplicate.«term_∈+_» `x " ∈+ " `l)
       "↔"
       («term_≤_» (num "2") "≤" (Term.app `count [`x `l])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≤_» (num "2") "≤" (Term.app `count [`x `l]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `count [`x `l])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `l
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `count
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 21 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 20, term))
      (List.Data.List.Duplicate.«term_∈+_» `x " ∈+ " `l)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'List.Data.List.Duplicate.«term_∈+_»', expected 'List.Data.List.Duplicate.term_∈+_._@.Data.List.Duplicate._hyg.8'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  duplicate_iff_two_le_count
  [ DecidableEq α ] : x ∈+ l ↔ 2 ≤ count x l
  := by simp [ duplicate_iff_sublist , le_count_iff_repeat_sublist ]
#align list.duplicate_iff_two_le_count List.duplicate_iff_two_le_count

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.instance
      (Term.attrKind [])
      "instance"
      []
      [(Command.declId `decidableDuplicate [])]
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `DecidableEq [`α]) "]")
        (Term.explicitBinder "(" [`x] [":" `α] [] ")")]
       (Term.typeSpec
        ":"
        (Term.forall
         "∀"
         [`l]
         [(Term.typeSpec ":" (Term.app `List [`α]))]
         ","
         (Term.app `Decidable [(List.Data.List.Duplicate.«term_∈+_» `x " ∈+ " `l)]))))
      (Command.declValEqns
       (Term.matchAltsWhereDecls
        (Term.matchAlts
         [(Term.matchAlt
           "|"
           [[(«term[_]» "[" [] "]")]]
           "=>"
           (Term.app `isFalse [(Term.app `not_duplicate_nil [`x])]))
          (Term.matchAlt
           "|"
           [[(«term_::_» `y "::" `l)]]
           "=>"
           (Term.match
            "match"
            []
            []
            [(Term.matchDiscr [] (Term.app `decidable_duplicate [`l]))]
            "with"
            (Term.matchAlts
             [(Term.matchAlt
               "|"
               [[(Term.app `is_true [`h])]]
               "=>"
               (Term.app `isTrue [(Term.app (Term.proj `h "." `duplicate_cons) [`y])]))
              (Term.matchAlt
               "|"
               [[(Term.app `is_false [`h])]]
               "=>"
               (termDepIfThenElse
                "if"
                (Lean.binderIdent `hx)
                ":"
                («term_∧_» («term_=_» `y "=" `x) "∧" («term_∈_» `x "∈" `l))
                "then"
                (Term.app
                 `isTrue
                 [(Term.subst
                   (Term.proj (Term.proj `hx "." `left) "." `symm)
                   "▸"
                   [(Term.proj (Term.proj `hx "." `right) "." `duplicate_cons_self)])])
                "else"
                (Term.app
                 `isFalse
                 [(Term.byTactic
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
                          [(Tactic.simpLemma [] [] `duplicate_cons_iff)
                           ","
                           (Tactic.simpLemma [] [] `h)]
                          "]")]
                        ["using" `hx]))])))])))])))])
        []))
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValEqns', expected 'Lean.Parser.Command.declValSimple'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.match
       "match"
       []
       []
       [(Term.matchDiscr [] (Term.app `decidable_duplicate [`l]))]
       "with"
       (Term.matchAlts
        [(Term.matchAlt
          "|"
          [[(Term.app `is_true [`h])]]
          "=>"
          (Term.app `isTrue [(Term.app (Term.proj `h "." `duplicate_cons) [`y])]))
         (Term.matchAlt
          "|"
          [[(Term.app `is_false [`h])]]
          "=>"
          (termDepIfThenElse
           "if"
           (Lean.binderIdent `hx)
           ":"
           («term_∧_» («term_=_» `y "=" `x) "∧" («term_∈_» `x "∈" `l))
           "then"
           (Term.app
            `isTrue
            [(Term.subst
              (Term.proj (Term.proj `hx "." `left) "." `symm)
              "▸"
              [(Term.proj (Term.proj `hx "." `right) "." `duplicate_cons_self)])])
           "else"
           (Term.app
            `isFalse
            [(Term.byTactic
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
                     [(Tactic.simpLemma [] [] `duplicate_cons_iff) "," (Tactic.simpLemma [] [] `h)]
                     "]")]
                   ["using" `hx]))])))])))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (termDepIfThenElse
       "if"
       (Lean.binderIdent `hx)
       ":"
       («term_∧_» («term_=_» `y "=" `x) "∧" («term_∈_» `x "∈" `l))
       "then"
       (Term.app
        `isTrue
        [(Term.subst
          (Term.proj (Term.proj `hx "." `left) "." `symm)
          "▸"
          [(Term.proj (Term.proj `hx "." `right) "." `duplicate_cons_self)])])
       "else"
       (Term.app
        `isFalse
        [(Term.byTactic
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
                 [(Tactic.simpLemma [] [] `duplicate_cons_iff) "," (Tactic.simpLemma [] [] `h)]
                 "]")]
               ["using" `hx]))])))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `isFalse
       [(Term.byTactic
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
                [(Tactic.simpLemma [] [] `duplicate_cons_iff) "," (Tactic.simpLemma [] [] `h)]
                "]")]
              ["using" `hx]))])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.ellipsis'
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
              [(Tactic.simpLemma [] [] `duplicate_cons_iff) "," (Tactic.simpLemma [] [] `h)]
              "]")]
            ["using" `hx]))])))
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
          [(Tactic.simpLemma [] [] `duplicate_cons_iff) "," (Tactic.simpLemma [] [] `h)]
          "]")]
        ["using" `hx]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hx
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `duplicate_cons_iff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
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
             [(Tactic.simpLemma [] [] `duplicate_cons_iff) "," (Tactic.simpLemma [] [] `h)]
             "]")]
           ["using" `hx]))])))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `isFalse
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `isTrue
       [(Term.subst
         (Term.proj (Term.proj `hx "." `left) "." `symm)
         "▸"
         [(Term.proj (Term.proj `hx "." `right) "." `duplicate_cons_self)])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.subst', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.subst', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.subst
       (Term.proj (Term.proj `hx "." `left) "." `symm)
       "▸"
       [(Term.proj (Term.proj `hx "." `right) "." `duplicate_cons_self)])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.proj `hx "." `right) "." `duplicate_cons_self)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj `hx "." `right)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hx
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 75 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 75, term))
      (Term.proj (Term.proj `hx "." `left) "." `symm)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj `hx "." `left)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hx
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 75, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 75, (some 75, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.subst
      (Term.proj (Term.proj `hx "." `left) "." `symm)
      "▸"
      [(Term.proj (Term.proj `hx "." `right) "." `duplicate_cons_self)])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `isTrue
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∧_» («term_=_» `y "=" `x) "∧" («term_∈_» `x "∈" `l))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∈_» `x "∈" `l)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `l
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 35 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 35, term))
      («term_=_» `y "=" `x)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `y
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 36 >? 50, (some 51, term) <=? (some 35, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 35, (some 35, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `is_false [`h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `is_false
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app `isTrue [(Term.app (Term.proj `h "." `duplicate_cons) [`y])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj `h "." `duplicate_cons) [`y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `h "." `duplicate_cons)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `h
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.proj `h "." `duplicate_cons) [`y])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `isTrue
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `is_true [`h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `is_true
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `decidable_duplicate [`l])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `l
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `decidable_duplicate
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_::_» `y "::" `l)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `l
[PrettyPrinter.parenthesize] ...precedences are 67 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 67, term))
      `y
[PrettyPrinter.parenthesize] ...precedences are 68 >? 1024, (none, [anonymous]) <=? (some 67, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 67, (some 67, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app `isFalse [(Term.app `not_duplicate_nil [`x])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `not_duplicate_nil [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `not_duplicate_nil
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `not_duplicate_nil [`x]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `isFalse
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term[_]» "[" [] "]")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.forall
       "∀"
       [`l]
       [(Term.typeSpec ":" (Term.app `List [`α]))]
       ","
       (Term.app `Decidable [(List.Data.List.Duplicate.«term_∈+_» `x " ∈+ " `l)]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Decidable [(List.Data.List.Duplicate.«term_∈+_» `x " ∈+ " `l)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'List.Data.List.Duplicate.«term_∈+_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'List.Data.List.Duplicate.«term_∈+_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (List.Data.List.Duplicate.«term_∈+_» `x " ∈+ " `l)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'List.Data.List.Duplicate.«term_∈+_»', expected 'List.Data.List.Duplicate.term_∈+_._@.Data.List.Duplicate._hyg.8'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
instance
  decidableDuplicate
  [ DecidableEq α ] ( x : α ) : ∀ l : List α , Decidable x ∈+ l
  | [ ] => isFalse not_duplicate_nil x
    |
      y :: l
      =>
      match
        decidable_duplicate l
        with
        | is_true h => isTrue h . duplicate_cons y
          |
            is_false h
            =>
            if
              hx
              :
              y = x ∧ x ∈ l
              then
              isTrue hx . left . symm ▸ hx . right . duplicate_cons_self
              else
              isFalse by simpa [ duplicate_cons_iff , h ] using hx
#align list.decidable_duplicate List.decidableDuplicate

end List

