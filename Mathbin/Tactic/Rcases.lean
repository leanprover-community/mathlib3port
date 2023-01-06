/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

! This file was ported from Lean 3 source module tactic.rcases
! leanprover-community/mathlib commit 18a5306c091183ac90884daa9373fa3b178e8607
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Leanbin.Data.Dlist
import Mathbin.Tactic.Core
import Mathbin.Tactic.Clear

/-!

# Recursive cases (`rcases`) tactic and related tactics

`rcases` is a tactic that will perform `cases` recursively, according to a pattern. It is used to
destructure hypotheses or expressions composed of inductive types like `h1 : a ∧ b ∧ c ∨ d` or
`h2 : ∃ x y, trans_rel R x y`. Usual usage might be `rcases h1 with ⟨ha, hb, hc⟩ | hd` or
`rcases h2 with ⟨x, y, _ | ⟨z, hxz, hzy⟩⟩` for these examples.

Each element of an `rcases` pattern is matched against a particular local hypothesis (most of which
are generated during the execution of `rcases` and represent individual elements destructured from
the input expression). An `rcases` pattern has the following grammar:

* A name like `x`, which names the active hypothesis as `x`.
* A blank `_`, which does nothing (letting the automatic naming system used by `cases` name the
  hypothesis).
* A hyphen `-`, which clears the active hypothesis and any dependents.
* The keyword `rfl`, which expects the hypothesis to be `h : a = b`, and calls `subst` on the
  hypothesis (which has the effect of replacing `b` with `a` everywhere or vice versa).
* A type ascription `p : ty`, which sets the type of the hypothesis to `ty` and then matches it
  against `p`. (Of course, `ty` must unify with the actual type of `h` for this to work.)
* A tuple pattern `⟨p1, p2, p3⟩`, which matches a constructor with many arguments, or a series
  of nested conjunctions or existentials. For example if the active hypothesis is `a ∧ b ∧ c`,
  then the conjunction will be destructured, and `p1` will be matched against `a`, `p2` against `b`
  and so on.
* A `@` before a tuple pattern as in `@⟨p1, p2, p3⟩` will bind all arguments in the constructor,
  while leaving the `@` off will only use the patterns on the explicit arguments.
* An alteration pattern `p1 | p2 | p3`, which matches an inductive type with multiple constructors,
  or a nested disjunction like `a ∨ b ∨ c`.

The patterns are fairly liberal about the exact shape of the constructors, and will insert
additional alternation branches and tuple arguments if there are not enough arguments provided, and
reuse the tail for further matches if there are too many arguments provided to alternation and
tuple patterns.

This file also contains the `obtain` and `rintro` tactics, which use the same syntax of `rcases`
patterns but with a slightly different use case:

* `rintro` (or `rintros`) is used like `rintro x ⟨y, z⟩` and is the same as `intros` followed by
  `rcases` on the newly introduced arguments.
* `obtain` is the same as `rcases` but with a syntax styled after `have` rather than `cases`.
  `obtain ⟨hx, hy⟩ | hz := foo` is equivalent to `rcases foo with ⟨hx, hy⟩ | hz`. Unlike `rcases`,
  `obtain` also allows one to omit `:= foo`, although a type must be provided in this case,
  as in `obtain ⟨hx, hy⟩ | hz : a ∧ b ∨ c`, in which case it produces a subgoal for proving
  `a ∧ b ∨ c` in addition to the subgoals `hx : a, hy : b |- goal` and `hz : c |- goal`.

## Tags

rcases, rintro, obtain, destructuring, cases, pattern matching, match
-/


open Lean Lean.Parser

namespace Tactic

/-!
These synonyms for `list` are used to clarify the meanings of the many
usages of lists in this module.

- `listΣ` is used where a list represents a disjunction, such as the
  list of possible constructors of an inductive type.

- `listΠ` is used where a list represents a conjunction, such as the
  list of arguments of an individual constructor.

These are merely type synonyms, and so are not checked for consistency
by the compiler.

The `def`/`local notation` combination makes Lean retain these
annotations in reported types.
-/


/-- A list, with a disjunctive meaning (like a list of inductive constructors, or subgoals) -/
@[reducible]
def ListSigma :=
  List
#align tactic.list_Sigma Tactic.ListSigma

/-- A list, with a conjunctive meaning (like a list of constructor arguments, or hypotheses) -/
@[reducible]
def ListPi :=
  List
#align tactic.list_Pi Tactic.ListPi

-- mathport name: «exprlistΣ»
local notation "listΣ" => ListSigma

-- mathport name: «exprlistΠ»
local notation "listΠ" => ListPi

/-- A metavariable representing a subgoal, together with a list of local constants to clear. -/
@[reducible]
unsafe def uncleared_goal :=
  List expr × expr
#align tactic.uncleared_goal tactic.uncleared_goal

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "An `rcases` pattern can be one of the following, in a nested combination:\n\n* A name like `foo`\n* The special keyword `rfl` (for pattern matching on equality using `subst`)\n* A hyphen `-`, which clears the active hypothesis and any dependents.\n* A type ascription like `pat : ty` (parentheses are optional)\n* A tuple constructor like `⟨p1, p2, p3⟩`\n* An alternation / variant pattern `p1 | p2 | p3`\n\nParentheses can be used for grouping; alternation is higher precedence than type ascription, so\n`p1 | p2 | p3 : ty` means `(p1 | p2 | p3) : ty`.\n\nN-ary alternations are treated as a group, so `p1 | p2 | p3` is not the same as `p1 | (p2 | p3)`,\nand similarly for tuples. However, note that an n-ary alternation or tuple can match an n-ary\nconjunction or disjunction, because if the number of patterns exceeds the number of constructors in\nthe type being destructed, the extra patterns will match on the last element, meaning that\n`p1 | p2 | p3` will act like `p1 | (p2 | p3)` when matching `a1 ∨ a2 ∨ a3`. If matching against a\ntype with 3 constructors,  `p1 | (p2 | p3)` will act like `p1 | (p2 | p3) | _` instead.\n-/")]
      []
      []
      []
      [(Command.unsafe "unsafe")]
      [])
     (Command.inductive
      "inductive"
      (Command.declId `rcases_patt [])
      (Command.optDeclSig [] [(Term.typeSpec ":" (Term.type "Type" []))])
      []
      [(Command.ctor
        []
        "|"
        (Command.declModifiers [] [] [] [] [] [])
        `one
        (Command.optDeclSig [] [(Term.typeSpec ":" (Term.arrow `Name "→" `rcases_patt))]))
       (Command.ctor
        []
        "|"
        (Command.declModifiers [] [] [] [] [] [])
        `clear
        (Command.optDeclSig [] [(Term.typeSpec ":" `rcases_patt)]))
       (Command.ctor
        []
        "|"
        (Command.declModifiers [] [] [] [] [] [])
        `explicit
        (Command.optDeclSig [] [(Term.typeSpec ":" (Term.arrow `rcases_patt "→" `rcases_patt))]))
       (Command.ctor
        []
        "|"
        (Command.declModifiers [] [] [] [] [] [])
        `typed
        (Command.optDeclSig
         []
         [(Term.typeSpec ":" (Term.arrow `rcases_patt "→" (Term.arrow `pexpr "→" `rcases_patt)))]))
       (Command.ctor
        []
        "|"
        (Command.declModifiers [] [] [] [] [] [])
        `tuple
        (Command.optDeclSig
         []
         [(Term.typeSpec
           ":"
           (Term.arrow
            (Term.app (Tactic.Tactic.Rcases.«termlistΠ» "listΠ") [`rcases_patt])
            "→"
            `rcases_patt))]))
       (Command.ctor
        []
        "|"
        (Command.declModifiers [] [] [] [] [] [])
        `alts
        (Command.optDeclSig
         []
         [(Term.typeSpec
           ":"
           (Term.arrow
            (Term.app (Tactic.Tactic.Rcases.«termlistΣ» "listΣ") [`rcases_patt])
            "→"
            `rcases_patt))]))]
      []
      (Command.optDeriving [])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.inductive', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.inductive', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.inductive', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.inductive', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.inductive', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.inductive', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.inductive', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.arrow
       (Term.app (Tactic.Tactic.Rcases.«termlistΣ» "listΣ") [`rcases_patt])
       "→"
       `rcases_patt)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rcases_patt
[PrettyPrinter.parenthesize] ...precedences are 25 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
      (Term.app (Tactic.Tactic.Rcases.«termlistΣ» "listΣ") [`rcases_patt])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rcases_patt
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Tactic.Tactic.Rcases.«termlistΣ» "listΣ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Tactic.Tactic.Rcases.«termlistΣ»', expected 'Tactic.Tactic.Rcases.termlistΣ._@.Tactic.Rcases._hyg.7'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.inductive', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.inductive', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
      An `rcases` pattern can be one of the following, in a nested combination:
      
      * A name like `foo`
      * The special keyword `rfl` (for pattern matching on equality using `subst`)
      * A hyphen `-`, which clears the active hypothesis and any dependents.
      * A type ascription like `pat : ty` (parentheses are optional)
      * A tuple constructor like `⟨p1, p2, p3⟩`
      * An alternation / variant pattern `p1 | p2 | p3`
      
      Parentheses can be used for grouping; alternation is higher precedence than type ascription, so
      `p1 | p2 | p3 : ty` means `(p1 | p2 | p3) : ty`.
      
      N-ary alternations are treated as a group, so `p1 | p2 | p3` is not the same as `p1 | (p2 | p3)`,
      and similarly for tuples. However, note that an n-ary alternation or tuple can match an n-ary
      conjunction or disjunction, because if the number of patterns exceeds the number of constructors in
      the type being destructed, the extra patterns will match on the last element, meaning that
      `p1 | p2 | p3` will act like `p1 | (p2 | p3)` when matching `a1 ∨ a2 ∨ a3`. If matching against a
      type with 3 constructors,  `p1 | (p2 | p3)` will act like `p1 | (p2 | p3) | _` instead.
      -/
    unsafe
  inductive
    rcases_patt
    : Type
    | one : Name → rcases_patt
      | clear : rcases_patt
      | explicit : rcases_patt → rcases_patt
      | typed : rcases_patt → pexpr → rcases_patt
      | tuple : listΠ rcases_patt → rcases_patt
      | alts : listΣ rcases_patt → rcases_patt
#align tactic.rcases_patt tactic.rcases_patt

namespace RcasesPatt

unsafe instance inhabited : Inhabited rcases_patt :=
  ⟨one `_⟩
#align tactic.rcases_patt.inhabited tactic.rcases_patt.inhabited

/-- Get the name from a pattern, if provided -/
unsafe def name : rcases_patt → Option Name
  | one `_ => none
  | one `rfl => none
  | one n => some n
  | explicit p => p.Name
  | typed p _ => p.Name
  | alts [p] => p.Name
  | _ => none
#align tactic.rcases_patt.name tactic.rcases_patt.name

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "Interpret an rcases pattern as a tuple, where `p` becomes `⟨p⟩`\nif `p` is not already a tuple. -/")]
      []
      []
      []
      [(Command.unsafe "unsafe")]
      [])
     (Command.def
      "def"
      (Command.declId `as_tuple [])
      (Command.optDeclSig
       []
       [(Term.typeSpec
         ":"
         (Term.arrow
          `rcases_patt
          "→"
          («term_×_»
           `Bool
           "×"
           (Term.app (Tactic.Tactic.Rcases.«termlistΠ» "listΠ") [`rcases_patt]))))])
      (Command.declValEqns
       (Term.matchAltsWhereDecls
        (Term.matchAlts
         [(Term.matchAlt
           "|"
           [[(Term.app `explicit [`p])]]
           "=>"
           (Term.tuple
            "("
            [`true "," [(Term.proj (Term.app `as_tuple [`p]) "." (fieldIdx "2"))]]
            ")"))
          (Term.matchAlt
           "|"
           [[(Term.app `tuple [`ps])]]
           "=>"
           (Term.tuple "(" [`false "," [`ps]] ")"))
          (Term.matchAlt
           "|"
           [[`p]]
           "=>"
           (Term.tuple "(" [`false "," [(«term[_]» "[" [`p] "]")]] ")"))])
        []))
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValEqns', expected 'Lean.Parser.Command.declValSimple'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.tuple "(" [`false "," [(«term[_]» "[" [`p] "]")]] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term[_]» "[" [`p] "]")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `false
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.tuple "(" [`false "," [`ps]] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ps
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `false
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `tuple [`ps])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ps
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `tuple
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.tuple "(" [`true "," [(Term.proj (Term.app `as_tuple [`p]) "." (fieldIdx "2"))]] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.app `as_tuple [`p]) "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `as_tuple [`p])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `as_tuple
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `as_tuple [`p]) ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `true
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `explicit [`p])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `explicit
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.arrow
       `rcases_patt
       "→"
       («term_×_» `Bool "×" (Term.app (Tactic.Tactic.Rcases.«termlistΠ» "listΠ") [`rcases_patt])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_×_» `Bool "×" (Term.app (Tactic.Tactic.Rcases.«termlistΠ» "listΠ") [`rcases_patt]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Tactic.Tactic.Rcases.«termlistΠ» "listΠ") [`rcases_patt])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rcases_patt
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Tactic.Tactic.Rcases.«termlistΠ» "listΠ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Tactic.Tactic.Rcases.«termlistΠ»', expected 'Tactic.Tactic.Rcases.termlistΠ._@.Tactic.Rcases._hyg.324'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
      Interpret an rcases pattern as a tuple, where `p` becomes `⟨p⟩`
      if `p` is not already a tuple. -/
    unsafe
  def
    as_tuple
    : rcases_patt → Bool × listΠ rcases_patt
    | explicit p => ( true , as_tuple p . 2 ) | tuple ps => ( false , ps ) | p => ( false , [ p ] )
#align tactic.rcases_patt.as_tuple tactic.rcases_patt.as_tuple

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "Interpret an rcases pattern as an alternation, where non-alternations are treated as one\nalternative. -/")]
      []
      []
      []
      [(Command.unsafe "unsafe")]
      [])
     (Command.def
      "def"
      (Command.declId `as_alts [])
      (Command.optDeclSig
       []
       [(Term.typeSpec
         ":"
         (Term.arrow
          `rcases_patt
          "→"
          (Term.app (Tactic.Tactic.Rcases.«termlistΣ» "listΣ") [`rcases_patt])))])
      (Command.declValEqns
       (Term.matchAltsWhereDecls
        (Term.matchAlts
         [(Term.matchAlt "|" [[(Term.app `alts [`ps])]] "=>" `ps)
          (Term.matchAlt "|" [[`p]] "=>" («term[_]» "[" [`p] "]"))])
        []))
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValEqns', expected 'Lean.Parser.Command.declValSimple'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term[_]» "[" [`p] "]")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      `ps
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `alts [`ps])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ps
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `alts
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.arrow
       `rcases_patt
       "→"
       (Term.app (Tactic.Tactic.Rcases.«termlistΣ» "listΣ") [`rcases_patt]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Tactic.Tactic.Rcases.«termlistΣ» "listΣ") [`rcases_patt])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rcases_patt
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Tactic.Tactic.Rcases.«termlistΣ» "listΣ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Tactic.Tactic.Rcases.«termlistΣ»', expected 'Tactic.Tactic.Rcases.termlistΣ._@.Tactic.Rcases._hyg.7'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
      Interpret an rcases pattern as an alternation, where non-alternations are treated as one
      alternative. -/
    unsafe
  def as_alts : rcases_patt → listΣ rcases_patt | alts ps => ps | p => [ p ]
#align tactic.rcases_patt.as_alts tactic.rcases_patt.as_alts

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "Convert a list of patterns to a tuple pattern, but mapping `[p]` to `p` instead of `⟨p⟩`. -/")]
      []
      []
      []
      [(Command.unsafe "unsafe")]
      [])
     (Command.def
      "def"
      (Command.declId `tuple' [])
      (Command.optDeclSig
       []
       [(Term.typeSpec
         ":"
         (Term.arrow
          (Term.app (Tactic.Tactic.Rcases.«termlistΠ» "listΠ") [`rcases_patt])
          "→"
          `rcases_patt))])
      (Command.declValEqns
       (Term.matchAltsWhereDecls
        (Term.matchAlts
         [(Term.matchAlt "|" [[(«term[_]» "[" [`p] "]")]] "=>" `p)
          (Term.matchAlt "|" [[`ps]] "=>" (Term.app `tuple [`ps]))])
        []))
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValEqns', expected 'Lean.Parser.Command.declValSimple'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `tuple [`ps])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ps
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `tuple
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ps
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      `p
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term[_]» "[" [`p] "]")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.arrow
       (Term.app (Tactic.Tactic.Rcases.«termlistΠ» "listΠ") [`rcases_patt])
       "→"
       `rcases_patt)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rcases_patt
[PrettyPrinter.parenthesize] ...precedences are 25 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
      (Term.app (Tactic.Tactic.Rcases.«termlistΠ» "listΠ") [`rcases_patt])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rcases_patt
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Tactic.Tactic.Rcases.«termlistΠ» "listΠ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Tactic.Tactic.Rcases.«termlistΠ»', expected 'Tactic.Tactic.Rcases.termlistΠ._@.Tactic.Rcases._hyg.324'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/-- Convert a list of patterns to a tuple pattern, but mapping `[p]` to `p` instead of `⟨p⟩`. -/
    unsafe
  def tuple' : listΠ rcases_patt → rcases_patt | [ p ] => p | ps => tuple ps
#align tactic.rcases_patt.tuple' tactic.rcases_patt.tuple'

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "Convert a list of patterns to an alternation pattern, but mapping `[p]` to `p` instead of\na unary alternation `|p`. -/")]
      []
      []
      []
      [(Command.unsafe "unsafe")]
      [])
     (Command.def
      "def"
      (Command.declId `alts' [])
      (Command.optDeclSig
       []
       [(Term.typeSpec
         ":"
         (Term.arrow
          (Term.app (Tactic.Tactic.Rcases.«termlistΣ» "listΣ") [`rcases_patt])
          "→"
          `rcases_patt))])
      (Command.declValEqns
       (Term.matchAltsWhereDecls
        (Term.matchAlts
         [(Term.matchAlt "|" [[(«term[_]» "[" [`p] "]")]] "=>" `p)
          (Term.matchAlt "|" [[`ps]] "=>" (Term.app `alts [`ps]))])
        []))
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValEqns', expected 'Lean.Parser.Command.declValSimple'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `alts [`ps])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ps
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `alts
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ps
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      `p
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term[_]» "[" [`p] "]")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.arrow
       (Term.app (Tactic.Tactic.Rcases.«termlistΣ» "listΣ") [`rcases_patt])
       "→"
       `rcases_patt)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rcases_patt
[PrettyPrinter.parenthesize] ...precedences are 25 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
      (Term.app (Tactic.Tactic.Rcases.«termlistΣ» "listΣ") [`rcases_patt])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rcases_patt
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Tactic.Tactic.Rcases.«termlistΣ» "listΣ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Tactic.Tactic.Rcases.«termlistΣ»', expected 'Tactic.Tactic.Rcases.termlistΣ._@.Tactic.Rcases._hyg.7'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
      Convert a list of patterns to an alternation pattern, but mapping `[p]` to `p` instead of
      a unary alternation `|p`. -/
    unsafe
  def alts' : listΣ rcases_patt → rcases_patt | [ p ] => p | ps => alts ps
#align tactic.rcases_patt.alts' tactic.rcases_patt.alts'

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "This function is used for producing rcases patterns based on a case tree. Suppose that we have\na list of patterns `ps` that will match correctly against the branches of the case tree for one\nconstructor. This function will merge tuples at the end of the list, so that `[a, b, ⟨c, d⟩]`\nbecomes `⟨a, b, c, d⟩` instead of `⟨a, b, ⟨c, d⟩⟩`.\n\nWe must be careful to turn `[a, ⟨⟩]` into `⟨a, ⟨⟩⟩` instead of `⟨a⟩` (which will not perform the\nnested match). -/")]
      []
      []
      []
      [(Command.unsafe "unsafe")]
      [])
     (Command.def
      "def"
      (Command.declId `tuple₁_core [])
      (Command.optDeclSig
       []
       [(Term.typeSpec
         ":"
         (Term.arrow
          (Term.app (Tactic.Tactic.Rcases.«termlistΠ» "listΠ") [`rcases_patt])
          "→"
          (Term.app (Tactic.Tactic.Rcases.«termlistΠ» "listΠ") [`rcases_patt])))])
      (Command.declValEqns
       (Term.matchAltsWhereDecls
        (Term.matchAlts
         [(Term.matchAlt "|" [[(«term[_]» "[" [] "]")]] "=>" («term[_]» "[" [] "]"))
          (Term.matchAlt
           "|"
           [[(«term[_]» "[" [(Term.app `tuple [(«term[_]» "[" [] "]")])] "]")]]
           "=>"
           («term[_]» "[" [(Term.app `tuple [(«term[_]» "[" [] "]")])] "]"))
          (Term.matchAlt "|" [[(«term[_]» "[" [(Term.app `tuple [`ps])] "]")]] "=>" `ps)
          (Term.matchAlt
           "|"
           [[(«term_::_» `p "::" `ps)]]
           "=>"
           («term_::_» `p "::" (Term.app `tuple₁_core [`ps])))])
        []))
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValEqns', expected 'Lean.Parser.Command.declValSimple'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_::_» `p "::" (Term.app `tuple₁_core [`ps]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `tuple₁_core [`ps])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ps
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `tuple₁_core
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 67 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 67, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 68 >? 1024, (none, [anonymous]) <=? (some 67, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 67, (some 67, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_::_» `p "::" `ps)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ps
[PrettyPrinter.parenthesize] ...precedences are 67 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 67, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 68 >? 1024, (none, [anonymous]) <=? (some 67, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 67, (some 67, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      `ps
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term[_]» "[" [(Term.app `tuple [`ps])] "]")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `tuple [`ps])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ps
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `tuple
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term[_]» "[" [(Term.app `tuple [(«term[_]» "[" [] "]")])] "]")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `tuple [(«term[_]» "[" [] "]")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term[_]»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term[_]»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term[_]» "[" [] "]")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `tuple
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term[_]» "[" [(Term.app `tuple [(«term[_]» "[" [] "]")])] "]")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `tuple [(«term[_]» "[" [] "]")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term[_]»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term[_]»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term[_]» "[" [] "]")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `tuple
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term[_]» "[" [] "]")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term[_]» "[" [] "]")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.arrow
       (Term.app (Tactic.Tactic.Rcases.«termlistΠ» "listΠ") [`rcases_patt])
       "→"
       (Term.app (Tactic.Tactic.Rcases.«termlistΠ» "listΠ") [`rcases_patt]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Tactic.Tactic.Rcases.«termlistΠ» "listΠ") [`rcases_patt])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rcases_patt
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Tactic.Tactic.Rcases.«termlistΠ» "listΠ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Tactic.Tactic.Rcases.«termlistΠ»', expected 'Tactic.Tactic.Rcases.termlistΠ._@.Tactic.Rcases._hyg.324'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
      This function is used for producing rcases patterns based on a case tree. Suppose that we have
      a list of patterns `ps` that will match correctly against the branches of the case tree for one
      constructor. This function will merge tuples at the end of the list, so that `[a, b, ⟨c, d⟩]`
      becomes `⟨a, b, c, d⟩` instead of `⟨a, b, ⟨c, d⟩⟩`.
      
      We must be careful to turn `[a, ⟨⟩]` into `⟨a, ⟨⟩⟩` instead of `⟨a⟩` (which will not perform the
      nested match). -/
    unsafe
  def
    tuple₁_core
    : listΠ rcases_patt → listΠ rcases_patt
    | [ ] => [ ]
      | [ tuple [ ] ] => [ tuple [ ] ]
      | [ tuple ps ] => ps
      | p :: ps => p :: tuple₁_core ps
#align tactic.rcases_patt.tuple₁_core tactic.rcases_patt.tuple₁_core

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "This function is used for producing rcases patterns based on a case tree. This is like\n`tuple₁_core` but it produces a pattern instead of a tuple pattern list, converting `[n]` to `n`\ninstead of `⟨n⟩` and `[]` to `_`, and otherwise just converting `[a, b, c]` to `⟨a, b, c⟩`. -/")]
      []
      []
      []
      [(Command.unsafe "unsafe")]
      [])
     (Command.def
      "def"
      (Command.declId `tuple₁ [])
      (Command.optDeclSig
       []
       [(Term.typeSpec
         ":"
         (Term.arrow
          (Term.app (Tactic.Tactic.Rcases.«termlistΠ» "listΠ") [`rcases_patt])
          "→"
          `rcases_patt))])
      (Command.declValEqns
       (Term.matchAltsWhereDecls
        (Term.matchAlts
         [(Term.matchAlt "|" [[(«term[_]» "[" [] "]")]] "=>" `default)
          (Term.matchAlt
           "|"
           [[(«term[_]» "[" [(Term.app `one [`n])] "]")]]
           "=>"
           (Term.app `one [`n]))
          (Term.matchAlt "|" [[`ps]] "=>" (Term.app `tuple [(Term.app `tuple₁_core [`ps])]))])
        []))
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValEqns', expected 'Lean.Parser.Command.declValSimple'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `tuple [(Term.app `tuple₁_core [`ps])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `tuple₁_core [`ps])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ps
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `tuple₁_core
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `tuple₁_core [`ps]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `tuple
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ps
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app `one [`n])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `one
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term[_]» "[" [(Term.app `one [`n])] "]")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `one [`n])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `one
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      `default
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term[_]» "[" [] "]")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.arrow
       (Term.app (Tactic.Tactic.Rcases.«termlistΠ» "listΠ") [`rcases_patt])
       "→"
       `rcases_patt)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rcases_patt
[PrettyPrinter.parenthesize] ...precedences are 25 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
      (Term.app (Tactic.Tactic.Rcases.«termlistΠ» "listΠ") [`rcases_patt])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rcases_patt
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Tactic.Tactic.Rcases.«termlistΠ» "listΠ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Tactic.Tactic.Rcases.«termlistΠ»', expected 'Tactic.Tactic.Rcases.termlistΠ._@.Tactic.Rcases._hyg.324'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
      This function is used for producing rcases patterns based on a case tree. This is like
      `tuple₁_core` but it produces a pattern instead of a tuple pattern list, converting `[n]` to `n`
      instead of `⟨n⟩` and `[]` to `_`, and otherwise just converting `[a, b, c]` to `⟨a, b, c⟩`. -/
    unsafe
  def
    tuple₁
    : listΠ rcases_patt → rcases_patt
    | [ ] => default | [ one n ] => one n | ps => tuple tuple₁_core ps
#align tactic.rcases_patt.tuple₁ tactic.rcases_patt.tuple₁

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "This function is used for producing rcases patterns based on a case tree. Here we are given\nthe list of patterns to apply to each argument of each constructor after the main case, and must\nproduce a list of alternatives with the same effect. This function calls `tuple₁` to make the\nindividual alternatives, and handles merging `[a, b, c | d]` to `a | b | c | d` instead of\n`a | b | (c | d)`. -/")]
      []
      []
      []
      [(Command.unsafe "unsafe")]
      [])
     (Command.def
      "def"
      (Command.declId `alts₁_core [])
      (Command.optDeclSig
       []
       [(Term.typeSpec
         ":"
         (Term.arrow
          (Term.app
           (Tactic.Tactic.Rcases.«termlistΣ» "listΣ")
           [(Term.app (Tactic.Tactic.Rcases.«termlistΠ» "listΠ") [`rcases_patt])])
          "→"
          (Term.app (Tactic.Tactic.Rcases.«termlistΣ» "listΣ") [`rcases_patt])))])
      (Command.declValEqns
       (Term.matchAltsWhereDecls
        (Term.matchAlts
         [(Term.matchAlt "|" [[(«term[_]» "[" [] "]")]] "=>" («term[_]» "[" [] "]"))
          (Term.matchAlt
           "|"
           [[(«term[_]» "[" [(«term[_]» "[" [(Term.app `alts [`ps])] "]")] "]")]]
           "=>"
           `ps)
          (Term.matchAlt
           "|"
           [[(«term_::_» `p "::" `ps)]]
           "=>"
           («term_::_» (Term.app `tuple₁ [`p]) "::" (Term.app `alts₁_core [`ps])))])
        []))
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValEqns', expected 'Lean.Parser.Command.declValSimple'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_::_» (Term.app `tuple₁ [`p]) "::" (Term.app `alts₁_core [`ps]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `alts₁_core [`ps])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ps
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `alts₁_core
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 67 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 67, term))
      (Term.app `tuple₁ [`p])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `tuple₁
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 68 >? 1022, (some 1023, term) <=? (some 67, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 67, (some 67, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_::_» `p "::" `ps)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ps
[PrettyPrinter.parenthesize] ...precedences are 67 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 67, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 68 >? 1024, (none, [anonymous]) <=? (some 67, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 67, (some 67, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      `ps
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term[_]» "[" [(«term[_]» "[" [(Term.app `alts [`ps])] "]")] "]")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term[_]» "[" [(Term.app `alts [`ps])] "]")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `alts [`ps])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ps
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `alts
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term[_]» "[" [] "]")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term[_]» "[" [] "]")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.arrow
       (Term.app
        (Tactic.Tactic.Rcases.«termlistΣ» "listΣ")
        [(Term.app (Tactic.Tactic.Rcases.«termlistΠ» "listΠ") [`rcases_patt])])
       "→"
       (Term.app (Tactic.Tactic.Rcases.«termlistΣ» "listΣ") [`rcases_patt]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Tactic.Tactic.Rcases.«termlistΣ» "listΣ") [`rcases_patt])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rcases_patt
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Tactic.Tactic.Rcases.«termlistΣ» "listΣ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Tactic.Tactic.Rcases.«termlistΣ»', expected 'Tactic.Tactic.Rcases.termlistΣ._@.Tactic.Rcases._hyg.7'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
      This function is used for producing rcases patterns based on a case tree. Here we are given
      the list of patterns to apply to each argument of each constructor after the main case, and must
      produce a list of alternatives with the same effect. This function calls `tuple₁` to make the
      individual alternatives, and handles merging `[a, b, c | d]` to `a | b | c | d` instead of
      `a | b | (c | d)`. -/
    unsafe
  def
    alts₁_core
    : listΣ listΠ rcases_patt → listΣ rcases_patt
    | [ ] => [ ] | [ [ alts ps ] ] => ps | p :: ps => tuple₁ p :: alts₁_core ps
#align tactic.rcases_patt.alts₁_core tactic.rcases_patt.alts₁_core

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "This function is used for producing rcases patterns based on a case tree. This is like\n`alts₁_core`, but it produces a cases pattern directly instead of a list of alternatives. We\nspecially translate the empty alternation to `⟨⟩`, and translate `|(a | b)` to `⟨a | b⟩` (because we\ndon't have any syntax for unary alternation). Otherwise we can use the regular merging of\nalternations at the last argument so that `a | b | (c | d)` becomes `a | b | c | d`. -/")]
      []
      []
      []
      [(Command.unsafe "unsafe")]
      [])
     (Command.def
      "def"
      (Command.declId `alts₁ [])
      (Command.optDeclSig
       []
       [(Term.typeSpec
         ":"
         (Term.arrow
          (Term.app
           (Tactic.Tactic.Rcases.«termlistΣ» "listΣ")
           [(Term.app (Tactic.Tactic.Rcases.«termlistΠ» "listΠ") [`rcases_patt])])
          "→"
          `rcases_patt))])
      (Command.declValEqns
       (Term.matchAltsWhereDecls
        (Term.matchAlts
         [(Term.matchAlt
           "|"
           [[(«term[_]» "[" [(«term[_]» "[" [] "]")] "]")]]
           "=>"
           (Term.app `tuple [(«term[_]» "[" [] "]")]))
          (Term.matchAlt
           "|"
           [[(«term[_]» "[" [(«term[_]» "[" [(Term.app `alts [`ps])] "]")] "]")]]
           "=>"
           (Term.app `tuple [(«term[_]» "[" [(Term.app `alts [`ps])] "]")]))
          (Term.matchAlt "|" [[`ps]] "=>" (Term.app `alts' [(Term.app `alts₁_core [`ps])]))])
        []))
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValEqns', expected 'Lean.Parser.Command.declValSimple'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `alts' [(Term.app `alts₁_core [`ps])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `alts₁_core [`ps])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ps
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `alts₁_core
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `alts₁_core [`ps]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `alts'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ps
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app `tuple [(«term[_]» "[" [(Term.app `alts [`ps])] "]")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term[_]»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term[_]»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term[_]» "[" [(Term.app `alts [`ps])] "]")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `alts [`ps])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ps
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `alts
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `tuple
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term[_]» "[" [(«term[_]» "[" [(Term.app `alts [`ps])] "]")] "]")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term[_]» "[" [(Term.app `alts [`ps])] "]")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `alts [`ps])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ps
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `alts
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app `tuple [(«term[_]» "[" [] "]")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term[_]»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term[_]»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term[_]» "[" [] "]")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `tuple
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term[_]» "[" [(«term[_]» "[" [] "]")] "]")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term[_]» "[" [] "]")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.arrow
       (Term.app
        (Tactic.Tactic.Rcases.«termlistΣ» "listΣ")
        [(Term.app (Tactic.Tactic.Rcases.«termlistΠ» "listΠ") [`rcases_patt])])
       "→"
       `rcases_patt)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rcases_patt
[PrettyPrinter.parenthesize] ...precedences are 25 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
      (Term.app
       (Tactic.Tactic.Rcases.«termlistΣ» "listΣ")
       [(Term.app (Tactic.Tactic.Rcases.«termlistΠ» "listΠ") [`rcases_patt])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Tactic.Tactic.Rcases.«termlistΠ» "listΠ") [`rcases_patt])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rcases_patt
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Tactic.Tactic.Rcases.«termlistΠ» "listΠ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Tactic.Tactic.Rcases.«termlistΠ»', expected 'Tactic.Tactic.Rcases.termlistΠ._@.Tactic.Rcases._hyg.324'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
      This function is used for producing rcases patterns based on a case tree. This is like
      `alts₁_core`, but it produces a cases pattern directly instead of a list of alternatives. We
      specially translate the empty alternation to `⟨⟩`, and translate `|(a | b)` to `⟨a | b⟩` (because we
      don't have any syntax for unary alternation). Otherwise we can use the regular merging of
      alternations at the last argument so that `a | b | (c | d)` becomes `a | b | c | d`. -/
    unsafe
  def
    alts₁
    : listΣ listΠ rcases_patt → rcases_patt
    | [ [ ] ] => tuple [ ] | [ [ alts ps ] ] => tuple [ alts ps ] | ps => alts' alts₁_core ps
#align tactic.rcases_patt.alts₁ tactic.rcases_patt.alts₁

unsafe instance has_reflect : has_reflect rcases_patt
  | one n => q(_)
  | clear => q(_)
  | explicit l => q(explicit).subst (has_reflect l)
  | typed l e => (q(typed).subst (has_reflect l)).subst (reflect e)
  | tuple l =>
    q(fun l => tuple l).subst <|
      haveI := has_reflect
      list.reflect l
  | alts l =>
    q(fun l => alts l).subst <|
      haveI := has_reflect
      list.reflect l
#align tactic.rcases_patt.has_reflect tactic.rcases_patt.has_reflect

/-- Formats an `rcases` pattern. If the `bracket` argument is true, then it will be
printed at high precedence, i.e. it will have parentheses around it if it is not already a tuple
or atomic name. -/
protected unsafe def format : ∀ bracket : Bool, rcases_patt → tactic _root_.format
  | _, one n => pure <| to_fmt n
  | _, clear => pure "-"
  | _, explicit p => do
    let f ← format true p
    pure <| "@" ++ f
  | _, tuple [] => pure "⟨⟩"
  | _, tuple ls => do
    let fs ← ls.mmap <| format false
    pure <|
        "⟨" ++
            _root_.format.group
              (_root_.format.nest 1 <|
                _root_.format.join <| List.intersperse ("," ++ _root_.format.line) fs) ++
          "⟩"
  | br, alts ls => do
    let fs ← ls.mmap <| format true
    let fmt := _root_.format.join <| List.intersperse (↑" |" ++ _root_.format.space) fs
    pure <| if br then _root_.format.bracket "(" ")" fmt else fmt
  | br, typed p e => do
    let fp ← format false p
    let fe ← pp e
    let fmt := fp ++ " : " ++ fe
    pure <| if br then _root_.format.bracket "(" ")" fmt else fmt
#align tactic.rcases_patt.format tactic.rcases_patt.format

unsafe instance has_to_tactic_format : has_to_tactic_format rcases_patt :=
  ⟨rcases_patt.format false⟩
#align tactic.rcases_patt.has_to_tactic_format tactic.rcases_patt.has_to_tactic_format

end RcasesPatt

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "Takes the number of fields of a single constructor and patterns to match its fields against\n(not necessarily the same number). The returned lists each contain one element per field of the\nconstructor. The `name` is the name which will be used in the top-level `cases` tactic, and the\n`rcases_patt` is the pattern which the field will be matched against by subsequent `cases`\ntactics. -/")]
      []
      []
      []
      [(Command.unsafe "unsafe")]
      [])
     (Command.def
      "def"
      (Command.declId `rcases.process_constructor [])
      (Command.optDeclSig
       []
       [(Term.typeSpec
         ":"
         (Term.arrow
          `Bool
          "→"
          (Term.arrow
           (Term.app `List [`BinderInfo])
           "→"
           (Term.arrow
            (Term.app (Tactic.Tactic.Rcases.«termlistΠ» "listΠ") [`rcases_patt])
            "→"
            («term_×_»
             (Term.app (Tactic.Tactic.Rcases.«termlistΠ» "listΠ") [`Name])
             "×"
             (Term.app (Tactic.Tactic.Rcases.«termlistΠ» "listΠ") [`rcases_patt]))))))])
      (Command.declValEqns
       (Term.matchAltsWhereDecls
        (Term.matchAlts
         [(Term.matchAlt
           "|"
           [[(Term.hole "_") "," («term[_]» "[" [] "]") "," `ps]]
           "=>"
           (Term.tuple "(" [(«term[_]» "[" [] "]") "," [(«term[_]» "[" [] "]")]] ")"))
          (Term.matchAlt
           "|"
           [[`explicit "," («term_::_» `bi "::" `l) "," `ps]]
           "=>"
           (termIfThenElse
            "if"
            («term_&&_»
             (Data.Bool.Basic.term!_ "!" `explicit)
             "&&"
             («term_≠_» `bi "≠" `BinderInfo.default))
            "then"
            (Term.let
             "let"
             (Term.letDecl
              (Term.letPatDecl
               (Term.tuple "(" [`ns "," [`tl]] ")")
               []
               []
               ":="
               (Term.app `rcases.process_constructor [`explicit `l `ps])))
             []
             (Term.tuple
              "("
              [(«term_::_» (Term.quotedName (name "`_")) "::" `ns)
               ","
               [(«term_::_» `default "::" `tl)]]
              ")"))
            "else"
            (Term.match
             "match"
             []
             []
             [(Term.matchDiscr [] `l) "," (Term.matchDiscr [] `ps)]
             "with"
             (Term.matchAlts
              [(Term.matchAlt
                "|"
                [[(«term[_]» "[" [] "]") "," («term[_]» "[" [] "]")]]
                "=>"
                (Term.tuple
                 "("
                 [(«term[_]» "[" [(Term.quotedName (name "`_"))] "]")
                  ","
                  [(«term[_]» "[" [`default] "]")]]
                 ")"))
               (Term.matchAlt
                "|"
                [[(«term[_]» "[" [] "]") "," («term[_]» "[" [`p] "]")]]
                "=>"
                (Term.tuple
                 "("
                 [(«term[_]»
                   "["
                   [(Term.app
                     (Term.proj (Term.proj `p "." `Name) "." `getOrElse)
                     [(Term.quotedName (name "`_"))])]
                   "]")
                  ","
                  [(«term[_]» "[" [`p] "]")]]
                 ")"))
               (Term.matchAlt
                "|"
                [[(«term[_]» "[" [] "]") "," `ps]]
                "=>"
                (Term.tuple
                 "("
                 [(«term[_]» "[" [(Term.quotedName (name "`_"))] "]")
                  ","
                  [(«term[_]»
                    "["
                    [(Term.app
                      `cond
                      [`explicit
                       (Term.proj (Term.app `rcases_patt.tuple [`ps]) "." `explicit)
                       (Term.app `rcases_patt.tuple [`ps])])]
                    "]")]]
                 ")"))
               (Term.matchAlt
                "|"
                [[`l "," `ps]]
                "=>"
                (Term.let
                 "let"
                 (Term.letDecl (Term.letIdDecl `hd [] [] ":=" (Term.proj `ps "." `head)))
                 []
                 (Term.let
                  "let"
                  (Term.letDecl
                   (Term.letPatDecl
                    (Term.tuple "(" [`ns "," [`tl]] ")")
                    []
                    []
                    ":="
                    (Term.app
                     `rcases.process_constructor
                     [`explicit `l (Term.proj `ps "." `tail)])))
                  []
                  (Term.tuple
                   "("
                   [(«term_::_»
                     (Term.app
                      (Term.proj (Term.proj `hd "." `Name) "." `getOrElse)
                      [(Term.quotedName (name "`_"))])
                     "::"
                     `ns)
                    ","
                    [(«term_::_» `hd "::" `tl)]]
                   ")"))))]))))])
        []))
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValEqns', expected 'Lean.Parser.Command.declValSimple'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (termIfThenElse
       "if"
       («term_&&_»
        (Data.Bool.Basic.term!_ "!" `explicit)
        "&&"
        («term_≠_» `bi "≠" `BinderInfo.default))
       "then"
       (Term.let
        "let"
        (Term.letDecl
         (Term.letPatDecl
          (Term.tuple "(" [`ns "," [`tl]] ")")
          []
          []
          ":="
          (Term.app `rcases.process_constructor [`explicit `l `ps])))
        []
        (Term.tuple
         "("
         [(«term_::_» (Term.quotedName (name "`_")) "::" `ns) "," [(«term_::_» `default "::" `tl)]]
         ")"))
       "else"
       (Term.match
        "match"
        []
        []
        [(Term.matchDiscr [] `l) "," (Term.matchDiscr [] `ps)]
        "with"
        (Term.matchAlts
         [(Term.matchAlt
           "|"
           [[(«term[_]» "[" [] "]") "," («term[_]» "[" [] "]")]]
           "=>"
           (Term.tuple
            "("
            [(«term[_]» "[" [(Term.quotedName (name "`_"))] "]")
             ","
             [(«term[_]» "[" [`default] "]")]]
            ")"))
          (Term.matchAlt
           "|"
           [[(«term[_]» "[" [] "]") "," («term[_]» "[" [`p] "]")]]
           "=>"
           (Term.tuple
            "("
            [(«term[_]»
              "["
              [(Term.app
                (Term.proj (Term.proj `p "." `Name) "." `getOrElse)
                [(Term.quotedName (name "`_"))])]
              "]")
             ","
             [(«term[_]» "[" [`p] "]")]]
            ")"))
          (Term.matchAlt
           "|"
           [[(«term[_]» "[" [] "]") "," `ps]]
           "=>"
           (Term.tuple
            "("
            [(«term[_]» "[" [(Term.quotedName (name "`_"))] "]")
             ","
             [(«term[_]»
               "["
               [(Term.app
                 `cond
                 [`explicit
                  (Term.proj (Term.app `rcases_patt.tuple [`ps]) "." `explicit)
                  (Term.app `rcases_patt.tuple [`ps])])]
               "]")]]
            ")"))
          (Term.matchAlt
           "|"
           [[`l "," `ps]]
           "=>"
           (Term.let
            "let"
            (Term.letDecl (Term.letIdDecl `hd [] [] ":=" (Term.proj `ps "." `head)))
            []
            (Term.let
             "let"
             (Term.letDecl
              (Term.letPatDecl
               (Term.tuple "(" [`ns "," [`tl]] ")")
               []
               []
               ":="
               (Term.app `rcases.process_constructor [`explicit `l (Term.proj `ps "." `tail)])))
             []
             (Term.tuple
              "("
              [(«term_::_»
                (Term.app
                 (Term.proj (Term.proj `hd "." `Name) "." `getOrElse)
                 [(Term.quotedName (name "`_"))])
                "::"
                `ns)
               ","
               [(«term_::_» `hd "::" `tl)]]
              ")"))))])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.match
       "match"
       []
       []
       [(Term.matchDiscr [] `l) "," (Term.matchDiscr [] `ps)]
       "with"
       (Term.matchAlts
        [(Term.matchAlt
          "|"
          [[(«term[_]» "[" [] "]") "," («term[_]» "[" [] "]")]]
          "=>"
          (Term.tuple
           "("
           [(«term[_]» "[" [(Term.quotedName (name "`_"))] "]")
            ","
            [(«term[_]» "[" [`default] "]")]]
           ")"))
         (Term.matchAlt
          "|"
          [[(«term[_]» "[" [] "]") "," («term[_]» "[" [`p] "]")]]
          "=>"
          (Term.tuple
           "("
           [(«term[_]»
             "["
             [(Term.app
               (Term.proj (Term.proj `p "." `Name) "." `getOrElse)
               [(Term.quotedName (name "`_"))])]
             "]")
            ","
            [(«term[_]» "[" [`p] "]")]]
           ")"))
         (Term.matchAlt
          "|"
          [[(«term[_]» "[" [] "]") "," `ps]]
          "=>"
          (Term.tuple
           "("
           [(«term[_]» "[" [(Term.quotedName (name "`_"))] "]")
            ","
            [(«term[_]»
              "["
              [(Term.app
                `cond
                [`explicit
                 (Term.proj (Term.app `rcases_patt.tuple [`ps]) "." `explicit)
                 (Term.app `rcases_patt.tuple [`ps])])]
              "]")]]
           ")"))
         (Term.matchAlt
          "|"
          [[`l "," `ps]]
          "=>"
          (Term.let
           "let"
           (Term.letDecl (Term.letIdDecl `hd [] [] ":=" (Term.proj `ps "." `head)))
           []
           (Term.let
            "let"
            (Term.letDecl
             (Term.letPatDecl
              (Term.tuple "(" [`ns "," [`tl]] ")")
              []
              []
              ":="
              (Term.app `rcases.process_constructor [`explicit `l (Term.proj `ps "." `tail)])))
            []
            (Term.tuple
             "("
             [(«term_::_»
               (Term.app
                (Term.proj (Term.proj `hd "." `Name) "." `getOrElse)
                [(Term.quotedName (name "`_"))])
               "::"
               `ns)
              ","
              [(«term_::_» `hd "::" `tl)]]
             ")"))))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.let
       "let"
       (Term.letDecl (Term.letIdDecl `hd [] [] ":=" (Term.proj `ps "." `head)))
       []
       (Term.let
        "let"
        (Term.letDecl
         (Term.letPatDecl
          (Term.tuple "(" [`ns "," [`tl]] ")")
          []
          []
          ":="
          (Term.app `rcases.process_constructor [`explicit `l (Term.proj `ps "." `tail)])))
        []
        (Term.tuple
         "("
         [(«term_::_»
           (Term.app
            (Term.proj (Term.proj `hd "." `Name) "." `getOrElse)
            [(Term.quotedName (name "`_"))])
           "::"
           `ns)
          ","
          [(«term_::_» `hd "::" `tl)]]
         ")")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.let
       "let"
       (Term.letDecl
        (Term.letPatDecl
         (Term.tuple "(" [`ns "," [`tl]] ")")
         []
         []
         ":="
         (Term.app `rcases.process_constructor [`explicit `l (Term.proj `ps "." `tail)])))
       []
       (Term.tuple
        "("
        [(«term_::_»
          (Term.app
           (Term.proj (Term.proj `hd "." `Name) "." `getOrElse)
           [(Term.quotedName (name "`_"))])
          "::"
          `ns)
         ","
         [(«term_::_» `hd "::" `tl)]]
        ")"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.tuple
       "("
       [(«term_::_»
         (Term.app
          (Term.proj (Term.proj `hd "." `Name) "." `getOrElse)
          [(Term.quotedName (name "`_"))])
         "::"
         `ns)
        ","
        [(«term_::_» `hd "::" `tl)]]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_::_» `hd "::" `tl)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `tl
[PrettyPrinter.parenthesize] ...precedences are 67 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 67, term))
      `hd
[PrettyPrinter.parenthesize] ...precedences are 68 >? 1024, (none, [anonymous]) <=? (some 67, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 67, (some 67, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_::_»
       (Term.app
        (Term.proj (Term.proj `hd "." `Name) "." `getOrElse)
        [(Term.quotedName (name "`_"))])
       "::"
       `ns)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ns
[PrettyPrinter.parenthesize] ...precedences are 67 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 67, term))
      (Term.app
       (Term.proj (Term.proj `hd "." `Name) "." `getOrElse)
       [(Term.quotedName (name "`_"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.quotedName', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.quotedName', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.quotedName (name "`_"))
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.proj `hd "." `Name) "." `getOrElse)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj `hd "." `Name)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hd
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 68 >? 1022, (some 1023, term) <=? (some 67, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 67, (some 67, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letPatDecl', expected 'Lean.Parser.Term.letIdDecl'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `rcases.process_constructor [`explicit `l (Term.proj `ps "." `tail)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `ps "." `tail)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `ps
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `l
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `explicit
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `rcases.process_constructor
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.tuple "(" [`ns "," [`tl]] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `tl
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ns
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `ps "." `head)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `ps
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ps
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `l
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.tuple
       "("
       [(«term[_]» "[" [(Term.quotedName (name "`_"))] "]")
        ","
        [(«term[_]»
          "["
          [(Term.app
            `cond
            [`explicit
             (Term.proj (Term.app `rcases_patt.tuple [`ps]) "." `explicit)
             (Term.app `rcases_patt.tuple [`ps])])]
          "]")]]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term[_]»
       "["
       [(Term.app
         `cond
         [`explicit
          (Term.proj (Term.app `rcases_patt.tuple [`ps]) "." `explicit)
          (Term.app `rcases_patt.tuple [`ps])])]
       "]")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `cond
       [`explicit
        (Term.proj (Term.app `rcases_patt.tuple [`ps]) "." `explicit)
        (Term.app `rcases_patt.tuple [`ps])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `rcases_patt.tuple [`ps])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ps
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `rcases_patt.tuple
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `rcases_patt.tuple [`ps]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj (Term.app `rcases_patt.tuple [`ps]) "." `explicit)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `rcases_patt.tuple [`ps])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ps
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `rcases_patt.tuple
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `rcases_patt.tuple [`ps]) ")")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `explicit
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `cond
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term[_]» "[" [(Term.quotedName (name "`_"))] "]")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.quotedName (name "`_"))
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ps
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term[_]» "[" [] "]")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.tuple
       "("
       [(«term[_]»
         "["
         [(Term.app
           (Term.proj (Term.proj `p "." `Name) "." `getOrElse)
           [(Term.quotedName (name "`_"))])]
         "]")
        ","
        [(«term[_]» "[" [`p] "]")]]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term[_]» "[" [`p] "]")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term[_]»
       "["
       [(Term.app
         (Term.proj (Term.proj `p "." `Name) "." `getOrElse)
         [(Term.quotedName (name "`_"))])]
       "]")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj (Term.proj `p "." `Name) "." `getOrElse) [(Term.quotedName (name "`_"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.quotedName', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.quotedName', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.quotedName (name "`_"))
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.proj `p "." `Name) "." `getOrElse)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj `p "." `Name)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term[_]» "[" [`p] "]")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term[_]» "[" [] "]")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.tuple
       "("
       [(«term[_]» "[" [(Term.quotedName (name "`_"))] "]") "," [(«term[_]» "[" [`default] "]")]]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term[_]» "[" [`default] "]")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `default
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term[_]» "[" [(Term.quotedName (name "`_"))] "]")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.quotedName (name "`_"))
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term[_]» "[" [] "]")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term[_]» "[" [] "]")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ps
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `l
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.let
       "let"
       (Term.letDecl
        (Term.letPatDecl
         (Term.tuple "(" [`ns "," [`tl]] ")")
         []
         []
         ":="
         (Term.app `rcases.process_constructor [`explicit `l `ps])))
       []
       (Term.tuple
        "("
        [(«term_::_» (Term.quotedName (name "`_")) "::" `ns) "," [(«term_::_» `default "::" `tl)]]
        ")"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.tuple
       "("
       [(«term_::_» (Term.quotedName (name "`_")) "::" `ns) "," [(«term_::_» `default "::" `tl)]]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_::_» `default "::" `tl)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `tl
[PrettyPrinter.parenthesize] ...precedences are 67 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 67, term))
      `default
[PrettyPrinter.parenthesize] ...precedences are 68 >? 1024, (none, [anonymous]) <=? (some 67, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 67, (some 67, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_::_» (Term.quotedName (name "`_")) "::" `ns)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ns
[PrettyPrinter.parenthesize] ...precedences are 67 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 67, term))
      (Term.quotedName (name "`_"))
[PrettyPrinter.parenthesize] ...precedences are 68 >? 1024, (none, [anonymous]) <=? (some 67, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 67, (some 67, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letPatDecl', expected 'Lean.Parser.Term.letIdDecl'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `rcases.process_constructor [`explicit `l `ps])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ps
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `l
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `explicit
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `rcases.process_constructor
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.tuple "(" [`ns "," [`tl]] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `tl
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ns
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_&&_»
       (Data.Bool.Basic.term!_ "!" `explicit)
       "&&"
       («term_≠_» `bi "≠" `BinderInfo.default))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≠_» `bi "≠" `BinderInfo.default)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `BinderInfo.default
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `bi
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 36 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 35, term))
      (Data.Bool.Basic.term!_ "!" `explicit)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `explicit
[PrettyPrinter.parenthesize] ...precedences are 90 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 35 >? 90, (some 90, term) <=? (some 35, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 35, (some 36, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ps
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_::_» `bi "::" `l)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `l
[PrettyPrinter.parenthesize] ...precedences are 67 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 67, term))
      `bi
[PrettyPrinter.parenthesize] ...precedences are 68 >? 1024, (none, [anonymous]) <=? (some 67, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 67, (some 67, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `explicit
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.tuple "(" [(«term[_]» "[" [] "]") "," [(«term[_]» "[" [] "]")]] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term[_]» "[" [] "]")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term[_]» "[" [] "]")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ps
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term[_]» "[" [] "]")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.arrow
       `Bool
       "→"
       (Term.arrow
        (Term.app `List [`BinderInfo])
        "→"
        (Term.arrow
         (Term.app (Tactic.Tactic.Rcases.«termlistΠ» "listΠ") [`rcases_patt])
         "→"
         («term_×_»
          (Term.app (Tactic.Tactic.Rcases.«termlistΠ» "listΠ") [`Name])
          "×"
          (Term.app (Tactic.Tactic.Rcases.«termlistΠ» "listΠ") [`rcases_patt])))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.arrow
       (Term.app `List [`BinderInfo])
       "→"
       (Term.arrow
        (Term.app (Tactic.Tactic.Rcases.«termlistΠ» "listΠ") [`rcases_patt])
        "→"
        («term_×_»
         (Term.app (Tactic.Tactic.Rcases.«termlistΠ» "listΠ") [`Name])
         "×"
         (Term.app (Tactic.Tactic.Rcases.«termlistΠ» "listΠ") [`rcases_patt]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.arrow
       (Term.app (Tactic.Tactic.Rcases.«termlistΠ» "listΠ") [`rcases_patt])
       "→"
       («term_×_»
        (Term.app (Tactic.Tactic.Rcases.«termlistΠ» "listΠ") [`Name])
        "×"
        (Term.app (Tactic.Tactic.Rcases.«termlistΠ» "listΠ") [`rcases_patt])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_×_»
       (Term.app (Tactic.Tactic.Rcases.«termlistΠ» "listΠ") [`Name])
       "×"
       (Term.app (Tactic.Tactic.Rcases.«termlistΠ» "listΠ") [`rcases_patt]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Tactic.Tactic.Rcases.«termlistΠ» "listΠ") [`rcases_patt])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rcases_patt
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Tactic.Tactic.Rcases.«termlistΠ» "listΠ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Tactic.Tactic.Rcases.«termlistΠ»', expected 'Tactic.Tactic.Rcases.termlistΠ._@.Tactic.Rcases._hyg.324'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
      Takes the number of fields of a single constructor and patterns to match its fields against
      (not necessarily the same number). The returned lists each contain one element per field of the
      constructor. The `name` is the name which will be used in the top-level `cases` tactic, and the
      `rcases_patt` is the pattern which the field will be matched against by subsequent `cases`
      tactics. -/
    unsafe
  def
    rcases.process_constructor
    : Bool → List BinderInfo → listΠ rcases_patt → listΠ Name × listΠ rcases_patt
    | _ , [ ] , ps => ( [ ] , [ ] )
      |
        explicit , bi :: l , ps
        =>
        if
          ! explicit && bi ≠ BinderInfo.default
          then
          let ( ns , tl ) := rcases.process_constructor explicit l ps ( `_ :: ns , default :: tl )
          else
          match
            l , ps
            with
            | [ ] , [ ] => ( [ `_ ] , [ default ] )
              | [ ] , [ p ] => ( [ p . Name . getOrElse `_ ] , [ p ] )
              |
                [ ] , ps
                =>
                ( [ `_ ] , [ cond explicit rcases_patt.tuple ps . explicit rcases_patt.tuple ps ] )
              |
                l , ps
                =>
                let
                  hd := ps . head
                  let
                    ( ns , tl ) := rcases.process_constructor explicit l ps . tail
                    ( hd . Name . getOrElse `_ :: ns , hd :: tl )
#align tactic.rcases.process_constructor tactic.rcases.process_constructor

private unsafe def get_pi_arity_list_aux : expr → tactic (List BinderInfo)
  | expr.pi n bi d b => do
    let m ← mk_fresh_name
    let l := expr.local_const m n bi d
    let new_b ← whnf (expr.instantiate_var b l)
    let r ← get_pi_arity_list_aux new_b
    return (bi :: r)
  | e => return []
#align tactic.get_pi_arity_list_aux tactic.get_pi_arity_list_aux

/-- Compute the arity of the given (Pi-)type -/
unsafe def get_pi_arity_list (type : expr) : tactic (List BinderInfo) :=
  whnf type >>= get_pi_arity_list_aux
#align tactic.get_pi_arity_list tactic.get_pi_arity_list

/-- Compute the arity of the given function -/
unsafe def get_arity_list (fn : expr) : tactic (List BinderInfo) :=
  infer_type fn >>= get_pi_arity_list
#align tactic.get_arity_list tactic.get_arity_list

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "Takes a list of constructor names, and an (alternation) list of patterns, and matches each\npattern against its constructor. It returns the list of names that will be passed to `cases`,\nand the list of `(constructor name, patterns)` for each constructor, where `patterns` is the\n(conjunctive) list of patterns to apply to each constructor argument. -/")]
      []
      []
      []
      [(Command.unsafe "unsafe")]
      [])
     (Command.def
      "def"
      (Command.declId `rcases.process_constructors [])
      (Command.optDeclSig
       [(Term.explicitBinder "(" [`params] [":" `Nat] [] ")")]
       [(Term.typeSpec
         ":"
         (Term.arrow
          (Term.app (Tactic.Tactic.Rcases.«termlistΣ» "listΣ") [`Name])
          "→"
          (Term.arrow
           (Term.app (Tactic.Tactic.Rcases.«termlistΣ» "listΣ") [`rcases_patt])
           "→"
           (Term.app
            `tactic
            [(«term_×_»
              (Term.app `Dlist [`Name])
              "×"
              (Term.app
               (Tactic.Tactic.Rcases.«termlistΣ» "listΣ")
               [(«term_×_»
                 `Name
                 "×"
                 (Term.app (Tactic.Tactic.Rcases.«termlistΠ» "listΠ") [`rcases_patt]))]))]))))])
      (Command.declValEqns
       (Term.matchAltsWhereDecls
        (Term.matchAlts
         [(Term.matchAlt
           "|"
           [[(«term[_]» "[" [] "]") "," `ps]]
           "=>"
           (Term.app `pure [(Term.tuple "(" [`Dlist.empty "," [(«term[_]» "[" [] "]")]] ")")]))
          (Term.matchAlt
           "|"
           [[(«term_::_» `c "::" `cs) "," `ps]]
           "=>"
           (Term.do
            "do"
            (Term.doSeqIndent
             [(Term.doSeqItem
               (Term.doLetArrow
                "let"
                []
                (Term.doIdDecl
                 `l
                 []
                 "←"
                 (Term.doExpr («term_>>=_» (Term.app `mk_const [`c]) ">>=" `get_arity_list))))
               [])
              (Term.doSeqItem
               (Term.doLet
                "let"
                []
                (Term.letDecl
                 (Term.letPatDecl
                  (Term.tuple "(" [(Term.tuple "(" [`explicit "," [`h]] ")") "," [`t]] ")")
                  []
                  []
                  ":="
                  (Term.typeAscription
                   "("
                   (Term.match
                    "match"
                    []
                    []
                    [(Term.matchDiscr [] `cs) "," (Term.matchDiscr [] (Term.proj `ps "." `tail))]
                    "with"
                    (Term.matchAlts
                     [(Term.matchAlt
                       "|"
                       [[(«term[_]» "[" [] "]")
                         ","
                         («term_::_» (Term.hole "_") "::" (Term.hole "_"))]]
                       "=>"
                       (Term.tuple
                        "("
                        [(Term.tuple
                          "("
                          [`false "," [(«term[_]» "[" [(Term.app `rcases_patt.alts [`ps])] "]")]]
                          ")")
                         ","
                         [(«term[_]» "[" [] "]")]]
                        ")"))
                      (Term.matchAlt
                       "|"
                       [[(Term.hole "_") "," (Term.hole "_")]]
                       "=>"
                       (Term.tuple
                        "("
                        [(Term.proj (Term.proj `ps "." `head) "." `as_tuple)
                         ","
                         [(Term.proj `ps "." `tail)]]
                        ")"))]))
                   ":"
                   [(Term.hole "_")]
                   ")"))))
               [])
              (Term.doSeqItem
               (Term.doLet
                "let"
                []
                (Term.letDecl
                 (Term.letPatDecl
                  (Term.tuple "(" [`ns "," [`ps]] ")")
                  []
                  []
                  ":="
                  (Term.app
                   `rcases.process_constructor
                   [`explicit (Term.app (Term.proj `l "." `drop) [`params]) `h]))))
               [])
              (Term.doSeqItem
               (Term.doLetArrow
                "let"
                []
                (Term.doPatDecl
                 (Term.tuple "(" [`l "," [`r]] ")")
                 "←"
                 (Term.doExpr (Term.app `rcases.process_constructors [`cs `t]))
                 []))
               [])
              (Term.doSeqItem
               (Term.doExpr
                (Term.app
                 `pure
                 [(Term.tuple
                   "("
                   [(«term_++_» (Term.app `Dlist.ofList [`ns]) "++" `l)
                    ","
                    [(«term_::_» (Term.tuple "(" [`c "," [`ps]] ")") "::" `r)]]
                   ")")]))
               [])])))])
        []))
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValEqns', expected 'Lean.Parser.Command.declValSimple'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.do
       "do"
       (Term.doSeqIndent
        [(Term.doSeqItem
          (Term.doLetArrow
           "let"
           []
           (Term.doIdDecl
            `l
            []
            "←"
            (Term.doExpr («term_>>=_» (Term.app `mk_const [`c]) ">>=" `get_arity_list))))
          [])
         (Term.doSeqItem
          (Term.doLet
           "let"
           []
           (Term.letDecl
            (Term.letPatDecl
             (Term.tuple "(" [(Term.tuple "(" [`explicit "," [`h]] ")") "," [`t]] ")")
             []
             []
             ":="
             (Term.typeAscription
              "("
              (Term.match
               "match"
               []
               []
               [(Term.matchDiscr [] `cs) "," (Term.matchDiscr [] (Term.proj `ps "." `tail))]
               "with"
               (Term.matchAlts
                [(Term.matchAlt
                  "|"
                  [[(«term[_]» "[" [] "]") "," («term_::_» (Term.hole "_") "::" (Term.hole "_"))]]
                  "=>"
                  (Term.tuple
                   "("
                   [(Term.tuple
                     "("
                     [`false "," [(«term[_]» "[" [(Term.app `rcases_patt.alts [`ps])] "]")]]
                     ")")
                    ","
                    [(«term[_]» "[" [] "]")]]
                   ")"))
                 (Term.matchAlt
                  "|"
                  [[(Term.hole "_") "," (Term.hole "_")]]
                  "=>"
                  (Term.tuple
                   "("
                   [(Term.proj (Term.proj `ps "." `head) "." `as_tuple)
                    ","
                    [(Term.proj `ps "." `tail)]]
                   ")"))]))
              ":"
              [(Term.hole "_")]
              ")"))))
          [])
         (Term.doSeqItem
          (Term.doLet
           "let"
           []
           (Term.letDecl
            (Term.letPatDecl
             (Term.tuple "(" [`ns "," [`ps]] ")")
             []
             []
             ":="
             (Term.app
              `rcases.process_constructor
              [`explicit (Term.app (Term.proj `l "." `drop) [`params]) `h]))))
          [])
         (Term.doSeqItem
          (Term.doLetArrow
           "let"
           []
           (Term.doPatDecl
            (Term.tuple "(" [`l "," [`r]] ")")
            "←"
            (Term.doExpr (Term.app `rcases.process_constructors [`cs `t]))
            []))
          [])
         (Term.doSeqItem
          (Term.doExpr
           (Term.app
            `pure
            [(Term.tuple
              "("
              [(«term_++_» (Term.app `Dlist.ofList [`ns]) "++" `l)
               ","
               [(«term_::_» (Term.tuple "(" [`c "," [`ps]] ")") "::" `r)]]
              ")")]))
          [])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doSeqIndent', expected 'Lean.Parser.Term.doSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `pure
       [(Term.tuple
         "("
         [(«term_++_» (Term.app `Dlist.ofList [`ns]) "++" `l)
          ","
          [(«term_::_» (Term.tuple "(" [`c "," [`ps]] ")") "::" `r)]]
         ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.tuple', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.tuple', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.tuple
       "("
       [(«term_++_» (Term.app `Dlist.ofList [`ns]) "++" `l)
        ","
        [(«term_::_» (Term.tuple "(" [`c "," [`ps]] ")") "::" `r)]]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_::_» (Term.tuple "(" [`c "," [`ps]] ")") "::" `r)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `r
[PrettyPrinter.parenthesize] ...precedences are 67 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 67, term))
      (Term.tuple "(" [`c "," [`ps]] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ps
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `c
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 68 >? 1024, (none, [anonymous]) <=? (some 67, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 67, (some 67, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_++_» (Term.app `Dlist.ofList [`ns]) "++" `l)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `l
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      (Term.app `Dlist.ofList [`ns])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ns
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Dlist.ofList
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1022, (some 1023, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `pure
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doPatDecl', expected 'Lean.Parser.Term.doIdDecl'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, doElem))
      (Term.app `rcases.process_constructors [`cs `t])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `t
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `cs
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `rcases.process_constructors
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, doElem)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.tuple "(" [`l "," [`r]] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `r
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `l
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letPatDecl', expected 'Lean.Parser.Term.letIdDecl'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, doElem))
      (Term.app
       `rcases.process_constructor
       [`explicit (Term.app (Term.proj `l "." `drop) [`params]) `h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app (Term.proj `l "." `drop) [`params])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `params
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `l "." `drop)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `l
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.proj `l "." `drop) [`params])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `explicit
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `rcases.process_constructor
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1023, doElem)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.tuple "(" [`ns "," [`ps]] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ps
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ns
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letPatDecl', expected 'Lean.Parser.Term.letIdDecl'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, doElem))
      (Term.typeAscription
       "("
       (Term.match
        "match"
        []
        []
        [(Term.matchDiscr [] `cs) "," (Term.matchDiscr [] (Term.proj `ps "." `tail))]
        "with"
        (Term.matchAlts
         [(Term.matchAlt
           "|"
           [[(«term[_]» "[" [] "]") "," («term_::_» (Term.hole "_") "::" (Term.hole "_"))]]
           "=>"
           (Term.tuple
            "("
            [(Term.tuple
              "("
              [`false "," [(«term[_]» "[" [(Term.app `rcases_patt.alts [`ps])] "]")]]
              ")")
             ","
             [(«term[_]» "[" [] "]")]]
            ")"))
          (Term.matchAlt
           "|"
           [[(Term.hole "_") "," (Term.hole "_")]]
           "=>"
           (Term.tuple
            "("
            [(Term.proj (Term.proj `ps "." `head) "." `as_tuple) "," [(Term.proj `ps "." `tail)]]
            ")"))]))
       ":"
       [(Term.hole "_")]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.match
       "match"
       []
       []
       [(Term.matchDiscr [] `cs) "," (Term.matchDiscr [] (Term.proj `ps "." `tail))]
       "with"
       (Term.matchAlts
        [(Term.matchAlt
          "|"
          [[(«term[_]» "[" [] "]") "," («term_::_» (Term.hole "_") "::" (Term.hole "_"))]]
          "=>"
          (Term.tuple
           "("
           [(Term.tuple
             "("
             [`false "," [(«term[_]» "[" [(Term.app `rcases_patt.alts [`ps])] "]")]]
             ")")
            ","
            [(«term[_]» "[" [] "]")]]
           ")"))
         (Term.matchAlt
          "|"
          [[(Term.hole "_") "," (Term.hole "_")]]
          "=>"
          (Term.tuple
           "("
           [(Term.proj (Term.proj `ps "." `head) "." `as_tuple) "," [(Term.proj `ps "." `tail)]]
           ")"))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.tuple
       "("
       [(Term.proj (Term.proj `ps "." `head) "." `as_tuple) "," [(Term.proj `ps "." `tail)]]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `ps "." `tail)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `ps
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.proj `ps "." `head) "." `as_tuple)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj `ps "." `head)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `ps
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.tuple
       "("
       [(Term.tuple "(" [`false "," [(«term[_]» "[" [(Term.app `rcases_patt.alts [`ps])] "]")]] ")")
        ","
        [(«term[_]» "[" [] "]")]]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term[_]» "[" [] "]")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.tuple "(" [`false "," [(«term[_]» "[" [(Term.app `rcases_patt.alts [`ps])] "]")]] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term[_]» "[" [(Term.app `rcases_patt.alts [`ps])] "]")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `rcases_patt.alts [`ps])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ps
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `rcases_patt.alts
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `false
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_::_» (Term.hole "_") "::" (Term.hole "_"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 67 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 67, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 68 >? 1024, (none, [anonymous]) <=? (some 67, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 67, (some 67, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term[_]» "[" [] "]")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `ps "." `tail)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `ps
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `cs
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (some 1023, doElem)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.tuple "(" [(Term.tuple "(" [`explicit "," [`h]] ")") "," [`t]] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `t
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.tuple "(" [`explicit "," [`h]] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `explicit
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, doElem))
      («term_>>=_» (Term.app `mk_const [`c]) ">>=" `get_arity_list)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `get_arity_list
[PrettyPrinter.parenthesize] ...precedences are 56 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 55, term))
      (Term.app `mk_const [`c])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `c
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `mk_const
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 55 >? 1022, (some 1023, term) <=? (some 55, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 55, (some 56, term) <=? (none, doElem)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1023, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ps
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_::_» `c "::" `cs)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `cs
[PrettyPrinter.parenthesize] ...precedences are 67 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 67, term))
      `c
[PrettyPrinter.parenthesize] ...precedences are 68 >? 1024, (none, [anonymous]) <=? (some 67, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 67, (some 67, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app `pure [(Term.tuple "(" [`Dlist.empty "," [(«term[_]» "[" [] "]")]] ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.tuple', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.tuple', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.tuple "(" [`Dlist.empty "," [(«term[_]» "[" [] "]")]] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term[_]» "[" [] "]")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Dlist.empty
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `pure
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ps
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term[_]» "[" [] "]")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.arrow
       (Term.app (Tactic.Tactic.Rcases.«termlistΣ» "listΣ") [`Name])
       "→"
       (Term.arrow
        (Term.app (Tactic.Tactic.Rcases.«termlistΣ» "listΣ") [`rcases_patt])
        "→"
        (Term.app
         `tactic
         [(«term_×_»
           (Term.app `Dlist [`Name])
           "×"
           (Term.app
            (Tactic.Tactic.Rcases.«termlistΣ» "listΣ")
            [(«term_×_»
              `Name
              "×"
              (Term.app (Tactic.Tactic.Rcases.«termlistΠ» "listΠ") [`rcases_patt]))]))])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.arrow
       (Term.app (Tactic.Tactic.Rcases.«termlistΣ» "listΣ") [`rcases_patt])
       "→"
       (Term.app
        `tactic
        [(«term_×_»
          (Term.app `Dlist [`Name])
          "×"
          (Term.app
           (Tactic.Tactic.Rcases.«termlistΣ» "listΣ")
           [(«term_×_»
             `Name
             "×"
             (Term.app (Tactic.Tactic.Rcases.«termlistΠ» "listΠ") [`rcases_patt]))]))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `tactic
       [(«term_×_»
         (Term.app `Dlist [`Name])
         "×"
         (Term.app
          (Tactic.Tactic.Rcases.«termlistΣ» "listΣ")
          [(«term_×_»
            `Name
            "×"
            (Term.app (Tactic.Tactic.Rcases.«termlistΠ» "listΠ") [`rcases_patt]))]))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_×_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_×_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_×_»
       (Term.app `Dlist [`Name])
       "×"
       (Term.app
        (Tactic.Tactic.Rcases.«termlistΣ» "listΣ")
        [(«term_×_»
          `Name
          "×"
          (Term.app (Tactic.Tactic.Rcases.«termlistΠ» "listΠ") [`rcases_patt]))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Tactic.Tactic.Rcases.«termlistΣ» "listΣ")
       [(«term_×_» `Name "×" (Term.app (Tactic.Tactic.Rcases.«termlistΠ» "listΠ") [`rcases_patt]))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_×_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_×_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_×_» `Name "×" (Term.app (Tactic.Tactic.Rcases.«termlistΠ» "listΠ") [`rcases_patt]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Tactic.Tactic.Rcases.«termlistΠ» "listΠ") [`rcases_patt])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rcases_patt
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Tactic.Tactic.Rcases.«termlistΠ» "listΠ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Tactic.Tactic.Rcases.«termlistΠ»', expected 'Tactic.Tactic.Rcases.termlistΠ._@.Tactic.Rcases._hyg.324'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
      Takes a list of constructor names, and an (alternation) list of patterns, and matches each
      pattern against its constructor. It returns the list of names that will be passed to `cases`,
      and the list of `(constructor name, patterns)` for each constructor, where `patterns` is the
      (conjunctive) list of patterns to apply to each constructor argument. -/
    unsafe
  def
    rcases.process_constructors
    ( params : Nat )
      : listΣ Name → listΣ rcases_patt → tactic Dlist Name × listΣ Name × listΠ rcases_patt
    | [ ] , ps => pure ( Dlist.empty , [ ] )
      |
        c :: cs , ps
        =>
        do
          let l ← mk_const c >>= get_arity_list
            let
              ( ( explicit , h ) , t )
                :=
                (
                  match
                    cs , ps . tail
                    with
                    | [ ] , _ :: _ => ( ( false , [ rcases_patt.alts ps ] ) , [ ] )
                      | _ , _ => ( ps . head . as_tuple , ps . tail )
                  :
                  _
                  )
            let ( ns , ps ) := rcases.process_constructor explicit l . drop params h
            let ( l , r ) ← rcases.process_constructors cs t
            pure ( Dlist.ofList ns ++ l , ( c , ps ) :: r )
#align tactic.rcases.process_constructors tactic.rcases.process_constructors

/-- Like `zip`, but only elements satisfying a matching predicate `p` will go in the list,
and elements of the first list that fail to match the second list will be skipped. -/
private def align {α β} (p : α → β → Prop) [∀ a b, Decidable (p a b)] :
    List α → List β → List (α × β)
  | a :: as, b :: bs => if p a b then (a, b) :: align as bs else align as (b :: bs)
  | _, _ => []
#align tactic.align tactic.align

/-- Given a local constant `e`, get its type. *But* if `e` does not exist, go find a hypothesis
with the same pretty name as `e` and get it instead. This is needed because we can sometimes lose
track of the unique names of hypotheses when they are revert/intro'd by `change` and `cases`. (A
better solution would be for these tactics to return a map of renamed hypotheses so that we don't
lose track of them.) -/
private unsafe def get_local_and_type (e : expr) : tactic (expr × expr) :=
  (do
      let t ← infer_type e
      pure (t, e)) <|>
    do
    let e ← get_local e.local_pp_name
    let t ← infer_type e
    pure (t, e)
#align tactic.get_local_and_type tactic.get_local_and_type

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.mutual
     "mutual"
     [(Command.declaration
       (Command.declModifiers
        [(Command.docComment
          "/--"
          "* `rcases_core p e` will match a pattern `p` against a local hypothesis `e`.\n  It returns the list of subgoals that were produced.\n* `rcases.continue pes` will match a (conjunctive) list of `(p, e)` pairs which refer to\n  patterns and local hypotheses to match against, and applies all of them. Note that this can\n  involve matching later arguments multiple times given earlier arguments, for example\n  `⟨a | b, ⟨c, d⟩⟩` performs the `⟨c, d⟩` match twice, once on the `a` branch and once on `b`.\n-/")]
        []
        []
        []
        [(Command.unsafe "unsafe")]
        [])
       (Command.def
        "def"
        (Command.declId `rcases_core [])
        (Command.optDeclSig
         []
         [(Term.typeSpec
           ":"
           (Term.arrow
            `rcases_patt
            "→"
            (Term.arrow `expr "→" (Term.app `tactic [(Term.app `List [`uncleared_goal])]))))])
        (Command.declValEqns
         (Term.matchAltsWhereDecls
          (Term.matchAlts
           [(Term.matchAlt
             "|"
             [[(Term.app `rcases_patt.one [(Term.quotedName (name "`rfl"))]) "," `e]]
             "=>"
             (Term.do
              "do"
              (Term.doSeqIndent
               [(Term.doSeqItem
                 (Term.doLetArrow
                  "let"
                  []
                  (Term.doPatDecl
                   (Term.tuple "(" [`t "," [`e]] ")")
                   "←"
                   (Term.doExpr (Term.app `get_local_and_type [`e]))
                   []))
                 [])
                (Term.doSeqItem (Term.doExpr (Term.app `subst' [`e])) [])
                (Term.doSeqItem
                 (Term.doExpr
                  («term_<$>_»
                   (Term.app `List.map [(Term.app `Prod.mk [(«term[_]» "[" [] "]")])])
                   "<$>"
                   `get_goals))
                 [])])))
            (Term.matchAlt
             "|"
             [[(Term.app `rcases_patt.one [(Term.hole "_")]) "," (Term.hole "_")]]
             "=>"
             («term_<$>_»
              (Term.app `List.map [(Term.app `Prod.mk [(«term[_]» "[" [] "]")])])
              "<$>"
              `get_goals))
            (Term.matchAlt
             "|"
             [[`rcases_patt.clear "," `e]]
             "=>"
             (Term.do
              "do"
              (Term.doSeqIndent
               [(Term.doSeqItem
                 (Term.doLetArrow
                  "let"
                  []
                  (Term.doIdDecl
                   `m
                   []
                   "←"
                   (Term.doExpr (Term.app `try_core [(Term.app `get_local_and_type [`e])]))))
                 [])
                (Term.doSeqItem
                 (Term.doExpr
                  («term_<$>_»
                   (Term.app
                    `List.map
                    [(«term_<|_»
                      `Prod.mk
                      "<|"
                      (Term.app
                       `m
                       [(«term[_]» "[" [] "]")
                        (Term.fun
                         "fun"
                         (Term.basicFun
                          [(Term.anonymousCtor "⟨" [(Term.hole "_") "," `e] "⟩")]
                          []
                          "=>"
                          («term[_]» "[" [`e] "]")))]))])
                   "<$>"
                   `get_goals))
                 [])])))
            (Term.matchAlt
             "|"
             [[(Term.app `rcases_patt.typed [`p `ty]) "," `e]]
             "=>"
             (Term.do
              "do"
              (Term.doSeqIndent
               [(Term.doSeqItem
                 (Term.doLetArrow
                  "let"
                  []
                  (Term.doPatDecl
                   (Term.tuple "(" [`t "," [`e]] ")")
                   "←"
                   (Term.doExpr (Term.app `get_local_and_type [`e]))
                   []))
                 [])
                (Term.doSeqItem
                 (Term.doLetArrow
                  "let"
                  []
                  (Term.doIdDecl
                   `ty
                   []
                   "←"
                   (Term.doExpr
                    (Term.app
                     `i_to_expr_no_subgoals
                     [(Term.precheckedQuot
                       "`"
                       (Term.quot
                        "`("
                        (Term.typeAscription
                         "("
                         (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `ty ")") [])
                         ":"
                         [(Term.sort "Sort" [(Level.hole "_")])]
                         ")")
                        ")"))]))))
                 [])
                (Term.doSeqItem (Term.doExpr (Term.app `unify [`t `ty])) [])
                (Term.doSeqItem
                 (Term.doLetArrow
                  "let"
                  []
                  (Term.doIdDecl `t [] "←" (Term.doExpr (Term.app `instantiate_mvars [`t]))))
                 [])
                (Term.doSeqItem
                 (Term.doLetArrow
                  "let"
                  []
                  (Term.doIdDecl `ty [] "←" (Term.doExpr (Term.app `instantiate_mvars [`ty]))))
                 [])
                (Term.doSeqItem
                 (Term.doLetArrow
                  "let"
                  []
                  (Term.doIdDecl
                   `e
                   []
                   "←"
                   (Term.doExpr
                    (termIfThenElse
                     "if"
                     («term_==_» `t "==" `ty)
                     "then"
                     (Term.app `pure [`e])
                     "else"
                     («term_>>_»
                      (Term.app `change_core [`ty (Term.app `some [`e])])
                      ">>"
                      (Term.app `get_local [(Term.proj `e "." `local_pp_name)]))))))
                 [])
                (Term.doSeqItem (Term.doExpr (Term.app `rcases_core [`p `e])) [])])))
            (Term.matchAlt
             "|"
             [[(Term.app `rcases_patt.alts [(«term[_]» "[" [`p] "]")]) "," `e]]
             "=>"
             (Term.app `rcases_core [`p `e]))
            (Term.matchAlt
             "|"
             [[`pat "," `e]]
             "=>"
             (Term.do
              "do"
              (Term.doSeqIndent
               [(Term.doSeqItem
                 (Term.doLetArrow
                  "let"
                  []
                  (Term.doPatDecl
                   (Term.tuple "(" [`t "," [`e]] ")")
                   "←"
                   (Term.doExpr (Term.app `get_local_and_type [`e]))
                   []))
                 [])
                (Term.doSeqItem
                 (Term.doLetArrow
                  "let"
                  []
                  (Term.doIdDecl `t [] "←" (Term.doExpr (Term.app `whnf [`t]))))
                 [])
                (Term.doSeqItem
                 (Term.doLetArrow "let" [] (Term.doIdDecl `env [] "←" (Term.doExpr `get_env)))
                 [])
                (Term.doSeqItem
                 (Term.doLet
                  "let"
                  []
                  (Term.letDecl
                   (Term.letIdDecl
                    `I
                    []
                    []
                    ":="
                    (Term.proj (Term.proj `t "." `get_app_fn) "." `const_name))))
                 [])
                (Term.doSeqItem
                 (Term.doLet
                  "let"
                  []
                  (Term.letDecl (Term.letIdDecl `pat [] [] ":=" (Term.proj `pat "." `as_alts))))
                 [])
                (Term.doSeqItem
                 (Term.doLetArrow
                  "let"
                  []
                  (Term.doPatDecl
                   (Term.tuple "(" [`ids "," [`r "," `l]] ")")
                   "←"
                   (Term.doExpr
                    (termIfThenElse
                     "if"
                     («term_≠_» `I "≠" (Term.quotedName (name "`quot")))
                     "then"
                     (Term.do
                      "do"
                      (Term.doSeqIndent
                       [(Term.doSeqItem
                         (Term.doExpr
                          («term_<|_»
                           (Term.app `when [(«term¬_» "¬" (Term.app `env [`I]))])
                           "<|"
                           (Term.app
                            `fail
                            [(Std.termF!_
                              "f!"
                              (interpolatedStrKind
                               (interpolatedStrLitKind "\"rcases tactic failed: {")
                               `e
                               (interpolatedStrLitKind "} : {")
                               `I
                               (interpolatedStrLitKind "} is not an inductive datatype\"")))])))
                         [])
                        (Term.doSeqItem
                         (Term.doLet
                          "let"
                          []
                          (Term.letDecl
                           (Term.letIdDecl
                            `params
                            []
                            []
                            ":="
                            (Term.app (Term.proj `env "." `inductive_num_params) [`I]))))
                         [])
                        (Term.doSeqItem
                         (Term.doLet
                          "let"
                          []
                          (Term.letDecl
                           (Term.letIdDecl
                            `c
                            []
                            []
                            ":="
                            (Term.app (Term.proj `env "." `constructors_of) [`I]))))
                         [])
                        (Term.doSeqItem
                         (Term.doLetArrow
                          "let"
                          []
                          (Term.doPatDecl
                           (Term.tuple "(" [`ids "," [`r]] ")")
                           "←"
                           (Term.doExpr (Term.app `rcases.process_constructors [`params `c `pat]))
                           []))
                         [])
                        (Term.doSeqItem
                         (Term.doLetArrow
                          "let"
                          []
                          (Term.doIdDecl
                           `l
                           []
                           "←"
                           (Term.doExpr (Term.app `cases_core [`e (Term.proj `ids "." `toList)]))))
                         [])
                        (Term.doSeqItem
                         (Term.doExpr
                          (Term.app `pure [(Term.tuple "(" [`ids "," [`r "," `l]] ")")]))
                         [])]))
                     "else"
                     (Term.do
                      "do"
                      (Term.doSeqIndent
                       [(Term.doSeqItem
                         (Term.doLetArrow
                          "let"
                          []
                          (Term.doPatDecl
                           (Term.tuple "(" [`ids "," [`r]] ")")
                           "←"
                           (Term.doExpr
                            (Term.app
                             `rcases.process_constructors
                             [(num "2")
                              («term[_]» "[" [(Term.quotedName (name "`quot.mk"))] "]")
                              `pat]))
                           []))
                         [])
                        (Term.doSeqItem
                         (Term.doLetArrow
                          "let"
                          []
                          (Term.doPatDecl
                           («term[_]» "[" [(Term.tuple "(" [(Term.hole "_") "," [`d]] ")")] "]")
                           "←"
                           (Term.doExpr
                            (Term.app
                             `induction
                             [`e
                              (Term.proj `ids "." `toList)
                              (Term.quotedName (name "`quot.induction_on"))]))
                           ["|"
                            (Term.doSeqIndent
                             [(Term.doSeqItem
                               (Term.doExpr
                                (Term.app
                                 `fail
                                 [(Std.termF!_
                                   "f!"
                                   (interpolatedStrKind
                                    (interpolatedStrLitKind "\"quotient induction on {")
                                    `e
                                    (interpolatedStrLitKind
                                     "} failed. Maybe goal is not in Prop?\"")))]))
                               [])])]))
                         [])
                        (Term.doSeqItem
                         (Term.doExpr
                          (Term.app
                           `pure
                           [(Term.tuple
                             "("
                             [`ids
                              ","
                              [`r
                               ","
                               («term[_]»
                                "["
                                [(Term.tuple
                                  "("
                                  [(Term.quotedName (name "`quot.mk")) "," [`d]]
                                  ")")]
                                "]")]]
                             ")")]))
                         [])]))))
                   []))
                 [])
                (Term.doSeqItem
                 (Term.doLetArrow "let" [] (Term.doIdDecl `gs [] "←" (Term.doExpr `get_goals)))
                 [])
                (Term.doSeqItem
                 (Term.doLet
                  "let"
                  []
                  (Term.letDecl
                   (Term.letIdDecl
                    `ls
                    []
                    []
                    ":="
                    (Term.app
                     `align
                     [(Term.fun
                       "fun"
                       (Term.basicFun
                        [(Term.typeAscription
                          "("
                          (Term.app `a [])
                          ":"
                          [(«term_×_» `Name "×" (Term.hole "_"))]
                          ")")
                         (Term.typeAscription
                          "("
                          (Term.app `b [])
                          ":"
                          [(«term_×_» (Term.hole "_") "×" («term_×_» `Name "×" (Term.hole "_")))]
                          ")")]
                        []
                        "=>"
                        («term_=_»
                         (Term.proj `a "." (fieldIdx "1"))
                         "="
                         (Term.proj (Term.proj `b "." (fieldIdx "2")) "." (fieldIdx "1")))))
                      `r
                      (Term.app (Term.proj `gs "." `zip) [`l])]))))
                 [])
                (Term.doSeqItem
                 (Term.doExpr
                  («term_<$>_»
                   `List.join
                   "<$>"
                   (Term.app
                    `ls
                    [(Term.fun
                      "fun"
                      (Term.basicFun
                       [(Term.anonymousCtor
                         "⟨"
                         [(Term.anonymousCtor "⟨" [(Term.hole "_") "," `ps] "⟩")
                          ","
                          `g
                          ","
                          (Term.hole "_")
                          ","
                          `hs
                          ","
                          (Term.hole "_")]
                         "⟩")]
                       []
                       "=>"
                       («term_>>_»
                        (Term.app `set_goals [(«term[_]» "[" [`g] "]")])
                        ">>"
                        (Term.app `rcases.continue [(Term.app `ps [`hs])]))))])))
                 [])])))])
          []))
        []
        []
        []))
      (Command.declaration
       (Command.declModifiers
        [(Command.docComment
          "/--"
          "* `rcases_core p e` will match a pattern `p` against a local hypothesis `e`.\n  It returns the list of subgoals that were produced.\n* `rcases.continue pes` will match a (conjunctive) list of `(p, e)` pairs which refer to\n  patterns and local hypotheses to match against, and applies all of them. Note that this can\n  involve matching later arguments multiple times given earlier arguments, for example\n  `⟨a | b, ⟨c, d⟩⟩` performs the `⟨c, d⟩` match twice, once on the `a` branch and once on `b`.\n-/")]
        []
        []
        []
        [(Command.unsafe "unsafe")]
        [])
       (Command.def
        "def"
        (Command.declId `rcases.continue [])
        (Command.optDeclSig
         []
         [(Term.typeSpec
           ":"
           (Term.arrow
            (Term.app
             (Tactic.Tactic.Rcases.«termlistΠ» "listΠ")
             [(«term_×_» `rcases_patt "×" `expr)])
            "→"
            (Term.app `tactic [(Term.app `List [`uncleared_goal])])))])
        (Command.declValEqns
         (Term.matchAltsWhereDecls
          (Term.matchAlts
           [(Term.matchAlt
             "|"
             [[(«term[_]» "[" [] "]")]]
             "=>"
             («term_<$>_»
              (Term.app `List.map [(Term.app `Prod.mk [(«term[_]» "[" [] "]")])])
              "<$>"
              `get_goals))
            (Term.matchAlt
             "|"
             [[(«term_::_» (Term.tuple "(" [`pat "," [`e]] ")") "::" `pes)]]
             "=>"
             (Term.do
              "do"
              (Term.doSeqIndent
               [(Term.doSeqItem
                 (Term.doLetArrow
                  "let"
                  []
                  (Term.doIdDecl `gs [] "←" (Term.doExpr (Term.app `rcases_core [`pat `e]))))
                 [])
                (Term.doSeqItem
                 (Term.doExpr
                  («term_<$>_»
                   `List.join
                   "<$>"
                   (Term.app
                    `gs
                    [(Term.fun
                      "fun"
                      (Term.basicFun
                       [(Term.anonymousCtor "⟨" [`cs "," `g] "⟩")]
                       []
                       "=>"
                       (Term.do
                        "do"
                        (Term.doSeqIndent
                         [(Term.doSeqItem
                           (Term.doExpr (Term.app `set_goals [(«term[_]» "[" [`g] "]")]))
                           [])
                          (Term.doSeqItem
                           (Term.doLetArrow
                            "let"
                            []
                            (Term.doIdDecl
                             `ugs
                             []
                             "←"
                             (Term.doExpr (Term.app `rcases.continue [`pes]))))
                           [])
                          (Term.doSeqItem
                           (Term.doExpr
                            («term_<|_»
                             `pure
                             "<|"
                             (Term.app
                              `ugs
                              [(Term.fun
                                "fun"
                                (Term.basicFun
                                 [(Term.anonymousCtor "⟨" [`cs' "," `gs] "⟩")]
                                 []
                                 "=>"
                                 (Term.tuple "(" [(«term_++_» `cs "++" `cs') "," [`gs]] ")")))])))
                           [])]))))])))
                 [])])))])
          []))
        []
        []
        []))]
     "end"
     []
     [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValEqns', expected 'Lean.Parser.Command.declValSimple'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.do
       "do"
       (Term.doSeqIndent
        [(Term.doSeqItem
          (Term.doLetArrow
           "let"
           []
           (Term.doIdDecl `gs [] "←" (Term.doExpr (Term.app `rcases_core [`pat `e]))))
          [])
         (Term.doSeqItem
          (Term.doExpr
           («term_<$>_»
            `List.join
            "<$>"
            (Term.app
             `gs
             [(Term.fun
               "fun"
               (Term.basicFun
                [(Term.anonymousCtor "⟨" [`cs "," `g] "⟩")]
                []
                "=>"
                (Term.do
                 "do"
                 (Term.doSeqIndent
                  [(Term.doSeqItem
                    (Term.doExpr (Term.app `set_goals [(«term[_]» "[" [`g] "]")]))
                    [])
                   (Term.doSeqItem
                    (Term.doLetArrow
                     "let"
                     []
                     (Term.doIdDecl `ugs [] "←" (Term.doExpr (Term.app `rcases.continue [`pes]))))
                    [])
                   (Term.doSeqItem
                    (Term.doExpr
                     («term_<|_»
                      `pure
                      "<|"
                      (Term.app
                       `ugs
                       [(Term.fun
                         "fun"
                         (Term.basicFun
                          [(Term.anonymousCtor "⟨" [`cs' "," `gs] "⟩")]
                          []
                          "=>"
                          (Term.tuple "(" [(«term_++_» `cs "++" `cs') "," [`gs]] ")")))])))
                    [])]))))])))
          [])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doSeqIndent', expected 'Lean.Parser.Term.doSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<$>_»
       `List.join
       "<$>"
       (Term.app
        `gs
        [(Term.fun
          "fun"
          (Term.basicFun
           [(Term.anonymousCtor "⟨" [`cs "," `g] "⟩")]
           []
           "=>"
           (Term.do
            "do"
            (Term.doSeqIndent
             [(Term.doSeqItem (Term.doExpr (Term.app `set_goals [(«term[_]» "[" [`g] "]")])) [])
              (Term.doSeqItem
               (Term.doLetArrow
                "let"
                []
                (Term.doIdDecl `ugs [] "←" (Term.doExpr (Term.app `rcases.continue [`pes]))))
               [])
              (Term.doSeqItem
               (Term.doExpr
                («term_<|_»
                 `pure
                 "<|"
                 (Term.app
                  `ugs
                  [(Term.fun
                    "fun"
                    (Term.basicFun
                     [(Term.anonymousCtor "⟨" [`cs' "," `gs] "⟩")]
                     []
                     "=>"
                     (Term.tuple "(" [(«term_++_» `cs "++" `cs') "," [`gs]] ")")))])))
               [])]))))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `gs
       [(Term.fun
         "fun"
         (Term.basicFun
          [(Term.anonymousCtor "⟨" [`cs "," `g] "⟩")]
          []
          "=>"
          (Term.do
           "do"
           (Term.doSeqIndent
            [(Term.doSeqItem (Term.doExpr (Term.app `set_goals [(«term[_]» "[" [`g] "]")])) [])
             (Term.doSeqItem
              (Term.doLetArrow
               "let"
               []
               (Term.doIdDecl `ugs [] "←" (Term.doExpr (Term.app `rcases.continue [`pes]))))
              [])
             (Term.doSeqItem
              (Term.doExpr
               («term_<|_»
                `pure
                "<|"
                (Term.app
                 `ugs
                 [(Term.fun
                   "fun"
                   (Term.basicFun
                    [(Term.anonymousCtor "⟨" [`cs' "," `gs] "⟩")]
                    []
                    "=>"
                    (Term.tuple "(" [(«term_++_» `cs "++" `cs') "," [`gs]] ")")))])))
              [])]))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [(Term.anonymousCtor "⟨" [`cs "," `g] "⟩")]
        []
        "=>"
        (Term.do
         "do"
         (Term.doSeqIndent
          [(Term.doSeqItem (Term.doExpr (Term.app `set_goals [(«term[_]» "[" [`g] "]")])) [])
           (Term.doSeqItem
            (Term.doLetArrow
             "let"
             []
             (Term.doIdDecl `ugs [] "←" (Term.doExpr (Term.app `rcases.continue [`pes]))))
            [])
           (Term.doSeqItem
            (Term.doExpr
             («term_<|_»
              `pure
              "<|"
              (Term.app
               `ugs
               [(Term.fun
                 "fun"
                 (Term.basicFun
                  [(Term.anonymousCtor "⟨" [`cs' "," `gs] "⟩")]
                  []
                  "=>"
                  (Term.tuple "(" [(«term_++_» `cs "++" `cs') "," [`gs]] ")")))])))
            [])]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.do
       "do"
       (Term.doSeqIndent
        [(Term.doSeqItem (Term.doExpr (Term.app `set_goals [(«term[_]» "[" [`g] "]")])) [])
         (Term.doSeqItem
          (Term.doLetArrow
           "let"
           []
           (Term.doIdDecl `ugs [] "←" (Term.doExpr (Term.app `rcases.continue [`pes]))))
          [])
         (Term.doSeqItem
          (Term.doExpr
           («term_<|_»
            `pure
            "<|"
            (Term.app
             `ugs
             [(Term.fun
               "fun"
               (Term.basicFun
                [(Term.anonymousCtor "⟨" [`cs' "," `gs] "⟩")]
                []
                "=>"
                (Term.tuple "(" [(«term_++_» `cs "++" `cs') "," [`gs]] ")")))])))
          [])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doSeqIndent', expected 'Lean.Parser.Term.doSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_»
       `pure
       "<|"
       (Term.app
        `ugs
        [(Term.fun
          "fun"
          (Term.basicFun
           [(Term.anonymousCtor "⟨" [`cs' "," `gs] "⟩")]
           []
           "=>"
           (Term.tuple "(" [(«term_++_» `cs "++" `cs') "," [`gs]] ")")))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `ugs
       [(Term.fun
         "fun"
         (Term.basicFun
          [(Term.anonymousCtor "⟨" [`cs' "," `gs] "⟩")]
          []
          "=>"
          (Term.tuple "(" [(«term_++_» `cs "++" `cs') "," [`gs]] ")")))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [(Term.anonymousCtor "⟨" [`cs' "," `gs] "⟩")]
        []
        "=>"
        (Term.tuple "(" [(«term_++_» `cs "++" `cs') "," [`gs]] ")")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.tuple "(" [(«term_++_» `cs "++" `cs') "," [`gs]] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `gs
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_++_» `cs "++" `cs')
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `cs'
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `cs
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [`cs' "," `gs] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `gs
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `cs'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `ugs
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      `pure
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, doElem))
      (Term.app `rcases.continue [`pes])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `pes
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `rcases.continue
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, doElem)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, doElem))
      (Term.app `set_goals [(«term[_]» "[" [`g] "]")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term[_]»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term[_]»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term[_]» "[" [`g] "]")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `set_goals
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1023, doElem)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1023, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [`cs "," `g] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `cs
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `gs
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 100 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 100, term))
      `List.join
[PrettyPrinter.parenthesize] ...precedences are 101 >? 1024, (none,
     [anonymous]) <=? (some 100, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 100, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, doElem))
      (Term.app `rcases_core [`pat `e])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `e
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `pat
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `rcases_core
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, doElem)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1023, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_::_» (Term.tuple "(" [`pat "," [`e]] ")") "::" `pes)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `pes
[PrettyPrinter.parenthesize] ...precedences are 67 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 67, term))
      (Term.tuple "(" [`pat "," [`e]] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `e
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `pat
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 68 >? 1024, (none, [anonymous]) <=? (some 67, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 67, (some 67, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_<$>_»
       (Term.app `List.map [(Term.app `Prod.mk [(«term[_]» "[" [] "]")])])
       "<$>"
       `get_goals)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `get_goals
[PrettyPrinter.parenthesize] ...precedences are 100 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 100, term))
      (Term.app `List.map [(Term.app `Prod.mk [(«term[_]» "[" [] "]")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Prod.mk [(«term[_]» "[" [] "]")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term[_]»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term[_]»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term[_]» "[" [] "]")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Prod.mk
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `Prod.mk [(«term[_]» "[" [] "]")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `List.map
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 101 >? 1022, (some 1023, term) <=? (some 100, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 100, (some 100,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term[_]» "[" [] "]")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.arrow
       (Term.app (Tactic.Tactic.Rcases.«termlistΠ» "listΠ") [(«term_×_» `rcases_patt "×" `expr)])
       "→"
       (Term.app `tactic [(Term.app `List [`uncleared_goal])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `tactic [(Term.app `List [`uncleared_goal])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `List [`uncleared_goal])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `uncleared_goal
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `List
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `List [`uncleared_goal]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `tactic
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 25 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
      (Term.app (Tactic.Tactic.Rcases.«termlistΠ» "listΠ") [(«term_×_» `rcases_patt "×" `expr)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_×_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_×_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_×_» `rcases_patt "×" `expr)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `expr
[PrettyPrinter.parenthesize] ...precedences are 35 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 35, term))
      `rcases_patt
[PrettyPrinter.parenthesize] ...precedences are 36 >? 1024, (none, [anonymous]) <=? (some 35, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 35, (some 35, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_×_» `rcases_patt "×" `expr) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Tactic.Tactic.Rcases.«termlistΠ» "listΠ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Tactic.Tactic.Rcases.«termlistΠ»', expected 'Tactic.Tactic.Rcases.termlistΠ._@.Tactic.Rcases._hyg.324'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
mutual
  /--
          * `rcases_core p e` will match a pattern `p` against a local hypothesis `e`.
            It returns the list of subgoals that were produced.
          * `rcases.continue pes` will match a (conjunctive) list of `(p, e)` pairs which refer to
            patterns and local hypotheses to match against, and applies all of them. Note that this can
            involve matching later arguments multiple times given earlier arguments, for example
            `⟨a | b, ⟨c, d⟩⟩` performs the `⟨c, d⟩` match twice, once on the `a` branch and once on `b`.
          -/
        unsafe
      def
        rcases_core
        : rcases_patt → expr → tactic List uncleared_goal
        |
            rcases_patt.one `rfl , e
            =>
            do let ( t , e ) ← get_local_and_type e subst' e List.map Prod.mk [ ] <$> get_goals
          | rcases_patt.one _ , _ => List.map Prod.mk [ ] <$> get_goals
          |
            rcases_patt.clear , e
            =>
            do
              let m ← try_core get_local_and_type e
                List.map Prod.mk <| m [ ] fun ⟨ _ , e ⟩ => [ e ] <$> get_goals
          |
            rcases_patt.typed p ty , e
            =>
            do
              let ( t , e ) ← get_local_and_type e
                let ty ← i_to_expr_no_subgoals ` `( ( $ ( ty ) : Sort _ ) )
                unify t ty
                let t ← instantiate_mvars t
                let ty ← instantiate_mvars ty
                let
                  e
                    ←
                    if t == ty then pure e else change_core ty some e >> get_local e . local_pp_name
                rcases_core p e
          | rcases_patt.alts [ p ] , e => rcases_core p e
          |
            pat , e
            =>
            do
              let ( t , e ) ← get_local_and_type e
                let t ← whnf t
                let env ← get_env
                let I := t . get_app_fn . const_name
                let pat := pat . as_alts
                let
                  ( ids , r , l )
                    ←
                    if
                      I ≠ `quot
                      then
                      do
                        when ¬ env I
                            <|
                            fail
                              f! "rcases tactic failed: { e } : { I } is not an inductive datatype"
                          let params := env . inductive_num_params I
                          let c := env . constructors_of I
                          let ( ids , r ) ← rcases.process_constructors params c pat
                          let l ← cases_core e ids . toList
                          pure ( ids , r , l )
                      else
                      do
                        let ( ids , r ) ← rcases.process_constructors 2 [ `quot.mk ] pat
                          let
                            [ ( _ , d ) ]
                              ←
                              induction e ids . toList `quot.induction_on
                              |
                                fail
                                  f!
                                    "quotient induction on { e } failed. Maybe goal is not in Prop?"
                          pure ( ids , r , [ ( `quot.mk , d ) ] )
                let gs ← get_goals
                let
                  ls
                    :=
                    align
                      fun ( a : Name × _ ) ( b : _ × Name × _ ) => a . 1 = b . 2 . 1 r gs . zip l
                List.join
                  <$>
                  ls fun ⟨ ⟨ _ , ps ⟩ , g , _ , hs , _ ⟩ => set_goals [ g ] >> rcases.continue ps hs
    /--
          * `rcases_core p e` will match a pattern `p` against a local hypothesis `e`.
            It returns the list of subgoals that were produced.
          * `rcases.continue pes` will match a (conjunctive) list of `(p, e)` pairs which refer to
            patterns and local hypotheses to match against, and applies all of them. Note that this can
            involve matching later arguments multiple times given earlier arguments, for example
            `⟨a | b, ⟨c, d⟩⟩` performs the `⟨c, d⟩` match twice, once on the `a` branch and once on `b`.
          -/
        unsafe
      def
        rcases.continue
        : listΠ rcases_patt × expr → tactic List uncleared_goal
        | [ ] => List.map Prod.mk [ ] <$> get_goals
          |
            ( pat , e ) :: pes
            =>
            do
              let gs ← rcases_core pat e
                List.join
                  <$>
                  gs
                    fun
                      ⟨ cs , g ⟩
                        =>
                        do
                          set_goals [ g ]
                            let ugs ← rcases.continue pes
                            pure <| ugs fun ⟨ cs' , gs ⟩ => ( cs ++ cs' , gs )
  end
#align tactic.rcases_core tactic.rcases_core
#align tactic.rcases.continue tactic.rcases.continue

/-- Given a list of `uncleared_goal`s, each of which is a goal metavariable and
a list of variables to clear, actually perform the clear and set the goals with the result. -/
unsafe def clear_goals (ugs : List uncleared_goal) : tactic Unit := do
  let gs ←
    ugs.mmap fun ⟨cs, g⟩ => do
        set_goals [g]
        let cs ←
          cs.mfoldr
              (fun c cs =>
                (do
                    let (_, c) ← get_local_and_type c
                    pure (c :: cs)) <|>
                  pure cs)
              []
        clear' tt cs
        let [g] ← get_goals
        pure g
  set_goals gs
#align tactic.clear_goals tactic.clear_goals

/-- `rcases h e pat` performs case distinction on `e` using `pat` to
name the arising new variables and assumptions. If `h` is `some` name,
a new assumption `h : e = pat` will relate the expression `e` with the
current pattern. See the module comment for the syntax of `pat`. -/
unsafe def rcases (h : Option Name) (p : pexpr) (pat : rcases_patt) : tactic Unit := do
  let p :=
    match pat with
    | rcases_patt.typed _ ty => ``(($(p) : $(ty)))
    | _ => p
  let e ←
    match h with
      | some h => do
        let x ← get_unused_name <| pat.Name.getOrElse `this
        interactive.generalize h () (p, x)
        get_local x
      | none => i_to_expr p
  if e then
      match pat with
      | some x => do
        let n ← revert e
        let e ← intro x
        intron (n - 1)
        focus1 (rcases_core pat e >>= clear_goals)
      | none => focus1 (rcases_core pat e >>= clear_goals)
    else do
      let x ← pat mk_fresh_name pure
      let n ← revert_kdependencies e semireducible
      tactic.generalize e x <|> do
          let t ← infer_type e
          tactic.assertv x t e
          get_local x >>= tactic.revert
          pure ()
      let h ← tactic.intro1
      focus1 (rcases_core pat h >>= clear_goals)
#align tactic.rcases tactic.rcases

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "`rcases_many es pats` performs case distinction on the `es` using `pat` to\nname the arising new variables and assumptions.\nSee the module comment for the syntax of `pat`. -/")]
      []
      []
      []
      [(Command.unsafe "unsafe")]
      [])
     (Command.def
      "def"
      (Command.declId `rcases_many [])
      (Command.optDeclSig
       [(Term.explicitBinder
         "("
         [`ps]
         [":" (Term.app (Tactic.Tactic.Rcases.«termlistΠ» "listΠ") [`pexpr])]
         []
         ")")
        (Term.explicitBinder "(" [`pat] [":" `rcases_patt] [] ")")]
       [(Term.typeSpec ":" (Term.app `tactic [`Unit]))])
      (Command.declValSimple
       ":="
       (Term.do
        "do"
        (Term.doSeqIndent
         [(Term.doSeqItem
           (Term.doLet
            "let"
            []
            (Term.letDecl
             (Term.letPatDecl
              (Term.tuple "(" [(Term.hole "_") "," [`pats]] ")")
              []
              []
              ":="
              (Term.app
               `rcases.process_constructor
               [`false
                (Term.app
                 (Term.proj `ps "." `map)
                 [(Term.fun "fun" (Term.basicFun [(Term.hole "_")] [] "=>" `default))])
                (Term.proj (Term.proj `pat "." `as_tuple) "." (fieldIdx "2"))]))))
           [])
          (Term.doSeqItem
           (Term.doLetArrow
            "let"
            []
            (Term.doIdDecl
             `pes
             []
             "←"
             (Term.doExpr
              (Term.app
               (Term.proj (Term.app (Term.proj `ps "." `zip) [`pats]) "." `mmap)
               [(Term.fun
                 "fun"
                 (Term.basicFun
                  [(Term.anonymousCtor "⟨" [`p "," `pat] "⟩")]
                  []
                  "=>"
                  (Term.do
                   "do"
                   (Term.doSeqIndent
                    [(Term.doSeqItem
                      (Term.doLet
                       "let"
                       []
                       (Term.letDecl
                        (Term.letIdDecl
                         `p
                         []
                         []
                         ":="
                         (Term.match
                          "match"
                          []
                          []
                          [(Term.matchDiscr [] `pat)]
                          "with"
                          (Term.matchAlts
                           [(Term.matchAlt
                             "|"
                             [[(Term.app `rcases_patt.typed [(Term.hole "_") `ty])]]
                             "=>"
                             (Term.precheckedQuot
                              "`"
                              (Term.quot
                               "`("
                               (Term.typeAscription
                                "("
                                (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `p ")") [])
                                ":"
                                [(term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `ty ")") [])]
                                ")")
                               ")")))
                            (Term.matchAlt "|" [[(Term.hole "_")]] "=>" `p)])))))
                      [])
                     (Term.doSeqItem
                      (Term.doLetArrow
                       "let"
                       []
                       (Term.doIdDecl `e [] "←" (Term.doExpr (Term.app `i_to_expr [`p]))))
                      [])
                     (Term.doSeqItem
                      (Term.doExpr
                       (termIfThenElse
                        "if"
                        `e
                        "then"
                        (Term.match
                         "match"
                         []
                         []
                         [(Term.matchDiscr [] `pat)]
                         "with"
                         (Term.matchAlts
                          [(Term.matchAlt
                            "|"
                            [[(Term.app `some [`x])]]
                            "=>"
                            (Term.do
                             "do"
                             (Term.doSeqIndent
                              [(Term.doSeqItem
                                (Term.doLetArrow
                                 "let"
                                 []
                                 (Term.doIdDecl `n [] "←" (Term.doExpr (Term.app `revert [`e]))))
                                [])
                               (Term.doSeqItem
                                (Term.doLetArrow
                                 "let"
                                 []
                                 (Term.doIdDecl `e [] "←" (Term.doExpr (Term.app `intro [`x]))))
                                [])
                               (Term.doSeqItem
                                (Term.doExpr (Term.app `intron [(«term_-_» `n "-" (num "1"))]))
                                [])
                               (Term.doSeqItem
                                (Term.doExpr
                                 (Term.app `pure [(Term.tuple "(" [`pat "," [`e]] ")")]))
                                [])])))
                           (Term.matchAlt
                            "|"
                            [[`none]]
                            "=>"
                            (Term.app `pure [(Term.tuple "(" [`pat "," [`e]] ")")]))]))
                        "else"
                        (Term.do
                         "do"
                         (Term.doSeqIndent
                          [(Term.doSeqItem
                            (Term.doLetArrow
                             "let"
                             []
                             (Term.doIdDecl
                              `x
                              []
                              "←"
                              (Term.doExpr (Term.app `pat [`mk_fresh_name `pure]))))
                            [])
                           (Term.doSeqItem
                            (Term.doLetArrow
                             "let"
                             []
                             (Term.doIdDecl
                              `n
                              []
                              "←"
                              (Term.doExpr (Term.app `revert_kdependencies [`e `semireducible]))))
                            [])
                           (Term.doSeqItem
                            (Term.doExpr
                             («term_<|>_»
                              (Term.app `tactic.generalize [`e `x])
                              "<|>"
                              (Term.do
                               "do"
                               (Term.doSeqIndent
                                [(Term.doSeqItem
                                  (Term.doLetArrow
                                   "let"
                                   []
                                   (Term.doIdDecl
                                    `t
                                    []
                                    "←"
                                    (Term.doExpr (Term.app `infer_type [`e]))))
                                  [])
                                 (Term.doSeqItem
                                  (Term.doExpr (Term.app `tactic.assertv [`x `t `e]))
                                  [])
                                 (Term.doSeqItem
                                  (Term.doExpr
                                   («term_>>=_» (Term.app `get_local [`x]) ">>=" `tactic.revert))
                                  [])
                                 (Term.doSeqItem
                                  (Term.doExpr (Term.app `pure [(Term.tuple "(" [] ")")]))
                                  [])]))))
                            [])
                           (Term.doSeqItem
                            (Term.doExpr
                             («term_<$>_» (Term.app `Prod.mk [`pat]) "<$>" `tactic.intro1))
                            [])]))))
                      [])]))))]))))
           [])
          (Term.doSeqItem
           (Term.doExpr
            (Term.app
             `focus1
             [(«term_>>=_» (Term.app `rcases.continue [`pes]) ">>=" `clear_goals)]))
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
          (Term.doLet
           "let"
           []
           (Term.letDecl
            (Term.letPatDecl
             (Term.tuple "(" [(Term.hole "_") "," [`pats]] ")")
             []
             []
             ":="
             (Term.app
              `rcases.process_constructor
              [`false
               (Term.app
                (Term.proj `ps "." `map)
                [(Term.fun "fun" (Term.basicFun [(Term.hole "_")] [] "=>" `default))])
               (Term.proj (Term.proj `pat "." `as_tuple) "." (fieldIdx "2"))]))))
          [])
         (Term.doSeqItem
          (Term.doLetArrow
           "let"
           []
           (Term.doIdDecl
            `pes
            []
            "←"
            (Term.doExpr
             (Term.app
              (Term.proj (Term.app (Term.proj `ps "." `zip) [`pats]) "." `mmap)
              [(Term.fun
                "fun"
                (Term.basicFun
                 [(Term.anonymousCtor "⟨" [`p "," `pat] "⟩")]
                 []
                 "=>"
                 (Term.do
                  "do"
                  (Term.doSeqIndent
                   [(Term.doSeqItem
                     (Term.doLet
                      "let"
                      []
                      (Term.letDecl
                       (Term.letIdDecl
                        `p
                        []
                        []
                        ":="
                        (Term.match
                         "match"
                         []
                         []
                         [(Term.matchDiscr [] `pat)]
                         "with"
                         (Term.matchAlts
                          [(Term.matchAlt
                            "|"
                            [[(Term.app `rcases_patt.typed [(Term.hole "_") `ty])]]
                            "=>"
                            (Term.precheckedQuot
                             "`"
                             (Term.quot
                              "`("
                              (Term.typeAscription
                               "("
                               (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `p ")") [])
                               ":"
                               [(term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `ty ")") [])]
                               ")")
                              ")")))
                           (Term.matchAlt "|" [[(Term.hole "_")]] "=>" `p)])))))
                     [])
                    (Term.doSeqItem
                     (Term.doLetArrow
                      "let"
                      []
                      (Term.doIdDecl `e [] "←" (Term.doExpr (Term.app `i_to_expr [`p]))))
                     [])
                    (Term.doSeqItem
                     (Term.doExpr
                      (termIfThenElse
                       "if"
                       `e
                       "then"
                       (Term.match
                        "match"
                        []
                        []
                        [(Term.matchDiscr [] `pat)]
                        "with"
                        (Term.matchAlts
                         [(Term.matchAlt
                           "|"
                           [[(Term.app `some [`x])]]
                           "=>"
                           (Term.do
                            "do"
                            (Term.doSeqIndent
                             [(Term.doSeqItem
                               (Term.doLetArrow
                                "let"
                                []
                                (Term.doIdDecl `n [] "←" (Term.doExpr (Term.app `revert [`e]))))
                               [])
                              (Term.doSeqItem
                               (Term.doLetArrow
                                "let"
                                []
                                (Term.doIdDecl `e [] "←" (Term.doExpr (Term.app `intro [`x]))))
                               [])
                              (Term.doSeqItem
                               (Term.doExpr (Term.app `intron [(«term_-_» `n "-" (num "1"))]))
                               [])
                              (Term.doSeqItem
                               (Term.doExpr (Term.app `pure [(Term.tuple "(" [`pat "," [`e]] ")")]))
                               [])])))
                          (Term.matchAlt
                           "|"
                           [[`none]]
                           "=>"
                           (Term.app `pure [(Term.tuple "(" [`pat "," [`e]] ")")]))]))
                       "else"
                       (Term.do
                        "do"
                        (Term.doSeqIndent
                         [(Term.doSeqItem
                           (Term.doLetArrow
                            "let"
                            []
                            (Term.doIdDecl
                             `x
                             []
                             "←"
                             (Term.doExpr (Term.app `pat [`mk_fresh_name `pure]))))
                           [])
                          (Term.doSeqItem
                           (Term.doLetArrow
                            "let"
                            []
                            (Term.doIdDecl
                             `n
                             []
                             "←"
                             (Term.doExpr (Term.app `revert_kdependencies [`e `semireducible]))))
                           [])
                          (Term.doSeqItem
                           (Term.doExpr
                            («term_<|>_»
                             (Term.app `tactic.generalize [`e `x])
                             "<|>"
                             (Term.do
                              "do"
                              (Term.doSeqIndent
                               [(Term.doSeqItem
                                 (Term.doLetArrow
                                  "let"
                                  []
                                  (Term.doIdDecl
                                   `t
                                   []
                                   "←"
                                   (Term.doExpr (Term.app `infer_type [`e]))))
                                 [])
                                (Term.doSeqItem
                                 (Term.doExpr (Term.app `tactic.assertv [`x `t `e]))
                                 [])
                                (Term.doSeqItem
                                 (Term.doExpr
                                  («term_>>=_» (Term.app `get_local [`x]) ">>=" `tactic.revert))
                                 [])
                                (Term.doSeqItem
                                 (Term.doExpr (Term.app `pure [(Term.tuple "(" [] ")")]))
                                 [])]))))
                           [])
                          (Term.doSeqItem
                           (Term.doExpr
                            («term_<$>_» (Term.app `Prod.mk [`pat]) "<$>" `tactic.intro1))
                           [])]))))
                     [])]))))]))))
          [])
         (Term.doSeqItem
          (Term.doExpr
           (Term.app `focus1 [(«term_>>=_» (Term.app `rcases.continue [`pes]) ">>=" `clear_goals)]))
          [])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doSeqIndent', expected 'Lean.Parser.Term.doSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `focus1 [(«term_>>=_» (Term.app `rcases.continue [`pes]) ">>=" `clear_goals)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_>>=_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_>>=_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_>>=_» (Term.app `rcases.continue [`pes]) ">>=" `clear_goals)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `clear_goals
[PrettyPrinter.parenthesize] ...precedences are 56 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 55, term))
      (Term.app `rcases.continue [`pes])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `pes
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `rcases.continue
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 55 >? 1022, (some 1023, term) <=? (some 55, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 55, (some 56, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_>>=_» (Term.app `rcases.continue [`pes]) ">>=" `clear_goals)
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `focus1
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, doElem))
      (Term.app
       (Term.proj (Term.app (Term.proj `ps "." `zip) [`pats]) "." `mmap)
       [(Term.fun
         "fun"
         (Term.basicFun
          [(Term.anonymousCtor "⟨" [`p "," `pat] "⟩")]
          []
          "=>"
          (Term.do
           "do"
           (Term.doSeqIndent
            [(Term.doSeqItem
              (Term.doLet
               "let"
               []
               (Term.letDecl
                (Term.letIdDecl
                 `p
                 []
                 []
                 ":="
                 (Term.match
                  "match"
                  []
                  []
                  [(Term.matchDiscr [] `pat)]
                  "with"
                  (Term.matchAlts
                   [(Term.matchAlt
                     "|"
                     [[(Term.app `rcases_patt.typed [(Term.hole "_") `ty])]]
                     "=>"
                     (Term.precheckedQuot
                      "`"
                      (Term.quot
                       "`("
                       (Term.typeAscription
                        "("
                        (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `p ")") [])
                        ":"
                        [(term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `ty ")") [])]
                        ")")
                       ")")))
                    (Term.matchAlt "|" [[(Term.hole "_")]] "=>" `p)])))))
              [])
             (Term.doSeqItem
              (Term.doLetArrow
               "let"
               []
               (Term.doIdDecl `e [] "←" (Term.doExpr (Term.app `i_to_expr [`p]))))
              [])
             (Term.doSeqItem
              (Term.doExpr
               (termIfThenElse
                "if"
                `e
                "then"
                (Term.match
                 "match"
                 []
                 []
                 [(Term.matchDiscr [] `pat)]
                 "with"
                 (Term.matchAlts
                  [(Term.matchAlt
                    "|"
                    [[(Term.app `some [`x])]]
                    "=>"
                    (Term.do
                     "do"
                     (Term.doSeqIndent
                      [(Term.doSeqItem
                        (Term.doLetArrow
                         "let"
                         []
                         (Term.doIdDecl `n [] "←" (Term.doExpr (Term.app `revert [`e]))))
                        [])
                       (Term.doSeqItem
                        (Term.doLetArrow
                         "let"
                         []
                         (Term.doIdDecl `e [] "←" (Term.doExpr (Term.app `intro [`x]))))
                        [])
                       (Term.doSeqItem
                        (Term.doExpr (Term.app `intron [(«term_-_» `n "-" (num "1"))]))
                        [])
                       (Term.doSeqItem
                        (Term.doExpr (Term.app `pure [(Term.tuple "(" [`pat "," [`e]] ")")]))
                        [])])))
                   (Term.matchAlt
                    "|"
                    [[`none]]
                    "=>"
                    (Term.app `pure [(Term.tuple "(" [`pat "," [`e]] ")")]))]))
                "else"
                (Term.do
                 "do"
                 (Term.doSeqIndent
                  [(Term.doSeqItem
                    (Term.doLetArrow
                     "let"
                     []
                     (Term.doIdDecl `x [] "←" (Term.doExpr (Term.app `pat [`mk_fresh_name `pure]))))
                    [])
                   (Term.doSeqItem
                    (Term.doLetArrow
                     "let"
                     []
                     (Term.doIdDecl
                      `n
                      []
                      "←"
                      (Term.doExpr (Term.app `revert_kdependencies [`e `semireducible]))))
                    [])
                   (Term.doSeqItem
                    (Term.doExpr
                     («term_<|>_»
                      (Term.app `tactic.generalize [`e `x])
                      "<|>"
                      (Term.do
                       "do"
                       (Term.doSeqIndent
                        [(Term.doSeqItem
                          (Term.doLetArrow
                           "let"
                           []
                           (Term.doIdDecl `t [] "←" (Term.doExpr (Term.app `infer_type [`e]))))
                          [])
                         (Term.doSeqItem (Term.doExpr (Term.app `tactic.assertv [`x `t `e])) [])
                         (Term.doSeqItem
                          (Term.doExpr
                           («term_>>=_» (Term.app `get_local [`x]) ">>=" `tactic.revert))
                          [])
                         (Term.doSeqItem
                          (Term.doExpr (Term.app `pure [(Term.tuple "(" [] ")")]))
                          [])]))))
                    [])
                   (Term.doSeqItem
                    (Term.doExpr («term_<$>_» (Term.app `Prod.mk [`pat]) "<$>" `tactic.intro1))
                    [])]))))
              [])]))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [(Term.anonymousCtor "⟨" [`p "," `pat] "⟩")]
        []
        "=>"
        (Term.do
         "do"
         (Term.doSeqIndent
          [(Term.doSeqItem
            (Term.doLet
             "let"
             []
             (Term.letDecl
              (Term.letIdDecl
               `p
               []
               []
               ":="
               (Term.match
                "match"
                []
                []
                [(Term.matchDiscr [] `pat)]
                "with"
                (Term.matchAlts
                 [(Term.matchAlt
                   "|"
                   [[(Term.app `rcases_patt.typed [(Term.hole "_") `ty])]]
                   "=>"
                   (Term.precheckedQuot
                    "`"
                    (Term.quot
                     "`("
                     (Term.typeAscription
                      "("
                      (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `p ")") [])
                      ":"
                      [(term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `ty ")") [])]
                      ")")
                     ")")))
                  (Term.matchAlt "|" [[(Term.hole "_")]] "=>" `p)])))))
            [])
           (Term.doSeqItem
            (Term.doLetArrow
             "let"
             []
             (Term.doIdDecl `e [] "←" (Term.doExpr (Term.app `i_to_expr [`p]))))
            [])
           (Term.doSeqItem
            (Term.doExpr
             (termIfThenElse
              "if"
              `e
              "then"
              (Term.match
               "match"
               []
               []
               [(Term.matchDiscr [] `pat)]
               "with"
               (Term.matchAlts
                [(Term.matchAlt
                  "|"
                  [[(Term.app `some [`x])]]
                  "=>"
                  (Term.do
                   "do"
                   (Term.doSeqIndent
                    [(Term.doSeqItem
                      (Term.doLetArrow
                       "let"
                       []
                       (Term.doIdDecl `n [] "←" (Term.doExpr (Term.app `revert [`e]))))
                      [])
                     (Term.doSeqItem
                      (Term.doLetArrow
                       "let"
                       []
                       (Term.doIdDecl `e [] "←" (Term.doExpr (Term.app `intro [`x]))))
                      [])
                     (Term.doSeqItem
                      (Term.doExpr (Term.app `intron [(«term_-_» `n "-" (num "1"))]))
                      [])
                     (Term.doSeqItem
                      (Term.doExpr (Term.app `pure [(Term.tuple "(" [`pat "," [`e]] ")")]))
                      [])])))
                 (Term.matchAlt
                  "|"
                  [[`none]]
                  "=>"
                  (Term.app `pure [(Term.tuple "(" [`pat "," [`e]] ")")]))]))
              "else"
              (Term.do
               "do"
               (Term.doSeqIndent
                [(Term.doSeqItem
                  (Term.doLetArrow
                   "let"
                   []
                   (Term.doIdDecl `x [] "←" (Term.doExpr (Term.app `pat [`mk_fresh_name `pure]))))
                  [])
                 (Term.doSeqItem
                  (Term.doLetArrow
                   "let"
                   []
                   (Term.doIdDecl
                    `n
                    []
                    "←"
                    (Term.doExpr (Term.app `revert_kdependencies [`e `semireducible]))))
                  [])
                 (Term.doSeqItem
                  (Term.doExpr
                   («term_<|>_»
                    (Term.app `tactic.generalize [`e `x])
                    "<|>"
                    (Term.do
                     "do"
                     (Term.doSeqIndent
                      [(Term.doSeqItem
                        (Term.doLetArrow
                         "let"
                         []
                         (Term.doIdDecl `t [] "←" (Term.doExpr (Term.app `infer_type [`e]))))
                        [])
                       (Term.doSeqItem (Term.doExpr (Term.app `tactic.assertv [`x `t `e])) [])
                       (Term.doSeqItem
                        (Term.doExpr («term_>>=_» (Term.app `get_local [`x]) ">>=" `tactic.revert))
                        [])
                       (Term.doSeqItem
                        (Term.doExpr (Term.app `pure [(Term.tuple "(" [] ")")]))
                        [])]))))
                  [])
                 (Term.doSeqItem
                  (Term.doExpr («term_<$>_» (Term.app `Prod.mk [`pat]) "<$>" `tactic.intro1))
                  [])]))))
            [])]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.do
       "do"
       (Term.doSeqIndent
        [(Term.doSeqItem
          (Term.doLet
           "let"
           []
           (Term.letDecl
            (Term.letIdDecl
             `p
             []
             []
             ":="
             (Term.match
              "match"
              []
              []
              [(Term.matchDiscr [] `pat)]
              "with"
              (Term.matchAlts
               [(Term.matchAlt
                 "|"
                 [[(Term.app `rcases_patt.typed [(Term.hole "_") `ty])]]
                 "=>"
                 (Term.precheckedQuot
                  "`"
                  (Term.quot
                   "`("
                   (Term.typeAscription
                    "("
                    (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `p ")") [])
                    ":"
                    [(term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `ty ")") [])]
                    ")")
                   ")")))
                (Term.matchAlt "|" [[(Term.hole "_")]] "=>" `p)])))))
          [])
         (Term.doSeqItem
          (Term.doLetArrow
           "let"
           []
           (Term.doIdDecl `e [] "←" (Term.doExpr (Term.app `i_to_expr [`p]))))
          [])
         (Term.doSeqItem
          (Term.doExpr
           (termIfThenElse
            "if"
            `e
            "then"
            (Term.match
             "match"
             []
             []
             [(Term.matchDiscr [] `pat)]
             "with"
             (Term.matchAlts
              [(Term.matchAlt
                "|"
                [[(Term.app `some [`x])]]
                "=>"
                (Term.do
                 "do"
                 (Term.doSeqIndent
                  [(Term.doSeqItem
                    (Term.doLetArrow
                     "let"
                     []
                     (Term.doIdDecl `n [] "←" (Term.doExpr (Term.app `revert [`e]))))
                    [])
                   (Term.doSeqItem
                    (Term.doLetArrow
                     "let"
                     []
                     (Term.doIdDecl `e [] "←" (Term.doExpr (Term.app `intro [`x]))))
                    [])
                   (Term.doSeqItem
                    (Term.doExpr (Term.app `intron [(«term_-_» `n "-" (num "1"))]))
                    [])
                   (Term.doSeqItem
                    (Term.doExpr (Term.app `pure [(Term.tuple "(" [`pat "," [`e]] ")")]))
                    [])])))
               (Term.matchAlt
                "|"
                [[`none]]
                "=>"
                (Term.app `pure [(Term.tuple "(" [`pat "," [`e]] ")")]))]))
            "else"
            (Term.do
             "do"
             (Term.doSeqIndent
              [(Term.doSeqItem
                (Term.doLetArrow
                 "let"
                 []
                 (Term.doIdDecl `x [] "←" (Term.doExpr (Term.app `pat [`mk_fresh_name `pure]))))
                [])
               (Term.doSeqItem
                (Term.doLetArrow
                 "let"
                 []
                 (Term.doIdDecl
                  `n
                  []
                  "←"
                  (Term.doExpr (Term.app `revert_kdependencies [`e `semireducible]))))
                [])
               (Term.doSeqItem
                (Term.doExpr
                 («term_<|>_»
                  (Term.app `tactic.generalize [`e `x])
                  "<|>"
                  (Term.do
                   "do"
                   (Term.doSeqIndent
                    [(Term.doSeqItem
                      (Term.doLetArrow
                       "let"
                       []
                       (Term.doIdDecl `t [] "←" (Term.doExpr (Term.app `infer_type [`e]))))
                      [])
                     (Term.doSeqItem (Term.doExpr (Term.app `tactic.assertv [`x `t `e])) [])
                     (Term.doSeqItem
                      (Term.doExpr («term_>>=_» (Term.app `get_local [`x]) ">>=" `tactic.revert))
                      [])
                     (Term.doSeqItem
                      (Term.doExpr (Term.app `pure [(Term.tuple "(" [] ")")]))
                      [])]))))
                [])
               (Term.doSeqItem
                (Term.doExpr («term_<$>_» (Term.app `Prod.mk [`pat]) "<$>" `tactic.intro1))
                [])]))))
          [])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doSeqIndent', expected 'Lean.Parser.Term.doSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (termIfThenElse
       "if"
       `e
       "then"
       (Term.match
        "match"
        []
        []
        [(Term.matchDiscr [] `pat)]
        "with"
        (Term.matchAlts
         [(Term.matchAlt
           "|"
           [[(Term.app `some [`x])]]
           "=>"
           (Term.do
            "do"
            (Term.doSeqIndent
             [(Term.doSeqItem
               (Term.doLetArrow
                "let"
                []
                (Term.doIdDecl `n [] "←" (Term.doExpr (Term.app `revert [`e]))))
               [])
              (Term.doSeqItem
               (Term.doLetArrow
                "let"
                []
                (Term.doIdDecl `e [] "←" (Term.doExpr (Term.app `intro [`x]))))
               [])
              (Term.doSeqItem (Term.doExpr (Term.app `intron [(«term_-_» `n "-" (num "1"))])) [])
              (Term.doSeqItem
               (Term.doExpr (Term.app `pure [(Term.tuple "(" [`pat "," [`e]] ")")]))
               [])])))
          (Term.matchAlt
           "|"
           [[`none]]
           "=>"
           (Term.app `pure [(Term.tuple "(" [`pat "," [`e]] ")")]))]))
       "else"
       (Term.do
        "do"
        (Term.doSeqIndent
         [(Term.doSeqItem
           (Term.doLetArrow
            "let"
            []
            (Term.doIdDecl `x [] "←" (Term.doExpr (Term.app `pat [`mk_fresh_name `pure]))))
           [])
          (Term.doSeqItem
           (Term.doLetArrow
            "let"
            []
            (Term.doIdDecl
             `n
             []
             "←"
             (Term.doExpr (Term.app `revert_kdependencies [`e `semireducible]))))
           [])
          (Term.doSeqItem
           (Term.doExpr
            («term_<|>_»
             (Term.app `tactic.generalize [`e `x])
             "<|>"
             (Term.do
              "do"
              (Term.doSeqIndent
               [(Term.doSeqItem
                 (Term.doLetArrow
                  "let"
                  []
                  (Term.doIdDecl `t [] "←" (Term.doExpr (Term.app `infer_type [`e]))))
                 [])
                (Term.doSeqItem (Term.doExpr (Term.app `tactic.assertv [`x `t `e])) [])
                (Term.doSeqItem
                 (Term.doExpr («term_>>=_» (Term.app `get_local [`x]) ">>=" `tactic.revert))
                 [])
                (Term.doSeqItem (Term.doExpr (Term.app `pure [(Term.tuple "(" [] ")")])) [])]))))
           [])
          (Term.doSeqItem
           (Term.doExpr («term_<$>_» (Term.app `Prod.mk [`pat]) "<$>" `tactic.intro1))
           [])])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.do
       "do"
       (Term.doSeqIndent
        [(Term.doSeqItem
          (Term.doLetArrow
           "let"
           []
           (Term.doIdDecl `x [] "←" (Term.doExpr (Term.app `pat [`mk_fresh_name `pure]))))
          [])
         (Term.doSeqItem
          (Term.doLetArrow
           "let"
           []
           (Term.doIdDecl
            `n
            []
            "←"
            (Term.doExpr (Term.app `revert_kdependencies [`e `semireducible]))))
          [])
         (Term.doSeqItem
          (Term.doExpr
           («term_<|>_»
            (Term.app `tactic.generalize [`e `x])
            "<|>"
            (Term.do
             "do"
             (Term.doSeqIndent
              [(Term.doSeqItem
                (Term.doLetArrow
                 "let"
                 []
                 (Term.doIdDecl `t [] "←" (Term.doExpr (Term.app `infer_type [`e]))))
                [])
               (Term.doSeqItem (Term.doExpr (Term.app `tactic.assertv [`x `t `e])) [])
               (Term.doSeqItem
                (Term.doExpr («term_>>=_» (Term.app `get_local [`x]) ">>=" `tactic.revert))
                [])
               (Term.doSeqItem (Term.doExpr (Term.app `pure [(Term.tuple "(" [] ")")])) [])]))))
          [])
         (Term.doSeqItem
          (Term.doExpr («term_<$>_» (Term.app `Prod.mk [`pat]) "<$>" `tactic.intro1))
          [])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doSeqIndent', expected 'Lean.Parser.Term.doSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<$>_» (Term.app `Prod.mk [`pat]) "<$>" `tactic.intro1)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `tactic.intro1
[PrettyPrinter.parenthesize] ...precedences are 100 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 100, term))
      (Term.app `Prod.mk [`pat])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `pat
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Prod.mk
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 101 >? 1022, (some 1023, term) <=? (some 100, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 100, (some 100, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, doElem))
      («term_<|>_»
       (Term.app `tactic.generalize [`e `x])
       "<|>"
       (Term.do
        "do"
        (Term.doSeqIndent
         [(Term.doSeqItem
           (Term.doLetArrow
            "let"
            []
            (Term.doIdDecl `t [] "←" (Term.doExpr (Term.app `infer_type [`e]))))
           [])
          (Term.doSeqItem (Term.doExpr (Term.app `tactic.assertv [`x `t `e])) [])
          (Term.doSeqItem
           (Term.doExpr («term_>>=_» (Term.app `get_local [`x]) ">>=" `tactic.revert))
           [])
          (Term.doSeqItem (Term.doExpr (Term.app `pure [(Term.tuple "(" [] ")")])) [])])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.do
       "do"
       (Term.doSeqIndent
        [(Term.doSeqItem
          (Term.doLetArrow
           "let"
           []
           (Term.doIdDecl `t [] "←" (Term.doExpr (Term.app `infer_type [`e]))))
          [])
         (Term.doSeqItem (Term.doExpr (Term.app `tactic.assertv [`x `t `e])) [])
         (Term.doSeqItem
          (Term.doExpr («term_>>=_» (Term.app `get_local [`x]) ">>=" `tactic.revert))
          [])
         (Term.doSeqItem (Term.doExpr (Term.app `pure [(Term.tuple "(" [] ")")])) [])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doSeqIndent', expected 'Lean.Parser.Term.doSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `pure [(Term.tuple "(" [] ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.tuple', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.tuple', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.tuple "(" [] ")")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `pure
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, doElem))
      («term_>>=_» (Term.app `get_local [`x]) ">>=" `tactic.revert)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `tactic.revert
[PrettyPrinter.parenthesize] ...precedences are 56 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 55, term))
      (Term.app `get_local [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `get_local
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 55 >? 1022, (some 1023, term) <=? (some 55, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 55, (some 56, term) <=? (some 1023, doElem)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, doElem))
      (Term.app `tactic.assertv [`x `t `e])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `e
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `t
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `tactic.assertv
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1023, doElem)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, doElem))
      (Term.app `infer_type [`e])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `e
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `infer_type
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, doElem)
[PrettyPrinter.parenthesize] ...precedences are 20 >? 1023, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 20, term))
      (Term.app `tactic.generalize [`e `x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `e
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `tactic.generalize
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 21 >? 1022, (some 1023, term) <=? (some 20, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 20, (some 0, term) <=? (some 1023, doElem)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, doElem))
      (Term.app `revert_kdependencies [`e `semireducible])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `semireducible
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `e
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `revert_kdependencies
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, doElem)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, doElem))
      (Term.app `pat [`mk_fresh_name `pure])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `pure
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `mk_fresh_name
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `pat
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, doElem)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1023, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.match
       "match"
       []
       []
       [(Term.matchDiscr [] `pat)]
       "with"
       (Term.matchAlts
        [(Term.matchAlt
          "|"
          [[(Term.app `some [`x])]]
          "=>"
          (Term.do
           "do"
           (Term.doSeqIndent
            [(Term.doSeqItem
              (Term.doLetArrow
               "let"
               []
               (Term.doIdDecl `n [] "←" (Term.doExpr (Term.app `revert [`e]))))
              [])
             (Term.doSeqItem
              (Term.doLetArrow
               "let"
               []
               (Term.doIdDecl `e [] "←" (Term.doExpr (Term.app `intro [`x]))))
              [])
             (Term.doSeqItem (Term.doExpr (Term.app `intron [(«term_-_» `n "-" (num "1"))])) [])
             (Term.doSeqItem
              (Term.doExpr (Term.app `pure [(Term.tuple "(" [`pat "," [`e]] ")")]))
              [])])))
         (Term.matchAlt
          "|"
          [[`none]]
          "=>"
          (Term.app `pure [(Term.tuple "(" [`pat "," [`e]] ")")]))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `pure [(Term.tuple "(" [`pat "," [`e]] ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.tuple', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.tuple', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.tuple "(" [`pat "," [`e]] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `e
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `pat
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `pure
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `none
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.do
       "do"
       (Term.doSeqIndent
        [(Term.doSeqItem
          (Term.doLetArrow "let" [] (Term.doIdDecl `n [] "←" (Term.doExpr (Term.app `revert [`e]))))
          [])
         (Term.doSeqItem
          (Term.doLetArrow "let" [] (Term.doIdDecl `e [] "←" (Term.doExpr (Term.app `intro [`x]))))
          [])
         (Term.doSeqItem (Term.doExpr (Term.app `intron [(«term_-_» `n "-" (num "1"))])) [])
         (Term.doSeqItem
          (Term.doExpr (Term.app `pure [(Term.tuple "(" [`pat "," [`e]] ")")]))
          [])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doSeqIndent', expected 'Lean.Parser.Term.doSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `pure [(Term.tuple "(" [`pat "," [`e]] ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.tuple', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.tuple', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.tuple "(" [`pat "," [`e]] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `e
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `pat
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `pure
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, doElem))
      (Term.app `intron [(«term_-_» `n "-" (num "1"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_-_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_-_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_-_» `n "-" (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `n
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_-_» `n "-" (num "1")) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `intron
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1023, doElem)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, doElem))
      (Term.app `intro [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `intro
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, doElem)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, doElem))
      (Term.app `revert [`e])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `e
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `revert
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, doElem)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1023, (some 0,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `some [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `some
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `pat
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `e
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, doElem))
      (Term.app `i_to_expr [`p])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `i_to_expr
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, doElem)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, doElem))
      (Term.match
       "match"
       []
       []
       [(Term.matchDiscr [] `pat)]
       "with"
       (Term.matchAlts
        [(Term.matchAlt
          "|"
          [[(Term.app `rcases_patt.typed [(Term.hole "_") `ty])]]
          "=>"
          (Term.precheckedQuot
           "`"
           (Term.quot
            "`("
            (Term.typeAscription
             "("
             (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `p ")") [])
             ":"
             [(term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `ty ")") [])]
             ")")
            ")")))
         (Term.matchAlt "|" [[(Term.hole "_")]] "=>" `p)]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.precheckedQuot
       "`"
       (Term.quot
        "`("
        (Term.typeAscription
         "("
         (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `p ")") [])
         ":"
         [(term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `ty ")") [])]
         ")")
        ")"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription
       "("
       (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `p ")") [])
       ":"
       [(term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `ty ")") [])]
       ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'term.pseudo.antiquot', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `ty ")") [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'antiquotName'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'antiquotNestedExpr', expected 'ident'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `p ")") [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'antiquotName'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'antiquotNestedExpr', expected 'ident'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `rcases_patt.typed [(Term.hole "_") `ty])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ty
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `rcases_patt.typed
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `pat
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (some 1023, doElem)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1023, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [`p "," `pat] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `pat
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app (Term.proj `ps "." `zip) [`pats]) "." `mmap)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app (Term.proj `ps "." `zip) [`pats])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `pats
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `ps "." `zip)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `ps
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.proj `ps "." `zip) [`pats])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, doElem)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letPatDecl', expected 'Lean.Parser.Term.letIdDecl'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, doElem))
      (Term.app
       `rcases.process_constructor
       [`false
        (Term.app
         (Term.proj `ps "." `map)
         [(Term.fun "fun" (Term.basicFun [(Term.hole "_")] [] "=>" `default))])
        (Term.proj (Term.proj `pat "." `as_tuple) "." (fieldIdx "2"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.proj `pat "." `as_tuple) "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj `pat "." `as_tuple)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `pat
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       (Term.proj `ps "." `map)
       [(Term.fun "fun" (Term.basicFun [(Term.hole "_")] [] "=>" `default))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun "fun" (Term.basicFun [(Term.hole "_")] [] "=>" `default))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `default
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
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `ps "." `map)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `ps
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      (Term.proj `ps "." `map)
      [(Term.fun "fun" (Term.basicFun [(Term.hole "_")] [] "=>" `default))])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `false
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `rcases.process_constructor
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1023, doElem)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.tuple "(" [(Term.hole "_") "," [`pats]] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `pats
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1023, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app `tactic [`Unit])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Unit
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `tactic
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rcases_patt
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Tactic.Tactic.Rcases.«termlistΠ» "listΠ") [`pexpr])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `pexpr
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Tactic.Tactic.Rcases.«termlistΠ» "listΠ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Tactic.Tactic.Rcases.«termlistΠ»', expected 'Tactic.Tactic.Rcases.termlistΠ._@.Tactic.Rcases._hyg.324'
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
      `rcases_many es pats` performs case distinction on the `es` using `pat` to
      name the arising new variables and assumptions.
      See the module comment for the syntax of `pat`. -/
    unsafe
  def
    rcases_many
    ( ps : listΠ pexpr ) ( pat : rcases_patt ) : tactic Unit
    :=
      do
        let
            ( _ , pats )
              :=
              rcases.process_constructor false ps . map fun _ => default pat . as_tuple . 2
          let
            pes
              ←
              ps . zip pats . mmap
                fun
                  ⟨ p , pat ⟩
                    =>
                    do
                      let
                          p
                            :=
                            match
                              pat
                              with
                              | rcases_patt.typed _ ty => ` `( ( $ ( p ) : $ ( ty ) ) ) | _ => p
                        let e ← i_to_expr p
                        if
                          e
                          then
                          match
                            pat
                            with
                            |
                                some x
                                =>
                                do let n ← revert e let e ← intro x intron n - 1 pure ( pat , e )
                              | none => pure ( pat , e )
                          else
                          do
                            let x ← pat mk_fresh_name pure
                              let n ← revert_kdependencies e semireducible
                              tactic.generalize e x
                                <|>
                                do
                                  let t ← infer_type e
                                    tactic.assertv x t e
                                    get_local x >>= tactic.revert
                                    pure ( )
                              Prod.mk pat <$> tactic.intro1
          focus1 rcases.continue pes >>= clear_goals
#align tactic.rcases_many tactic.rcases_many

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "`rintro pat₁ pat₂ ... patₙ` introduces `n` arguments, then pattern matches on the `patᵢ` using\nthe same syntax as `rcases`. -/")]
      []
      []
      []
      [(Command.unsafe "unsafe")]
      [])
     (Command.def
      "def"
      (Command.declId `rintro [])
      (Command.optDeclSig
       [(Term.explicitBinder
         "("
         [`ids]
         [":" (Term.app (Tactic.Tactic.Rcases.«termlistΠ» "listΠ") [`rcases_patt])]
         []
         ")")]
       [(Term.typeSpec ":" (Term.app `tactic [`Unit]))])
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
             `l
             []
             "←"
             (Term.doExpr
              (Term.app
               (Term.proj `ids "." `mmap)
               [(Term.fun
                 "fun"
                 (Term.basicFun
                  [`id]
                  []
                  "=>"
                  (Term.do
                   "do"
                   (Term.doSeqIndent
                    [(Term.doSeqItem
                      (Term.doLetArrow
                       "let"
                       []
                       (Term.doIdDecl
                        `e
                        []
                        "←"
                        (Term.doExpr
                         («term_<|_»
                          `intro
                          "<|"
                          (Term.app
                           (Term.proj (Term.proj `id "." `Name) "." `getOrElse)
                           [(Term.quotedName (name "`_"))])))))
                      [])
                     (Term.doSeqItem
                      (Term.doExpr (Term.app `pure [(Term.tuple "(" [`id "," [`e]] ")")]))
                      [])]))))]))))
           [])
          (Term.doSeqItem
           (Term.doExpr
            (Term.app `focus1 [(«term_>>=_» (Term.app `rcases.continue [`l]) ">>=" `clear_goals)]))
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
            `l
            []
            "←"
            (Term.doExpr
             (Term.app
              (Term.proj `ids "." `mmap)
              [(Term.fun
                "fun"
                (Term.basicFun
                 [`id]
                 []
                 "=>"
                 (Term.do
                  "do"
                  (Term.doSeqIndent
                   [(Term.doSeqItem
                     (Term.doLetArrow
                      "let"
                      []
                      (Term.doIdDecl
                       `e
                       []
                       "←"
                       (Term.doExpr
                        («term_<|_»
                         `intro
                         "<|"
                         (Term.app
                          (Term.proj (Term.proj `id "." `Name) "." `getOrElse)
                          [(Term.quotedName (name "`_"))])))))
                     [])
                    (Term.doSeqItem
                     (Term.doExpr (Term.app `pure [(Term.tuple "(" [`id "," [`e]] ")")]))
                     [])]))))]))))
          [])
         (Term.doSeqItem
          (Term.doExpr
           (Term.app `focus1 [(«term_>>=_» (Term.app `rcases.continue [`l]) ">>=" `clear_goals)]))
          [])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doSeqIndent', expected 'Lean.Parser.Term.doSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `focus1 [(«term_>>=_» (Term.app `rcases.continue [`l]) ">>=" `clear_goals)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_>>=_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_>>=_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_>>=_» (Term.app `rcases.continue [`l]) ">>=" `clear_goals)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `clear_goals
[PrettyPrinter.parenthesize] ...precedences are 56 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 55, term))
      (Term.app `rcases.continue [`l])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `l
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `rcases.continue
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 55 >? 1022, (some 1023, term) <=? (some 55, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 55, (some 56, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_>>=_» (Term.app `rcases.continue [`l]) ">>=" `clear_goals)
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `focus1
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, doElem))
      (Term.app
       (Term.proj `ids "." `mmap)
       [(Term.fun
         "fun"
         (Term.basicFun
          [`id]
          []
          "=>"
          (Term.do
           "do"
           (Term.doSeqIndent
            [(Term.doSeqItem
              (Term.doLetArrow
               "let"
               []
               (Term.doIdDecl
                `e
                []
                "←"
                (Term.doExpr
                 («term_<|_»
                  `intro
                  "<|"
                  (Term.app
                   (Term.proj (Term.proj `id "." `Name) "." `getOrElse)
                   [(Term.quotedName (name "`_"))])))))
              [])
             (Term.doSeqItem
              (Term.doExpr (Term.app `pure [(Term.tuple "(" [`id "," [`e]] ")")]))
              [])]))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`id]
        []
        "=>"
        (Term.do
         "do"
         (Term.doSeqIndent
          [(Term.doSeqItem
            (Term.doLetArrow
             "let"
             []
             (Term.doIdDecl
              `e
              []
              "←"
              (Term.doExpr
               («term_<|_»
                `intro
                "<|"
                (Term.app
                 (Term.proj (Term.proj `id "." `Name) "." `getOrElse)
                 [(Term.quotedName (name "`_"))])))))
            [])
           (Term.doSeqItem
            (Term.doExpr (Term.app `pure [(Term.tuple "(" [`id "," [`e]] ")")]))
            [])]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.do
       "do"
       (Term.doSeqIndent
        [(Term.doSeqItem
          (Term.doLetArrow
           "let"
           []
           (Term.doIdDecl
            `e
            []
            "←"
            (Term.doExpr
             («term_<|_»
              `intro
              "<|"
              (Term.app
               (Term.proj (Term.proj `id "." `Name) "." `getOrElse)
               [(Term.quotedName (name "`_"))])))))
          [])
         (Term.doSeqItem (Term.doExpr (Term.app `pure [(Term.tuple "(" [`id "," [`e]] ")")])) [])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doSeqIndent', expected 'Lean.Parser.Term.doSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `pure [(Term.tuple "(" [`id "," [`e]] ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.tuple', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.tuple', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.tuple "(" [`id "," [`e]] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `e
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `id
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `pure
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, doElem))
      («term_<|_»
       `intro
       "<|"
       (Term.app
        (Term.proj (Term.proj `id "." `Name) "." `getOrElse)
        [(Term.quotedName (name "`_"))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj (Term.proj `id "." `Name) "." `getOrElse)
       [(Term.quotedName (name "`_"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.quotedName', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.quotedName', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.quotedName (name "`_"))
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.proj `id "." `Name) "." `getOrElse)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj `id "." `Name)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `id
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      `intro
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 10, term) <=? (none, doElem)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1023, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `id
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `ids "." `mmap)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `ids
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, doElem)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1023, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app `tactic [`Unit])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Unit
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `tactic
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Tactic.Tactic.Rcases.«termlistΠ» "listΠ") [`rcases_patt])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rcases_patt
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Tactic.Tactic.Rcases.«termlistΠ» "listΠ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Tactic.Tactic.Rcases.«termlistΠ»', expected 'Tactic.Tactic.Rcases.termlistΠ._@.Tactic.Rcases._hyg.324'
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
      `rintro pat₁ pat₂ ... patₙ` introduces `n` arguments, then pattern matches on the `patᵢ` using
      the same syntax as `rcases`. -/
    unsafe
  def
    rintro
    ( ids : listΠ rcases_patt ) : tactic Unit
    :=
      do
        let l ← ids . mmap fun id => do let e ← intro <| id . Name . getOrElse `_ pure ( id , e )
          focus1 rcases.continue l >>= clear_goals
#align tactic.rintro tactic.rintro

/-- Like `zip_with`, but if the lists don't match in length, the excess elements will be put at the
end of the result. -/
def mergeList {α} (m : α → α → α) : List α → List α → List α
  | [], l₂ => l₂
  | l₁, [] => l₁
  | a :: l₁, b :: l₂ => m a b :: merge_list l₁ l₂
#align tactic.merge_list Tactic.mergeList

/-- Merge two `rcases` patterns. This is used to underapproximate a case tree by an `rcases`
pattern. The two patterns come from cases in two branches, that due to the syntax of `rcases`
patterns are forced to overlap. The rule here is that we take only the case splits that are in
common between both branches. For example if one branch does `⟨a, b⟩` and the other does `c`,
then we return `c` because we don't know that a case on `c` would be safe to do. -/
unsafe def rcases_patt.merge : rcases_patt → rcases_patt → rcases_patt
  | rcases_patt.alts p₁, p₂ => rcases_patt.alts (mergeList rcases_patt.merge p₁ p₂.as_alts)
  | p₁, rcases_patt.alts p₂ => rcases_patt.alts (mergeList rcases_patt.merge p₁.as_alts p₂)
  | rcases_patt.explicit p₁, p₂ => rcases_patt.explicit (p₁.merge p₂)
  | p₁, rcases_patt.explicit p₂ => rcases_patt.explicit (p₁.merge p₂)
  | rcases_patt.tuple p₁, p₂ => rcases_patt.tuple (mergeList rcases_patt.merge p₁ p₂.as_tuple.2)
  | p₁, rcases_patt.tuple p₂ => rcases_patt.tuple (mergeList rcases_patt.merge p₁.as_tuple.2 p₂)
  | rcases_patt.typed p₁ e, p₂ => rcases_patt.typed (p₁.merge p₂) e
  | p₁, rcases_patt.typed p₂ e => rcases_patt.typed (p₁.merge p₂) e
  | rcases_patt.one `rfl, rcases_patt.one `rfl => rcases_patt.one `rfl
  | rcases_patt.one `_, p => p
  | p, rcases_patt.one `_ => p
  | rcases_patt.clear, p => p
  | p, rcases_patt.clear => p
  | rcases_patt.one n, _ => rcases_patt.one n
#align tactic.rcases_patt.merge tactic.rcases_patt.merge

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.mutual
     "mutual"
     [(Command.declaration
       (Command.declModifiers
        [(Command.docComment
          "/--"
          "* `rcases_hint_core depth e` does the same as `rcases p e`, except the pattern `p` is an output\n  instead of an input, controlled only by the case depth argument `depth`. We use `cases` to depth\n  `depth` and then reconstruct an `rcases` pattern `p` that would, if passed to `rcases`, perform\n  the same thing as the case tree we just constructed (or at least, the nearest expressible\n  approximation to this.)\n* `rcases_hint.process_constructors depth cs l` takes a list of constructor names `cs` and a\n  matching list `l` of elements `(g, c', hs, _)` where  `c'` is a constructor name (used for\n  alignment with `cs`), `g` is the subgoal, and `hs` is the list of local hypotheses created by\n  `cases` in that subgoal. It matches on all of them, and then produces a `ΣΠ`-list of `rcases`\n  patterns describing the result, and the list of generated subgoals.\n* `rcases_hint.continue depth es` does the same as `rcases.continue (ps.zip es)`, except the\n  patterns `ps` are an output instead of an input, created by matching on everything to depth\n  `depth` and recording the successful cases. It returns `ps`, and the list of generated subgoals.\n-/")]
        []
        []
        []
        [(Command.unsafe "unsafe")]
        [])
       (Command.def
        "def"
        (Command.declId `rcases_hint_core [])
        (Command.optDeclSig
         [(Term.explicitBinder "(" [`explicit] [":" `Bool] [] ")")]
         [(Term.typeSpec
           ":"
           (Term.arrow
            `Bool
            "→"
            (Term.arrow
             (termℕ "ℕ")
             "→"
             (Term.arrow
              `expr
              "→"
              (Term.app
               `tactic
               [(«term_×_» (Term.app `Option [`rcases_patt]) "×" (Term.app `List [`expr]))])))))])
        (Command.declValEqns
         (Term.matchAltsWhereDecls
          (Term.matchAlts
           [(Term.matchAlt
             "|"
             [[`force "," `depth "," `e]]
             "=>"
             (Term.do
              "do"
              (Term.doSeqIndent
               [(Term.doSeqItem
                 (Term.doLetArrow
                  "let"
                  []
                  (Term.doPatDecl
                   (Term.tuple "(" [`t "," [`e]] ")")
                   "←"
                   (Term.doExpr (Term.app `get_local_and_type [`e]))
                   []))
                 [])
                (Term.doSeqItem
                 (Term.doLetArrow
                  "let"
                  []
                  (Term.doPatDecl
                   `tt
                   "←"
                   (Term.doExpr
                    (Term.app
                     `pure
                     [(«term_||_»
                       («term_||_» `explicit "||" `force)
                       "||"
                       («term_=_»
                        (Term.proj `e "." `local_binding_info)
                        "="
                        `BinderInfo.default))]))
                   ["|"
                    (Term.doSeqIndent
                     [(Term.doSeqItem
                       (Term.doExpr («term_<$>_» (Term.app `Prod.mk [`none]) "<$>" `get_goals))
                       [])])]))
                 [])
                (Term.doSeqItem
                 (Term.doLetArrow
                  "let"
                  []
                  (Term.doIdDecl `t [] "←" (Term.doExpr (Term.app `whnf [`t]))))
                 [])
                (Term.doSeqItem
                 (Term.doLetArrow "let" [] (Term.doIdDecl `env [] "←" (Term.doExpr `get_env)))
                 [])
                (Term.doSeqItem
                 (Term.doLet
                  "let"
                  []
                  (Term.letDecl
                   (Term.letIdDecl
                    `I
                    []
                    []
                    ":="
                    (Term.proj (Term.proj `t "." `get_app_fn) "." `const_name))))
                 [])
                (Term.doSeqItem
                 (Term.doExpr
                  («term_<|>_»
                   (Term.do
                    "do"
                    (Term.doSeqIndent
                     [(Term.doSeqItem
                       (Term.doExpr
                        (Term.app `guard [(«term_=_» `I "=" (Term.doubleQuotedName "`" "`" `Eq))]))
                       [])
                      (Term.doSeqItem (Term.doExpr (Term.app `subst' [`e])) [])
                      (Term.doSeqItem
                       (Term.doExpr
                        («term_<$>_»
                         (Term.app
                          `Prod.mk
                          [(Term.app
                            `some
                            [(Term.app `rcases_patt.one [(Term.quotedName (name "`rfl"))])])])
                         "<$>"
                         `get_goals))
                       [])]))
                   "<|>"
                   (Term.do
                    "do"
                    (Term.doSeqIndent
                     [(Term.doSeqItem
                       (Term.doLet
                        "let"
                        []
                        (Term.letDecl (Term.letIdDecl `c [] [] ":=" (Term.app `env [`I]))))
                       [])
                      (Term.doSeqItem
                       (Term.doLetArrow
                        "let"
                        []
                        (Term.doPatDecl
                         (Term.app `some [`l])
                         "←"
                         (Term.doExpr
                          (Term.app
                           `try_core
                           [(«term_>>_»
                             (Term.app `guard [(«term_≠_» `depth "≠" (num "0"))])
                             ">>"
                             (Term.app `cases_core [`e]))]))
                         ["|"
                          (Term.doSeqIndent
                           [(Term.doSeqItem
                             (Term.doExpr
                              (Term.let
                               "let"
                               (Term.letDecl
                                (Term.letIdDecl
                                 `n
                                 []
                                 []
                                 ":="
                                 (Term.match
                                  "match"
                                  []
                                  []
                                  [(Term.matchDiscr [] `e)]
                                  "with"
                                  (Term.matchAlts
                                   [(Term.matchAlt
                                     "|"
                                     [[`Name.anonymous]]
                                     "=>"
                                     (Term.quotedName (name "`_")))
                                    (Term.matchAlt "|" [[`n]] "=>" `n)]))))
                               []
                               («term_<$>_»
                                (Term.app
                                 `Prod.mk
                                 [(Term.app `some [(Term.app `rcases_patt.one [`n])])])
                                "<$>"
                                `get_goals)))
                             [])])]))
                       [])
                      (Term.doSeqItem
                       (Term.doLetArrow
                        "let"
                        []
                        (Term.doIdDecl `gs [] "←" (Term.doExpr `get_goals)))
                       [])
                      (Term.doSeqItem
                       (Term.doExpr
                        (termIfThenElse
                         "if"
                         `gs
                         "then"
                         (Term.app
                          `pure
                          [(Term.tuple
                            "("
                            [(Term.app
                              `some
                              [(Term.app `rcases_patt.tuple [(«term[_]» "[" [] "]")])])
                             ","
                             [(«term[_]» "[" [] "]")]]
                            ")")])
                         "else"
                         (Term.do
                          "do"
                          (Term.doSeqIndent
                           [(Term.doSeqItem
                             (Term.doLetArrow
                              "let"
                              []
                              (Term.doPatDecl
                               (Term.tuple "(" [`ps "," [`gs']] ")")
                               "←"
                               (Term.doExpr
                                (Term.app
                                 `rcases_hint.process_constructors
                                 [(«term_-_» `depth "-" (num "1")) `c (Term.app `gs [`l])]))
                               []))
                             [])
                            (Term.doSeqItem
                             (Term.doExpr
                              (Term.app
                               `pure
                               [(Term.tuple
                                 "("
                                 [(Term.app `some [(Term.app `rcases_patt.alts₁ [`ps])]) "," [`gs']]
                                 ")")]))
                             [])]))))
                       [])]))))
                 [])])))])
          []))
        []
        []
        []))
      (Command.declaration
       (Command.declModifiers
        [(Command.docComment
          "/--"
          "* `rcases_hint_core depth e` does the same as `rcases p e`, except the pattern `p` is an output\n  instead of an input, controlled only by the case depth argument `depth`. We use `cases` to depth\n  `depth` and then reconstruct an `rcases` pattern `p` that would, if passed to `rcases`, perform\n  the same thing as the case tree we just constructed (or at least, the nearest expressible\n  approximation to this.)\n* `rcases_hint.process_constructors depth cs l` takes a list of constructor names `cs` and a\n  matching list `l` of elements `(g, c', hs, _)` where  `c'` is a constructor name (used for\n  alignment with `cs`), `g` is the subgoal, and `hs` is the list of local hypotheses created by\n  `cases` in that subgoal. It matches on all of them, and then produces a `ΣΠ`-list of `rcases`\n  patterns describing the result, and the list of generated subgoals.\n* `rcases_hint.continue depth es` does the same as `rcases.continue (ps.zip es)`, except the\n  patterns `ps` are an output instead of an input, created by matching on everything to depth\n  `depth` and recording the successful cases. It returns `ps`, and the list of generated subgoals.\n-/")]
        []
        []
        []
        [(Command.unsafe "unsafe")]
        [])
       (Command.def
        "def"
        (Command.declId `rcases_hint.process_constructors [])
        (Command.optDeclSig
         [(Term.explicitBinder "(" [`explicit] [":" `Bool] [] ")")]
         [(Term.typeSpec
           ":"
           (Term.arrow
            (termℕ "ℕ")
            "→"
            (Term.arrow
             (Term.app (Tactic.Tactic.Rcases.«termlistΣ» "listΣ") [`Name])
             "→"
             (Term.arrow
              (Term.app
               `List
               [(«term_×_»
                 `expr
                 "×"
                 («term_×_»
                  `Name
                  "×"
                  («term_×_»
                   (Term.app (Tactic.Tactic.Rcases.«termlistΠ» "listΠ") [`expr])
                   "×"
                   (Term.app `List [(«term_×_» `Name "×" `expr)]))))])
              "→"
              (Term.app
               `tactic
               [(«term_×_»
                 (Term.app
                  (Tactic.Tactic.Rcases.«termlistΣ» "listΣ")
                  [(Term.app (Tactic.Tactic.Rcases.«termlistΠ» "listΠ") [`rcases_patt])])
                 "×"
                 (Term.app `List [`expr]))])))))])
        (Command.declValEqns
         (Term.matchAltsWhereDecls
          (Term.matchAlts
           [(Term.matchAlt
             "|"
             [[`depth "," («term[_]» "[" [] "]") "," (Term.hole "_")]]
             "=>"
             (Term.app
              `pure
              [(Term.tuple "(" [(«term[_]» "[" [] "]") "," [(«term[_]» "[" [] "]")]] ")")]))
            (Term.matchAlt
             "|"
             [[`depth "," `cs "," («term[_]» "[" [] "]")]]
             "=>"
             (Term.app
              `pure
              [(Term.tuple
                "("
                [(Term.app
                  (Term.proj `cs "." `map)
                  [(Term.fun
                    "fun"
                    (Term.basicFun [(Term.hole "_")] [] "=>" («term[_]» "[" [] "]")))])
                 ","
                 [(«term[_]» "[" [] "]")]]
                ")")]))
            (Term.matchAlt
             "|"
             [[`depth
               ","
               («term_::_» `c "::" `cs)
               ","
               (Term.namedPattern
                `ls
                "@"
                []
                («term_::_»
                 (Term.tuple "(" [`g "," [`c' "," `hs "," (Term.hole "_")]] ")")
                 "::"
                 `l))]]
             "=>"
             (termIfThenElse
              "if"
              («term_≠_» `c "≠" `c')
              "then"
              (Term.do
               "do"
               (Term.doSeqIndent
                [(Term.doSeqItem
                  (Term.doLetArrow
                   "let"
                   []
                   (Term.doPatDecl
                    (Term.tuple "(" [`ps "," [`gs]] ")")
                    "←"
                    (Term.doExpr (Term.app `rcases_hint.process_constructors [`depth `cs `ls]))
                    []))
                  [])
                 (Term.doSeqItem
                  (Term.doExpr
                   (Term.app
                    `pure
                    [(Term.tuple
                      "("
                      [(«term_::_» («term[_]» "[" [] "]") "::" `ps) "," [`gs]]
                      ")")]))
                  [])]))
              "else"
              (Term.do
               "do"
               (Term.doSeqIndent
                [(Term.doSeqItem
                  (Term.doLetArrow
                   "let"
                   []
                   (Term.doPatDecl
                    (Term.tuple "(" [`p "," [`gs]] ")")
                    "←"
                    (Term.doExpr
                     («term_>>_»
                      (Term.app `set_goals [(«term[_]» "[" [`g] "]")])
                      ">>"
                      (Term.app `rcases_hint.continue [`depth `hs])))
                    []))
                  [])
                 (Term.doSeqItem
                  (Term.doLetArrow
                   "let"
                   []
                   (Term.doPatDecl
                    (Term.tuple "(" [`ps "," [`gs']] ")")
                    "←"
                    (Term.doExpr (Term.app `rcases_hint.process_constructors [`depth `cs `l]))
                    []))
                  [])
                 (Term.doSeqItem
                  (Term.doExpr
                   (Term.app
                    `pure
                    [(Term.tuple
                      "("
                      [(«term_::_» `p "::" `ps) "," [(«term_++_» `gs "++" `gs')]]
                      ")")]))
                  [])]))))])
          []))
        []
        []
        []))
      (Command.declaration
       (Command.declModifiers
        [(Command.docComment
          "/--"
          "* `rcases_hint_core depth e` does the same as `rcases p e`, except the pattern `p` is an output\n  instead of an input, controlled only by the case depth argument `depth`. We use `cases` to depth\n  `depth` and then reconstruct an `rcases` pattern `p` that would, if passed to `rcases`, perform\n  the same thing as the case tree we just constructed (or at least, the nearest expressible\n  approximation to this.)\n* `rcases_hint.process_constructors depth cs l` takes a list of constructor names `cs` and a\n  matching list `l` of elements `(g, c', hs, _)` where  `c'` is a constructor name (used for\n  alignment with `cs`), `g` is the subgoal, and `hs` is the list of local hypotheses created by\n  `cases` in that subgoal. It matches on all of them, and then produces a `ΣΠ`-list of `rcases`\n  patterns describing the result, and the list of generated subgoals.\n* `rcases_hint.continue depth es` does the same as `rcases.continue (ps.zip es)`, except the\n  patterns `ps` are an output instead of an input, created by matching on everything to depth\n  `depth` and recording the successful cases. It returns `ps`, and the list of generated subgoals.\n-/")]
        []
        []
        []
        [(Command.unsafe "unsafe")]
        [])
       (Command.def
        "def"
        (Command.declId `rcases_hint.continue [])
        (Command.optDeclSig
         [(Term.explicitBinder "(" [`explicit] [":" `Bool] [] ")")]
         [(Term.typeSpec
           ":"
           (Term.arrow
            (termℕ "ℕ")
            "→"
            (Term.arrow
             (Term.app (Tactic.Tactic.Rcases.«termlistΠ» "listΠ") [`expr])
             "→"
             (Term.app
              `tactic
              [(«term_×_»
                (Term.app (Tactic.Tactic.Rcases.«termlistΠ» "listΠ") [`rcases_patt])
                "×"
                (Term.app `List [`expr]))]))))])
        (Command.declValEqns
         (Term.matchAltsWhereDecls
          (Term.matchAlts
           [(Term.matchAlt
             "|"
             [[`depth "," («term[_]» "[" [] "]")]]
             "=>"
             («term_<$>_» (Term.app `Prod.mk [(«term[_]» "[" [] "]")]) "<$>" `get_goals))
            (Term.matchAlt
             "|"
             [[`depth "," («term_::_» `e "::" `es)]]
             "=>"
             (Term.do
              "do"
              (Term.doSeqIndent
               [(Term.doSeqItem
                 (Term.doLetArrow
                  "let"
                  []
                  (Term.doPatDecl
                   (Term.tuple "(" [`p "," [`gs]] ")")
                   "←"
                   (Term.doExpr (Term.app `rcases_hint_core [`false `depth `e]))
                   []))
                 [])
                (Term.doSeqItem
                 (Term.doLetArrow
                  "let"
                  []
                  (Term.doPatDecl
                   (Term.tuple "(" [`ps "," [`gs']] ")")
                   "←"
                   (Term.doExpr
                    (Term.app
                     (Term.proj `gs "." `mfoldl)
                     [(Term.fun
                       "fun"
                       (Term.basicFun
                        [(Term.typeAscription
                          "("
                          (Term.app `r [])
                          ":"
                          [(«term_×_»
                            (Term.app (Tactic.Tactic.Rcases.«termlistΠ» "listΠ") [`rcases_patt])
                            "×"
                            (Term.app `List [`expr]))]
                          ")")
                         `g]
                        []
                        "=>"
                        (Term.do
                         "do"
                         (Term.doSeqIndent
                          [(Term.doSeqItem
                            (Term.doLetArrow
                             "let"
                             []
                             (Term.doPatDecl
                              (Term.tuple "(" [`ps "," [`gs']] ")")
                              "←"
                              (Term.doExpr
                               («term_>>_»
                                (Term.app `set_goals [(«term[_]» "[" [`g] "]")])
                                ">>"
                                (Term.app `rcases_hint.continue [`depth `es])))
                              []))
                            [])
                           (Term.doSeqItem
                            (Term.doExpr
                             (Term.app
                              `pure
                              [(Term.tuple
                                "("
                                [(Term.app
                                  `merge_list
                                  [`rcases_patt.merge (Term.proj `r "." (fieldIdx "1")) `ps])
                                 ","
                                 [(«term_++_» (Term.proj `r "." (fieldIdx "2")) "++" `gs')]]
                                ")")]))
                            [])]))))
                      (Term.tuple "(" [(«term[_]» "[" [] "]") "," [(«term[_]» "[" [] "]")]] ")")]))
                   []))
                 [])
                (Term.doSeqItem
                 (Term.doExpr
                  (Term.app
                   `pure
                   [(Term.tuple
                     "("
                     [(Term.match
                       "match"
                       []
                       []
                       [(Term.matchDiscr [] `p)]
                       "with"
                       (Term.matchAlts
                        [(Term.matchAlt "|" [[`none]] "=>" `ps)
                         (Term.matchAlt
                          "|"
                          [[(Term.app `some [`p])]]
                          "=>"
                          («term_::_» `p "::" `ps))]))
                      ","
                      [`gs']]
                     ")")]))
                 [])])))])
          []))
        []
        []
        []))]
     "end"
     []
     [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValEqns', expected 'Lean.Parser.Command.declValSimple'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.do
       "do"
       (Term.doSeqIndent
        [(Term.doSeqItem
          (Term.doLetArrow
           "let"
           []
           (Term.doPatDecl
            (Term.tuple "(" [`p "," [`gs]] ")")
            "←"
            (Term.doExpr (Term.app `rcases_hint_core [`false `depth `e]))
            []))
          [])
         (Term.doSeqItem
          (Term.doLetArrow
           "let"
           []
           (Term.doPatDecl
            (Term.tuple "(" [`ps "," [`gs']] ")")
            "←"
            (Term.doExpr
             (Term.app
              (Term.proj `gs "." `mfoldl)
              [(Term.fun
                "fun"
                (Term.basicFun
                 [(Term.typeAscription
                   "("
                   (Term.app `r [])
                   ":"
                   [(«term_×_»
                     (Term.app (Tactic.Tactic.Rcases.«termlistΠ» "listΠ") [`rcases_patt])
                     "×"
                     (Term.app `List [`expr]))]
                   ")")
                  `g]
                 []
                 "=>"
                 (Term.do
                  "do"
                  (Term.doSeqIndent
                   [(Term.doSeqItem
                     (Term.doLetArrow
                      "let"
                      []
                      (Term.doPatDecl
                       (Term.tuple "(" [`ps "," [`gs']] ")")
                       "←"
                       (Term.doExpr
                        («term_>>_»
                         (Term.app `set_goals [(«term[_]» "[" [`g] "]")])
                         ">>"
                         (Term.app `rcases_hint.continue [`depth `es])))
                       []))
                     [])
                    (Term.doSeqItem
                     (Term.doExpr
                      (Term.app
                       `pure
                       [(Term.tuple
                         "("
                         [(Term.app
                           `merge_list
                           [`rcases_patt.merge (Term.proj `r "." (fieldIdx "1")) `ps])
                          ","
                          [(«term_++_» (Term.proj `r "." (fieldIdx "2")) "++" `gs')]]
                         ")")]))
                     [])]))))
               (Term.tuple "(" [(«term[_]» "[" [] "]") "," [(«term[_]» "[" [] "]")]] ")")]))
            []))
          [])
         (Term.doSeqItem
          (Term.doExpr
           (Term.app
            `pure
            [(Term.tuple
              "("
              [(Term.match
                "match"
                []
                []
                [(Term.matchDiscr [] `p)]
                "with"
                (Term.matchAlts
                 [(Term.matchAlt "|" [[`none]] "=>" `ps)
                  (Term.matchAlt "|" [[(Term.app `some [`p])]] "=>" («term_::_» `p "::" `ps))]))
               ","
               [`gs']]
              ")")]))
          [])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doSeqIndent', expected 'Lean.Parser.Term.doSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `pure
       [(Term.tuple
         "("
         [(Term.match
           "match"
           []
           []
           [(Term.matchDiscr [] `p)]
           "with"
           (Term.matchAlts
            [(Term.matchAlt "|" [[`none]] "=>" `ps)
             (Term.matchAlt "|" [[(Term.app `some [`p])]] "=>" («term_::_» `p "::" `ps))]))
          ","
          [`gs']]
         ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.tuple', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.tuple', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.tuple
       "("
       [(Term.match
         "match"
         []
         []
         [(Term.matchDiscr [] `p)]
         "with"
         (Term.matchAlts
          [(Term.matchAlt "|" [[`none]] "=>" `ps)
           (Term.matchAlt "|" [[(Term.app `some [`p])]] "=>" («term_::_» `p "::" `ps))]))
        ","
        [`gs']]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `gs'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.match
       "match"
       []
       []
       [(Term.matchDiscr [] `p)]
       "with"
       (Term.matchAlts
        [(Term.matchAlt "|" [[`none]] "=>" `ps)
         (Term.matchAlt "|" [[(Term.app `some [`p])]] "=>" («term_::_» `p "::" `ps))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_::_» `p "::" `ps)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ps
[PrettyPrinter.parenthesize] ...precedences are 67 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 67, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 68 >? 1024, (none, [anonymous]) <=? (some 67, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 67, (some 67, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `some [`p])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `some
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      `ps
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `none
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `pure
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doPatDecl', expected 'Lean.Parser.Term.doIdDecl'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, doElem))
      (Term.app
       (Term.proj `gs "." `mfoldl)
       [(Term.fun
         "fun"
         (Term.basicFun
          [(Term.typeAscription
            "("
            (Term.app `r [])
            ":"
            [(«term_×_»
              (Term.app (Tactic.Tactic.Rcases.«termlistΠ» "listΠ") [`rcases_patt])
              "×"
              (Term.app `List [`expr]))]
            ")")
           `g]
          []
          "=>"
          (Term.do
           "do"
           (Term.doSeqIndent
            [(Term.doSeqItem
              (Term.doLetArrow
               "let"
               []
               (Term.doPatDecl
                (Term.tuple "(" [`ps "," [`gs']] ")")
                "←"
                (Term.doExpr
                 («term_>>_»
                  (Term.app `set_goals [(«term[_]» "[" [`g] "]")])
                  ">>"
                  (Term.app `rcases_hint.continue [`depth `es])))
                []))
              [])
             (Term.doSeqItem
              (Term.doExpr
               (Term.app
                `pure
                [(Term.tuple
                  "("
                  [(Term.app `merge_list [`rcases_patt.merge (Term.proj `r "." (fieldIdx "1")) `ps])
                   ","
                   [(«term_++_» (Term.proj `r "." (fieldIdx "2")) "++" `gs')]]
                  ")")]))
              [])]))))
        (Term.tuple "(" [(«term[_]» "[" [] "]") "," [(«term[_]» "[" [] "]")]] ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.tuple', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.tuple', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.tuple "(" [(«term[_]» "[" [] "]") "," [(«term[_]» "[" [] "]")]] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term[_]» "[" [] "]")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term[_]» "[" [] "]")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.fun
       "fun"
       (Term.basicFun
        [(Term.typeAscription
          "("
          (Term.app `r [])
          ":"
          [(«term_×_»
            (Term.app (Tactic.Tactic.Rcases.«termlistΠ» "listΠ") [`rcases_patt])
            "×"
            (Term.app `List [`expr]))]
          ")")
         `g]
        []
        "=>"
        (Term.do
         "do"
         (Term.doSeqIndent
          [(Term.doSeqItem
            (Term.doLetArrow
             "let"
             []
             (Term.doPatDecl
              (Term.tuple "(" [`ps "," [`gs']] ")")
              "←"
              (Term.doExpr
               («term_>>_»
                (Term.app `set_goals [(«term[_]» "[" [`g] "]")])
                ">>"
                (Term.app `rcases_hint.continue [`depth `es])))
              []))
            [])
           (Term.doSeqItem
            (Term.doExpr
             (Term.app
              `pure
              [(Term.tuple
                "("
                [(Term.app `merge_list [`rcases_patt.merge (Term.proj `r "." (fieldIdx "1")) `ps])
                 ","
                 [(«term_++_» (Term.proj `r "." (fieldIdx "2")) "++" `gs')]]
                ")")]))
            [])]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.do
       "do"
       (Term.doSeqIndent
        [(Term.doSeqItem
          (Term.doLetArrow
           "let"
           []
           (Term.doPatDecl
            (Term.tuple "(" [`ps "," [`gs']] ")")
            "←"
            (Term.doExpr
             («term_>>_»
              (Term.app `set_goals [(«term[_]» "[" [`g] "]")])
              ">>"
              (Term.app `rcases_hint.continue [`depth `es])))
            []))
          [])
         (Term.doSeqItem
          (Term.doExpr
           (Term.app
            `pure
            [(Term.tuple
              "("
              [(Term.app `merge_list [`rcases_patt.merge (Term.proj `r "." (fieldIdx "1")) `ps])
               ","
               [(«term_++_» (Term.proj `r "." (fieldIdx "2")) "++" `gs')]]
              ")")]))
          [])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doSeqIndent', expected 'Lean.Parser.Term.doSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `pure
       [(Term.tuple
         "("
         [(Term.app `merge_list [`rcases_patt.merge (Term.proj `r "." (fieldIdx "1")) `ps])
          ","
          [(«term_++_» (Term.proj `r "." (fieldIdx "2")) "++" `gs')]]
         ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.tuple', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.tuple', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.tuple
       "("
       [(Term.app `merge_list [`rcases_patt.merge (Term.proj `r "." (fieldIdx "1")) `ps])
        ","
        [(«term_++_» (Term.proj `r "." (fieldIdx "2")) "++" `gs')]]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_++_» (Term.proj `r "." (fieldIdx "2")) "++" `gs')
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `gs'
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      (Term.proj `r "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `r
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `merge_list [`rcases_patt.merge (Term.proj `r "." (fieldIdx "1")) `ps])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ps
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj `r "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `r
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `rcases_patt.merge
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `merge_list
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `pure
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doPatDecl', expected 'Lean.Parser.Term.doIdDecl'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, doElem))
      («term_>>_»
       (Term.app `set_goals [(«term[_]» "[" [`g] "]")])
       ">>"
       (Term.app `rcases_hint.continue [`depth `es]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `rcases_hint.continue [`depth `es])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `es
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `depth
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `rcases_hint.continue
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 60 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 60, term))
      (Term.app `set_goals [(«term[_]» "[" [`g] "]")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term[_]»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term[_]»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term[_]» "[" [`g] "]")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `set_goals
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 61 >? 1022, (some 1023, term) <=? (some 60, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 60, (some 60, term) <=? (none, doElem)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.tuple "(" [`ps "," [`gs']] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `gs'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ps
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1023, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.typeAscription
       "("
       (Term.app `r [])
       ":"
       [(«term_×_»
         (Term.app (Tactic.Tactic.Rcases.«termlistΠ» "listΠ") [`rcases_patt])
         "×"
         (Term.app `List [`expr]))]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_×_»
       (Term.app (Tactic.Tactic.Rcases.«termlistΠ» "listΠ") [`rcases_patt])
       "×"
       (Term.app `List [`expr]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `List [`expr])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `expr
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `List
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 35 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 35, term))
      (Term.app (Tactic.Tactic.Rcases.«termlistΠ» "listΠ") [`rcases_patt])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rcases_patt
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Tactic.Tactic.Rcases.«termlistΠ» "listΠ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Tactic.Tactic.Rcases.«termlistΠ»', expected 'Tactic.Tactic.Rcases.termlistΠ._@.Tactic.Rcases._hyg.324'
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
mutual
  /--
          * `rcases_hint_core depth e` does the same as `rcases p e`, except the pattern `p` is an output
            instead of an input, controlled only by the case depth argument `depth`. We use `cases` to depth
            `depth` and then reconstruct an `rcases` pattern `p` that would, if passed to `rcases`, perform
            the same thing as the case tree we just constructed (or at least, the nearest expressible
            approximation to this.)
          * `rcases_hint.process_constructors depth cs l` takes a list of constructor names `cs` and a
            matching list `l` of elements `(g, c', hs, _)` where  `c'` is a constructor name (used for
            alignment with `cs`), `g` is the subgoal, and `hs` is the list of local hypotheses created by
            `cases` in that subgoal. It matches on all of them, and then produces a `ΣΠ`-list of `rcases`
            patterns describing the result, and the list of generated subgoals.
          * `rcases_hint.continue depth es` does the same as `rcases.continue (ps.zip es)`, except the
            patterns `ps` are an output instead of an input, created by matching on everything to depth
            `depth` and recording the successful cases. It returns `ps`, and the list of generated subgoals.
          -/
        unsafe
      def
        rcases_hint_core
        ( explicit : Bool ) : Bool → ℕ → expr → tactic Option rcases_patt × List expr
        |
          force , depth , e
          =>
          do
            let ( t , e ) ← get_local_and_type e
              let
                tt
                  ←
                  pure explicit || force || e . local_binding_info = BinderInfo.default
                  | Prod.mk none <$> get_goals
              let t ← whnf t
              let env ← get_env
              let I := t . get_app_fn . const_name
              do guard I = ` ` Eq subst' e Prod.mk some rcases_patt.one `rfl <$> get_goals
                <|>
                do
                  let c := env I
                    let
                      some l
                        ←
                        try_core guard depth ≠ 0 >> cases_core e
                        |
                          let
                            n := match e with | Name.anonymous => `_ | n => n
                            Prod.mk some rcases_patt.one n <$> get_goals
                    let gs ← get_goals
                    if
                      gs
                      then
                      pure ( some rcases_patt.tuple [ ] , [ ] )
                      else
                      do
                        let ( ps , gs' ) ← rcases_hint.process_constructors depth - 1 c gs l
                          pure ( some rcases_patt.alts₁ ps , gs' )
    /--
          * `rcases_hint_core depth e` does the same as `rcases p e`, except the pattern `p` is an output
            instead of an input, controlled only by the case depth argument `depth`. We use `cases` to depth
            `depth` and then reconstruct an `rcases` pattern `p` that would, if passed to `rcases`, perform
            the same thing as the case tree we just constructed (or at least, the nearest expressible
            approximation to this.)
          * `rcases_hint.process_constructors depth cs l` takes a list of constructor names `cs` and a
            matching list `l` of elements `(g, c', hs, _)` where  `c'` is a constructor name (used for
            alignment with `cs`), `g` is the subgoal, and `hs` is the list of local hypotheses created by
            `cases` in that subgoal. It matches on all of them, and then produces a `ΣΠ`-list of `rcases`
            patterns describing the result, and the list of generated subgoals.
          * `rcases_hint.continue depth es` does the same as `rcases.continue (ps.zip es)`, except the
            patterns `ps` are an output instead of an input, created by matching on everything to depth
            `depth` and recording the successful cases. It returns `ps`, and the list of generated subgoals.
          -/
        unsafe
      def
        rcases_hint.process_constructors
        ( explicit : Bool )
          :
            ℕ
              →
              listΣ Name
                →
                List expr × Name × listΠ expr × List Name × expr
                  →
                  tactic listΣ listΠ rcases_patt × List expr
        | depth , [ ] , _ => pure ( [ ] , [ ] )
          | depth , cs , [ ] => pure ( cs . map fun _ => [ ] , [ ] )
          |
            depth , c :: cs , ls @ ( g , c' , hs , _ ) :: l
            =>
            if
              c ≠ c'
              then
              do
                let ( ps , gs ) ← rcases_hint.process_constructors depth cs ls
                  pure ( [ ] :: ps , gs )
              else
              do
                let ( p , gs ) ← set_goals [ g ] >> rcases_hint.continue depth hs
                  let ( ps , gs' ) ← rcases_hint.process_constructors depth cs l
                  pure ( p :: ps , gs ++ gs' )
    /--
          * `rcases_hint_core depth e` does the same as `rcases p e`, except the pattern `p` is an output
            instead of an input, controlled only by the case depth argument `depth`. We use `cases` to depth
            `depth` and then reconstruct an `rcases` pattern `p` that would, if passed to `rcases`, perform
            the same thing as the case tree we just constructed (or at least, the nearest expressible
            approximation to this.)
          * `rcases_hint.process_constructors depth cs l` takes a list of constructor names `cs` and a
            matching list `l` of elements `(g, c', hs, _)` where  `c'` is a constructor name (used for
            alignment with `cs`), `g` is the subgoal, and `hs` is the list of local hypotheses created by
            `cases` in that subgoal. It matches on all of them, and then produces a `ΣΠ`-list of `rcases`
            patterns describing the result, and the list of generated subgoals.
          * `rcases_hint.continue depth es` does the same as `rcases.continue (ps.zip es)`, except the
            patterns `ps` are an output instead of an input, created by matching on everything to depth
            `depth` and recording the successful cases. It returns `ps`, and the list of generated subgoals.
          -/
        unsafe
      def
        rcases_hint.continue
        ( explicit : Bool ) : ℕ → listΠ expr → tactic listΠ rcases_patt × List expr
        | depth , [ ] => Prod.mk [ ] <$> get_goals
          |
            depth , e :: es
            =>
            do
              let ( p , gs ) ← rcases_hint_core false depth e
                let
                  ( ps , gs' )
                    ←
                    gs . mfoldl
                      fun
                          ( r : listΠ rcases_patt × List expr ) g
                            =>
                            do
                              let ( ps , gs' ) ← set_goals [ g ] >> rcases_hint.continue depth es
                                pure ( merge_list rcases_patt.merge r . 1 ps , r . 2 ++ gs' )
                        ( [ ] , [ ] )
                pure ( match p with | none => ps | some p => p :: ps , gs' )
  end
#align tactic.rcases_hint_core tactic.rcases_hint_core
#align tactic.rcases_hint.process_constructors tactic.rcases_hint.process_constructors
#align tactic.rcases_hint.continue tactic.rcases_hint.continue

/--
* `rcases? e` is like `rcases e with ...`, except it generates `...` by matching on everything it
can, and it outputs an `rcases` invocation that should have the same effect.
* `rcases? e : n` can be used to control the depth of case splits (especially important for
recursive types like `nat`, which can be cased as many times as you like). -/
unsafe def rcases_hint (p : pexpr) (depth : Nat) : tactic rcases_patt := do
  let e ← i_to_expr p
  if e then
      focus1 do
        let (p, gs) ← rcases_hint_core ff tt depth e
        set_goals gs
        pure (p default)
    else do
      let x ← mk_fresh_name
      let n ← revert_kdependencies e semireducible
      tactic.generalize e x <|> do
          let t ← infer_type e
          tactic.assertv x t e
          get_local x >>= tactic.revert
          pure ()
      let h ← tactic.intro1
      focus1 do
          let (p, gs) ← rcases_hint_core ff tt depth h
          set_goals gs
          pure (p default)
#align tactic.rcases_hint tactic.rcases_hint

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "* `rcases? ⟨e1, e2, e3⟩` is like `rcases ⟨e1, e2, e3⟩ with ...`, except it\n  generates `...` by matching on everything it can, and it outputs an `rcases`\n  invocation that should have the same effect.\n* `rcases? ⟨e1, e2, e3⟩ : n` can be used to control the depth of case splits\n  (especially important for recursive types like `nat`, which can be cased as many\n  times as you like). -/")]
      []
      []
      []
      [(Command.unsafe "unsafe")]
      [])
     (Command.def
      "def"
      (Command.declId `rcases_hint_many [])
      (Command.optDeclSig
       [(Term.explicitBinder "(" [`ps] [":" (Term.app `List [`pexpr])] [] ")")
        (Term.explicitBinder "(" [`depth] [":" `Nat] [] ")")]
       [(Term.typeSpec
         ":"
         (Term.app
          `tactic
          [(Term.app (Tactic.Tactic.Rcases.«termlistΠ» "listΠ") [`rcases_patt])]))])
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
             `es
             []
             "←"
             (Term.doExpr
              (Term.app
               (Term.proj `ps "." `mmap)
               [(Term.fun
                 "fun"
                 (Term.basicFun
                  [`p]
                  []
                  "=>"
                  (Term.do
                   "do"
                   (Term.doSeqIndent
                    [(Term.doSeqItem
                      (Term.doLetArrow
                       "let"
                       []
                       (Term.doIdDecl `e [] "←" (Term.doExpr (Term.app `i_to_expr [`p]))))
                      [])
                     (Term.doSeqItem
                      (Term.doExpr
                       (termIfThenElse
                        "if"
                        `e
                        "then"
                        (Term.app `pure [`e])
                        "else"
                        (Term.do
                         "do"
                         (Term.doSeqIndent
                          [(Term.doSeqItem
                            (Term.doLetArrow
                             "let"
                             []
                             (Term.doIdDecl `x [] "←" (Term.doExpr `mk_fresh_name)))
                            [])
                           (Term.doSeqItem
                            (Term.doLetArrow
                             "let"
                             []
                             (Term.doIdDecl
                              `n
                              []
                              "←"
                              (Term.doExpr (Term.app `revert_kdependencies [`e `semireducible]))))
                            [])
                           (Term.doSeqItem
                            (Term.doExpr
                             («term_<|>_»
                              (Term.app `tactic.generalize [`e `x])
                              "<|>"
                              (Term.do
                               "do"
                               (Term.doSeqIndent
                                [(Term.doSeqItem
                                  (Term.doLetArrow
                                   "let"
                                   []
                                   (Term.doIdDecl
                                    `t
                                    []
                                    "←"
                                    (Term.doExpr (Term.app `infer_type [`e]))))
                                  [])
                                 (Term.doSeqItem
                                  (Term.doExpr (Term.app `tactic.assertv [`x `t `e]))
                                  [])
                                 (Term.doSeqItem
                                  (Term.doExpr
                                   («term_>>=_» (Term.app `get_local [`x]) ">>=" `tactic.revert))
                                  [])
                                 (Term.doSeqItem
                                  (Term.doExpr (Term.app `pure [(Term.tuple "(" [] ")")]))
                                  [])]))))
                            [])
                           (Term.doSeqItem (Term.doExpr `tactic.intro1) [])]))))
                      [])]))))]))))
           [])
          (Term.doSeqItem
           (Term.doExpr
            (Term.app
             `focus1
             [(Term.do
               "do"
               (Term.doSeqIndent
                [(Term.doSeqItem
                  (Term.doLetArrow
                   "let"
                   []
                   (Term.doPatDecl
                    (Term.tuple "(" [`ps "," [`gs]] ")")
                    "←"
                    (Term.doExpr (Term.app `rcases_hint.continue [`ff `depth `es]))
                    []))
                  [])
                 (Term.doSeqItem (Term.doExpr (Term.app `set_goals [`gs])) [])
                 (Term.doSeqItem (Term.doExpr (Term.app `pure [`ps])) [])]))]))
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
            `es
            []
            "←"
            (Term.doExpr
             (Term.app
              (Term.proj `ps "." `mmap)
              [(Term.fun
                "fun"
                (Term.basicFun
                 [`p]
                 []
                 "=>"
                 (Term.do
                  "do"
                  (Term.doSeqIndent
                   [(Term.doSeqItem
                     (Term.doLetArrow
                      "let"
                      []
                      (Term.doIdDecl `e [] "←" (Term.doExpr (Term.app `i_to_expr [`p]))))
                     [])
                    (Term.doSeqItem
                     (Term.doExpr
                      (termIfThenElse
                       "if"
                       `e
                       "then"
                       (Term.app `pure [`e])
                       "else"
                       (Term.do
                        "do"
                        (Term.doSeqIndent
                         [(Term.doSeqItem
                           (Term.doLetArrow
                            "let"
                            []
                            (Term.doIdDecl `x [] "←" (Term.doExpr `mk_fresh_name)))
                           [])
                          (Term.doSeqItem
                           (Term.doLetArrow
                            "let"
                            []
                            (Term.doIdDecl
                             `n
                             []
                             "←"
                             (Term.doExpr (Term.app `revert_kdependencies [`e `semireducible]))))
                           [])
                          (Term.doSeqItem
                           (Term.doExpr
                            («term_<|>_»
                             (Term.app `tactic.generalize [`e `x])
                             "<|>"
                             (Term.do
                              "do"
                              (Term.doSeqIndent
                               [(Term.doSeqItem
                                 (Term.doLetArrow
                                  "let"
                                  []
                                  (Term.doIdDecl
                                   `t
                                   []
                                   "←"
                                   (Term.doExpr (Term.app `infer_type [`e]))))
                                 [])
                                (Term.doSeqItem
                                 (Term.doExpr (Term.app `tactic.assertv [`x `t `e]))
                                 [])
                                (Term.doSeqItem
                                 (Term.doExpr
                                  («term_>>=_» (Term.app `get_local [`x]) ">>=" `tactic.revert))
                                 [])
                                (Term.doSeqItem
                                 (Term.doExpr (Term.app `pure [(Term.tuple "(" [] ")")]))
                                 [])]))))
                           [])
                          (Term.doSeqItem (Term.doExpr `tactic.intro1) [])]))))
                     [])]))))]))))
          [])
         (Term.doSeqItem
          (Term.doExpr
           (Term.app
            `focus1
            [(Term.do
              "do"
              (Term.doSeqIndent
               [(Term.doSeqItem
                 (Term.doLetArrow
                  "let"
                  []
                  (Term.doPatDecl
                   (Term.tuple "(" [`ps "," [`gs]] ")")
                   "←"
                   (Term.doExpr (Term.app `rcases_hint.continue [`ff `depth `es]))
                   []))
                 [])
                (Term.doSeqItem (Term.doExpr (Term.app `set_goals [`gs])) [])
                (Term.doSeqItem (Term.doExpr (Term.app `pure [`ps])) [])]))]))
          [])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doSeqIndent', expected 'Lean.Parser.Term.doSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `focus1
       [(Term.do
         "do"
         (Term.doSeqIndent
          [(Term.doSeqItem
            (Term.doLetArrow
             "let"
             []
             (Term.doPatDecl
              (Term.tuple "(" [`ps "," [`gs]] ")")
              "←"
              (Term.doExpr (Term.app `rcases_hint.continue [`ff `depth `es]))
              []))
            [])
           (Term.doSeqItem (Term.doExpr (Term.app `set_goals [`gs])) [])
           (Term.doSeqItem (Term.doExpr (Term.app `pure [`ps])) [])]))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.do', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.do', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.do
       "do"
       (Term.doSeqIndent
        [(Term.doSeqItem
          (Term.doLetArrow
           "let"
           []
           (Term.doPatDecl
            (Term.tuple "(" [`ps "," [`gs]] ")")
            "←"
            (Term.doExpr (Term.app `rcases_hint.continue [`ff `depth `es]))
            []))
          [])
         (Term.doSeqItem (Term.doExpr (Term.app `set_goals [`gs])) [])
         (Term.doSeqItem (Term.doExpr (Term.app `pure [`ps])) [])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doSeqIndent', expected 'Lean.Parser.Term.doSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `pure [`ps])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ps
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `pure
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, doElem))
      (Term.app `set_goals [`gs])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `gs
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `set_goals
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1023, doElem)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doPatDecl', expected 'Lean.Parser.Term.doIdDecl'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, doElem))
      (Term.app `rcases_hint.continue [`ff `depth `es])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `es
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `depth
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `ff
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `rcases_hint.continue
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, doElem)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.tuple "(" [`ps "," [`gs]] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `gs
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ps
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1023, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `focus1
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, doElem))
      (Term.app
       (Term.proj `ps "." `mmap)
       [(Term.fun
         "fun"
         (Term.basicFun
          [`p]
          []
          "=>"
          (Term.do
           "do"
           (Term.doSeqIndent
            [(Term.doSeqItem
              (Term.doLetArrow
               "let"
               []
               (Term.doIdDecl `e [] "←" (Term.doExpr (Term.app `i_to_expr [`p]))))
              [])
             (Term.doSeqItem
              (Term.doExpr
               (termIfThenElse
                "if"
                `e
                "then"
                (Term.app `pure [`e])
                "else"
                (Term.do
                 "do"
                 (Term.doSeqIndent
                  [(Term.doSeqItem
                    (Term.doLetArrow
                     "let"
                     []
                     (Term.doIdDecl `x [] "←" (Term.doExpr `mk_fresh_name)))
                    [])
                   (Term.doSeqItem
                    (Term.doLetArrow
                     "let"
                     []
                     (Term.doIdDecl
                      `n
                      []
                      "←"
                      (Term.doExpr (Term.app `revert_kdependencies [`e `semireducible]))))
                    [])
                   (Term.doSeqItem
                    (Term.doExpr
                     («term_<|>_»
                      (Term.app `tactic.generalize [`e `x])
                      "<|>"
                      (Term.do
                       "do"
                       (Term.doSeqIndent
                        [(Term.doSeqItem
                          (Term.doLetArrow
                           "let"
                           []
                           (Term.doIdDecl `t [] "←" (Term.doExpr (Term.app `infer_type [`e]))))
                          [])
                         (Term.doSeqItem (Term.doExpr (Term.app `tactic.assertv [`x `t `e])) [])
                         (Term.doSeqItem
                          (Term.doExpr
                           («term_>>=_» (Term.app `get_local [`x]) ">>=" `tactic.revert))
                          [])
                         (Term.doSeqItem
                          (Term.doExpr (Term.app `pure [(Term.tuple "(" [] ")")]))
                          [])]))))
                    [])
                   (Term.doSeqItem (Term.doExpr `tactic.intro1) [])]))))
              [])]))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`p]
        []
        "=>"
        (Term.do
         "do"
         (Term.doSeqIndent
          [(Term.doSeqItem
            (Term.doLetArrow
             "let"
             []
             (Term.doIdDecl `e [] "←" (Term.doExpr (Term.app `i_to_expr [`p]))))
            [])
           (Term.doSeqItem
            (Term.doExpr
             (termIfThenElse
              "if"
              `e
              "then"
              (Term.app `pure [`e])
              "else"
              (Term.do
               "do"
               (Term.doSeqIndent
                [(Term.doSeqItem
                  (Term.doLetArrow "let" [] (Term.doIdDecl `x [] "←" (Term.doExpr `mk_fresh_name)))
                  [])
                 (Term.doSeqItem
                  (Term.doLetArrow
                   "let"
                   []
                   (Term.doIdDecl
                    `n
                    []
                    "←"
                    (Term.doExpr (Term.app `revert_kdependencies [`e `semireducible]))))
                  [])
                 (Term.doSeqItem
                  (Term.doExpr
                   («term_<|>_»
                    (Term.app `tactic.generalize [`e `x])
                    "<|>"
                    (Term.do
                     "do"
                     (Term.doSeqIndent
                      [(Term.doSeqItem
                        (Term.doLetArrow
                         "let"
                         []
                         (Term.doIdDecl `t [] "←" (Term.doExpr (Term.app `infer_type [`e]))))
                        [])
                       (Term.doSeqItem (Term.doExpr (Term.app `tactic.assertv [`x `t `e])) [])
                       (Term.doSeqItem
                        (Term.doExpr («term_>>=_» (Term.app `get_local [`x]) ">>=" `tactic.revert))
                        [])
                       (Term.doSeqItem
                        (Term.doExpr (Term.app `pure [(Term.tuple "(" [] ")")]))
                        [])]))))
                  [])
                 (Term.doSeqItem (Term.doExpr `tactic.intro1) [])]))))
            [])]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.do
       "do"
       (Term.doSeqIndent
        [(Term.doSeqItem
          (Term.doLetArrow
           "let"
           []
           (Term.doIdDecl `e [] "←" (Term.doExpr (Term.app `i_to_expr [`p]))))
          [])
         (Term.doSeqItem
          (Term.doExpr
           (termIfThenElse
            "if"
            `e
            "then"
            (Term.app `pure [`e])
            "else"
            (Term.do
             "do"
             (Term.doSeqIndent
              [(Term.doSeqItem
                (Term.doLetArrow "let" [] (Term.doIdDecl `x [] "←" (Term.doExpr `mk_fresh_name)))
                [])
               (Term.doSeqItem
                (Term.doLetArrow
                 "let"
                 []
                 (Term.doIdDecl
                  `n
                  []
                  "←"
                  (Term.doExpr (Term.app `revert_kdependencies [`e `semireducible]))))
                [])
               (Term.doSeqItem
                (Term.doExpr
                 («term_<|>_»
                  (Term.app `tactic.generalize [`e `x])
                  "<|>"
                  (Term.do
                   "do"
                   (Term.doSeqIndent
                    [(Term.doSeqItem
                      (Term.doLetArrow
                       "let"
                       []
                       (Term.doIdDecl `t [] "←" (Term.doExpr (Term.app `infer_type [`e]))))
                      [])
                     (Term.doSeqItem (Term.doExpr (Term.app `tactic.assertv [`x `t `e])) [])
                     (Term.doSeqItem
                      (Term.doExpr («term_>>=_» (Term.app `get_local [`x]) ">>=" `tactic.revert))
                      [])
                     (Term.doSeqItem
                      (Term.doExpr (Term.app `pure [(Term.tuple "(" [] ")")]))
                      [])]))))
                [])
               (Term.doSeqItem (Term.doExpr `tactic.intro1) [])]))))
          [])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doSeqIndent', expected 'Lean.Parser.Term.doSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (termIfThenElse
       "if"
       `e
       "then"
       (Term.app `pure [`e])
       "else"
       (Term.do
        "do"
        (Term.doSeqIndent
         [(Term.doSeqItem
           (Term.doLetArrow "let" [] (Term.doIdDecl `x [] "←" (Term.doExpr `mk_fresh_name)))
           [])
          (Term.doSeqItem
           (Term.doLetArrow
            "let"
            []
            (Term.doIdDecl
             `n
             []
             "←"
             (Term.doExpr (Term.app `revert_kdependencies [`e `semireducible]))))
           [])
          (Term.doSeqItem
           (Term.doExpr
            («term_<|>_»
             (Term.app `tactic.generalize [`e `x])
             "<|>"
             (Term.do
              "do"
              (Term.doSeqIndent
               [(Term.doSeqItem
                 (Term.doLetArrow
                  "let"
                  []
                  (Term.doIdDecl `t [] "←" (Term.doExpr (Term.app `infer_type [`e]))))
                 [])
                (Term.doSeqItem (Term.doExpr (Term.app `tactic.assertv [`x `t `e])) [])
                (Term.doSeqItem
                 (Term.doExpr («term_>>=_» (Term.app `get_local [`x]) ">>=" `tactic.revert))
                 [])
                (Term.doSeqItem (Term.doExpr (Term.app `pure [(Term.tuple "(" [] ")")])) [])]))))
           [])
          (Term.doSeqItem (Term.doExpr `tactic.intro1) [])])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.do
       "do"
       (Term.doSeqIndent
        [(Term.doSeqItem
          (Term.doLetArrow "let" [] (Term.doIdDecl `x [] "←" (Term.doExpr `mk_fresh_name)))
          [])
         (Term.doSeqItem
          (Term.doLetArrow
           "let"
           []
           (Term.doIdDecl
            `n
            []
            "←"
            (Term.doExpr (Term.app `revert_kdependencies [`e `semireducible]))))
          [])
         (Term.doSeqItem
          (Term.doExpr
           («term_<|>_»
            (Term.app `tactic.generalize [`e `x])
            "<|>"
            (Term.do
             "do"
             (Term.doSeqIndent
              [(Term.doSeqItem
                (Term.doLetArrow
                 "let"
                 []
                 (Term.doIdDecl `t [] "←" (Term.doExpr (Term.app `infer_type [`e]))))
                [])
               (Term.doSeqItem (Term.doExpr (Term.app `tactic.assertv [`x `t `e])) [])
               (Term.doSeqItem
                (Term.doExpr («term_>>=_» (Term.app `get_local [`x]) ">>=" `tactic.revert))
                [])
               (Term.doSeqItem (Term.doExpr (Term.app `pure [(Term.tuple "(" [] ")")])) [])]))))
          [])
         (Term.doSeqItem (Term.doExpr `tactic.intro1) [])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doSeqIndent', expected 'Lean.Parser.Term.doSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `tactic.intro1
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, doElem))
      («term_<|>_»
       (Term.app `tactic.generalize [`e `x])
       "<|>"
       (Term.do
        "do"
        (Term.doSeqIndent
         [(Term.doSeqItem
           (Term.doLetArrow
            "let"
            []
            (Term.doIdDecl `t [] "←" (Term.doExpr (Term.app `infer_type [`e]))))
           [])
          (Term.doSeqItem (Term.doExpr (Term.app `tactic.assertv [`x `t `e])) [])
          (Term.doSeqItem
           (Term.doExpr («term_>>=_» (Term.app `get_local [`x]) ">>=" `tactic.revert))
           [])
          (Term.doSeqItem (Term.doExpr (Term.app `pure [(Term.tuple "(" [] ")")])) [])])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.do
       "do"
       (Term.doSeqIndent
        [(Term.doSeqItem
          (Term.doLetArrow
           "let"
           []
           (Term.doIdDecl `t [] "←" (Term.doExpr (Term.app `infer_type [`e]))))
          [])
         (Term.doSeqItem (Term.doExpr (Term.app `tactic.assertv [`x `t `e])) [])
         (Term.doSeqItem
          (Term.doExpr («term_>>=_» (Term.app `get_local [`x]) ">>=" `tactic.revert))
          [])
         (Term.doSeqItem (Term.doExpr (Term.app `pure [(Term.tuple "(" [] ")")])) [])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doSeqIndent', expected 'Lean.Parser.Term.doSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `pure [(Term.tuple "(" [] ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.tuple', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.tuple', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.tuple "(" [] ")")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `pure
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, doElem))
      («term_>>=_» (Term.app `get_local [`x]) ">>=" `tactic.revert)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `tactic.revert
[PrettyPrinter.parenthesize] ...precedences are 56 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 55, term))
      (Term.app `get_local [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `get_local
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 55 >? 1022, (some 1023, term) <=? (some 55, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 55, (some 56, term) <=? (some 1023, doElem)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, doElem))
      (Term.app `tactic.assertv [`x `t `e])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `e
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `t
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `tactic.assertv
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1023, doElem)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, doElem))
      (Term.app `infer_type [`e])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `e
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `infer_type
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, doElem)
[PrettyPrinter.parenthesize] ...precedences are 20 >? 1023, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 20, term))
      (Term.app `tactic.generalize [`e `x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `e
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `tactic.generalize
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 21 >? 1022, (some 1023, term) <=? (some 20, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 20, (some 0, term) <=? (some 1023, doElem)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, doElem))
      (Term.app `revert_kdependencies [`e `semireducible])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `semireducible
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `e
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `revert_kdependencies
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, doElem)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, doElem))
      `mk_fresh_name
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, doElem)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1023, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `pure [`e])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `e
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `pure
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `e
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, doElem))
      (Term.app `i_to_expr [`p])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `i_to_expr
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, doElem)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1023, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `ps "." `mmap)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `ps
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, doElem)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1023, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app `tactic [(Term.app (Tactic.Tactic.Rcases.«termlistΠ» "listΠ") [`rcases_patt])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Tactic.Tactic.Rcases.«termlistΠ» "listΠ") [`rcases_patt])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rcases_patt
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Tactic.Tactic.Rcases.«termlistΠ» "listΠ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Tactic.Tactic.Rcases.«termlistΠ»', expected 'Tactic.Tactic.Rcases.termlistΠ._@.Tactic.Rcases._hyg.324'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
      * `rcases? ⟨e1, e2, e3⟩` is like `rcases ⟨e1, e2, e3⟩ with ...`, except it
        generates `...` by matching on everything it can, and it outputs an `rcases`
        invocation that should have the same effect.
      * `rcases? ⟨e1, e2, e3⟩ : n` can be used to control the depth of case splits
        (especially important for recursive types like `nat`, which can be cased as many
        times as you like). -/
    unsafe
  def
    rcases_hint_many
    ( ps : List pexpr ) ( depth : Nat ) : tactic listΠ rcases_patt
    :=
      do
        let
            es
              ←
              ps . mmap
                fun
                  p
                    =>
                    do
                      let e ← i_to_expr p
                        if
                          e
                          then
                          pure e
                          else
                          do
                            let x ← mk_fresh_name
                              let n ← revert_kdependencies e semireducible
                              tactic.generalize e x
                                <|>
                                do
                                  let t ← infer_type e
                                    tactic.assertv x t e
                                    get_local x >>= tactic.revert
                                    pure ( )
                              tactic.intro1
          focus1 do let ( ps , gs ) ← rcases_hint.continue ff depth es set_goals gs pure ps
#align tactic.rcases_hint_many tactic.rcases_hint_many

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "* `rintro?` is like `rintro ...`, except it generates `...` by introducing and matching on\neverything it can, and it outputs an `rintro` invocation that should have the same effect.\n* `rintro? : n` can be used to control the depth of case splits (especially important for\nrecursive types like `nat`, which can be cased as many times as you like). -/")]
      []
      []
      []
      [(Command.unsafe "unsafe")]
      [])
     (Command.def
      "def"
      (Command.declId `rintro_hint [])
      (Command.optDeclSig
       [(Term.explicitBinder "(" [`depth] [":" `Nat] [] ")")]
       [(Term.typeSpec
         ":"
         (Term.app
          `tactic
          [(Term.app (Tactic.Tactic.Rcases.«termlistΠ» "listΠ") [`rcases_patt])]))])
      (Command.declValSimple
       ":="
       (Term.do
        "do"
        (Term.doSeqIndent
         [(Term.doSeqItem
           (Term.doLetArrow "let" [] (Term.doIdDecl `l [] "←" (Term.doExpr `intros)))
           [])
          (Term.doSeqItem
           (Term.doExpr
            (Term.app
             `focus1
             [(Term.do
               "do"
               (Term.doSeqIndent
                [(Term.doSeqItem
                  (Term.doLetArrow
                   "let"
                   []
                   (Term.doPatDecl
                    (Term.tuple "(" [`p "," [`gs]] ")")
                    "←"
                    (Term.doExpr (Term.app `rcases_hint.continue [`ff `depth `l]))
                    []))
                  [])
                 (Term.doSeqItem (Term.doExpr (Term.app `set_goals [`gs])) [])
                 (Term.doSeqItem (Term.doExpr (Term.app `pure [`p])) [])]))]))
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
          (Term.doLetArrow "let" [] (Term.doIdDecl `l [] "←" (Term.doExpr `intros)))
          [])
         (Term.doSeqItem
          (Term.doExpr
           (Term.app
            `focus1
            [(Term.do
              "do"
              (Term.doSeqIndent
               [(Term.doSeqItem
                 (Term.doLetArrow
                  "let"
                  []
                  (Term.doPatDecl
                   (Term.tuple "(" [`p "," [`gs]] ")")
                   "←"
                   (Term.doExpr (Term.app `rcases_hint.continue [`ff `depth `l]))
                   []))
                 [])
                (Term.doSeqItem (Term.doExpr (Term.app `set_goals [`gs])) [])
                (Term.doSeqItem (Term.doExpr (Term.app `pure [`p])) [])]))]))
          [])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doSeqIndent', expected 'Lean.Parser.Term.doSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `focus1
       [(Term.do
         "do"
         (Term.doSeqIndent
          [(Term.doSeqItem
            (Term.doLetArrow
             "let"
             []
             (Term.doPatDecl
              (Term.tuple "(" [`p "," [`gs]] ")")
              "←"
              (Term.doExpr (Term.app `rcases_hint.continue [`ff `depth `l]))
              []))
            [])
           (Term.doSeqItem (Term.doExpr (Term.app `set_goals [`gs])) [])
           (Term.doSeqItem (Term.doExpr (Term.app `pure [`p])) [])]))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.do', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.do', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.do
       "do"
       (Term.doSeqIndent
        [(Term.doSeqItem
          (Term.doLetArrow
           "let"
           []
           (Term.doPatDecl
            (Term.tuple "(" [`p "," [`gs]] ")")
            "←"
            (Term.doExpr (Term.app `rcases_hint.continue [`ff `depth `l]))
            []))
          [])
         (Term.doSeqItem (Term.doExpr (Term.app `set_goals [`gs])) [])
         (Term.doSeqItem (Term.doExpr (Term.app `pure [`p])) [])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doSeqIndent', expected 'Lean.Parser.Term.doSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `pure [`p])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `pure
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, doElem))
      (Term.app `set_goals [`gs])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `gs
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `set_goals
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1023, doElem)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doPatDecl', expected 'Lean.Parser.Term.doIdDecl'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, doElem))
      (Term.app `rcases_hint.continue [`ff `depth `l])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `l
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `depth
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `ff
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `rcases_hint.continue
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, doElem)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.tuple "(" [`p "," [`gs]] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `gs
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1023, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `focus1
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, doElem))
      `intros
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, doElem)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1023, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app `tactic [(Term.app (Tactic.Tactic.Rcases.«termlistΠ» "listΠ") [`rcases_patt])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Tactic.Tactic.Rcases.«termlistΠ» "listΠ") [`rcases_patt])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rcases_patt
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Tactic.Tactic.Rcases.«termlistΠ» "listΠ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Tactic.Tactic.Rcases.«termlistΠ»', expected 'Tactic.Tactic.Rcases.termlistΠ._@.Tactic.Rcases._hyg.324'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
      * `rintro?` is like `rintro ...`, except it generates `...` by introducing and matching on
      everything it can, and it outputs an `rintro` invocation that should have the same effect.
      * `rintro? : n` can be used to control the depth of case splits (especially important for
      recursive types like `nat`, which can be cased as many times as you like). -/
    unsafe
  def
    rintro_hint
    ( depth : Nat ) : tactic listΠ rcases_patt
    :=
      do
        let l ← intros
          focus1 do let ( p , gs ) ← rcases_hint.continue ff depth l set_goals gs pure p
#align tactic.rintro_hint tactic.rintro_hint

/- ./././Mathport/Syntax/Translate/Tactic/Mathlib/Core.lean:38:34: unsupported: setup_tactic_parser -/
/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.mutual
     "mutual"
     [(Command.declaration
       (Command.declModifiers
        [(Command.docComment
          "/--"
          "* `rcases_patt_parse_hi` will parse a high precedence `rcases` pattern, `patt_hi`.\n  This means only tuples and identifiers are allowed; alternations and type ascriptions\n  require `(...)` instead, which switches to `patt`.\n* `rcases_patt_parse` will parse a low precedence `rcases` pattern, `patt`. This consists of a\n  `patt_med` (which deals with alternations), optionally followed by a `: ty` type ascription. The\n  expression `ty` is at `texpr` precedence because it can appear at the end of a tactic, for\n  example in `rcases e with x : ty <|> skip`.\n* `rcases_patt_parse_list` will parse an alternation list, `patt_med`, one or more `patt`\n  patterns separated by `|`. It does not parse a `:` at the end, so that `a | b : ty` parses as\n  `(a | b) : ty` where `a | b` is the `patt_med` part.\n* `rcases_patt_parse_list_rest a` parses an alternation list after the initial pattern, `| b | c`.\n\n```lean\npatt ::= patt_med (\":\" expr)?\npatt_med ::= (patt_hi \"|\")* patt_hi\npatt_hi ::= id | \"rfl\" | \"_\" | \"@\" patt_hi | \"⟨\" (patt \",\")* patt \"⟩\" | \"(\" patt \")\"\n```\n-/")]
        []
        []
        []
        [(Command.unsafe "unsafe")]
        [])
       (Command.def
        "def"
        (Command.declId `rcases_patt_parse_hi' [])
        (Command.optDeclSig [] [(Term.typeSpec ":" (Term.app `parser [`rcases_patt]))])
        (Command.declValEqns
         (Term.matchAltsWhereDecls
          (Term.matchAlts
           [(Term.matchAlt
             "|"
             [[`x]]
             "=>"
             (Term.app
              («term_<|>_»
               (Term.app `brackets [(str "\"(\"") (str "\")\"") `rcases_patt_parse'])
               "<|>"
               («term_<|>_»
                («term_<$>_»
                 `rcases_patt.tuple
                 "<$>"
                 (Term.app
                  `brackets
                  [(str "\"⟨\"")
                   (str "\"⟩\"")
                   (Term.app `sep_by [(Term.app `tk [(str "\",\"")]) `rcases_patt_parse'])]))
                "<|>"
                («term_<|>_»
                 (Init.Control.Functor.«term_$>_»
                  (Term.app `tk [(str "\"-\"")])
                  " $> "
                  `rcases_patt.clear)
                 "<|>"
                 («term_<|>_»
                  («term_*>_»
                   (Term.app `tk [(str "\"@\"")])
                   "*>"
                   («term_<$>_» `rcases_patt.explicit "<$>" `rcases_patt_parse_hi'))
                  "<|>"
                  («term_<$>_» `rcases_patt.one "<$>" `ident_)))))
              [`x]))])
          []))
        []
        []
        []))
      (Command.declaration
       (Command.declModifiers
        [(Command.docComment
          "/--"
          "* `rcases_patt_parse_hi` will parse a high precedence `rcases` pattern, `patt_hi`.\n  This means only tuples and identifiers are allowed; alternations and type ascriptions\n  require `(...)` instead, which switches to `patt`.\n* `rcases_patt_parse` will parse a low precedence `rcases` pattern, `patt`. This consists of a\n  `patt_med` (which deals with alternations), optionally followed by a `: ty` type ascription. The\n  expression `ty` is at `texpr` precedence because it can appear at the end of a tactic, for\n  example in `rcases e with x : ty <|> skip`.\n* `rcases_patt_parse_list` will parse an alternation list, `patt_med`, one or more `patt`\n  patterns separated by `|`. It does not parse a `:` at the end, so that `a | b : ty` parses as\n  `(a | b) : ty` where `a | b` is the `patt_med` part.\n* `rcases_patt_parse_list_rest a` parses an alternation list after the initial pattern, `| b | c`.\n\n```lean\npatt ::= patt_med (\":\" expr)?\npatt_med ::= (patt_hi \"|\")* patt_hi\npatt_hi ::= id | \"rfl\" | \"_\" | \"@\" patt_hi | \"⟨\" (patt \",\")* patt \"⟩\" | \"(\" patt \")\"\n```\n-/")]
        []
        []
        []
        [(Command.unsafe "unsafe")]
        [])
       (Command.def
        "def"
        (Command.declId `rcases_patt_parse' [])
        (Command.optDeclSig [] [(Term.typeSpec ":" (Term.app `parser [`rcases_patt]))])
        (Command.declValEqns
         (Term.matchAltsWhereDecls
          (Term.matchAlts
           [(Term.matchAlt
             "|"
             [[`x]]
             "=>"
             (Term.app
              (Term.do
               "do"
               (Term.doSeqIndent
                [(Term.doSeqItem
                  (Term.doLetArrow
                   "let"
                   []
                   (Term.doIdDecl
                    `pat
                    []
                    "←"
                    (Term.doExpr («term_<$>_» `rcases_patt.alts' "<$>" `rcases_patt_parse_list'))))
                  [])
                 (Term.doSeqItem
                  (Term.doExpr
                   («term_<|>_»
                    («term_*>_» (Term.app `tk [(str "\":\"")]) "*>" («term_<$>_» `pat "<$>" `texpr))
                    "<|>"
                    (Term.app `pure [`pat])))
                  [])]))
              [`x]))])
          []))
        []
        []
        []))
      (Command.declaration
       (Command.declModifiers
        [(Command.docComment
          "/--"
          "* `rcases_patt_parse_hi` will parse a high precedence `rcases` pattern, `patt_hi`.\n  This means only tuples and identifiers are allowed; alternations and type ascriptions\n  require `(...)` instead, which switches to `patt`.\n* `rcases_patt_parse` will parse a low precedence `rcases` pattern, `patt`. This consists of a\n  `patt_med` (which deals with alternations), optionally followed by a `: ty` type ascription. The\n  expression `ty` is at `texpr` precedence because it can appear at the end of a tactic, for\n  example in `rcases e with x : ty <|> skip`.\n* `rcases_patt_parse_list` will parse an alternation list, `patt_med`, one or more `patt`\n  patterns separated by `|`. It does not parse a `:` at the end, so that `a | b : ty` parses as\n  `(a | b) : ty` where `a | b` is the `patt_med` part.\n* `rcases_patt_parse_list_rest a` parses an alternation list after the initial pattern, `| b | c`.\n\n```lean\npatt ::= patt_med (\":\" expr)?\npatt_med ::= (patt_hi \"|\")* patt_hi\npatt_hi ::= id | \"rfl\" | \"_\" | \"@\" patt_hi | \"⟨\" (patt \",\")* patt \"⟩\" | \"(\" patt \")\"\n```\n-/")]
        []
        []
        []
        [(Command.unsafe "unsafe")]
        [])
       (Command.def
        "def"
        (Command.declId `rcases_patt_parse_list' [])
        (Command.optDeclSig
         []
         [(Term.typeSpec
           ":"
           (Term.app
            `parser
            [(Term.app (Tactic.Tactic.Rcases.«termlistΣ» "listΣ") [`rcases_patt])]))])
        (Command.declValEqns
         (Term.matchAltsWhereDecls
          (Term.matchAlts
           [(Term.matchAlt
             "|"
             [[`x]]
             "=>"
             (Term.app
              («term_>>=_» `rcases_patt_parse_hi' ">>=" `rcases_patt_parse_list_rest)
              [`x]))])
          []))
        []
        []
        []))
      (Command.declaration
       (Command.declModifiers
        [(Command.docComment
          "/--"
          "* `rcases_patt_parse_hi` will parse a high precedence `rcases` pattern, `patt_hi`.\n  This means only tuples and identifiers are allowed; alternations and type ascriptions\n  require `(...)` instead, which switches to `patt`.\n* `rcases_patt_parse` will parse a low precedence `rcases` pattern, `patt`. This consists of a\n  `patt_med` (which deals with alternations), optionally followed by a `: ty` type ascription. The\n  expression `ty` is at `texpr` precedence because it can appear at the end of a tactic, for\n  example in `rcases e with x : ty <|> skip`.\n* `rcases_patt_parse_list` will parse an alternation list, `patt_med`, one or more `patt`\n  patterns separated by `|`. It does not parse a `:` at the end, so that `a | b : ty` parses as\n  `(a | b) : ty` where `a | b` is the `patt_med` part.\n* `rcases_patt_parse_list_rest a` parses an alternation list after the initial pattern, `| b | c`.\n\n```lean\npatt ::= patt_med (\":\" expr)?\npatt_med ::= (patt_hi \"|\")* patt_hi\npatt_hi ::= id | \"rfl\" | \"_\" | \"@\" patt_hi | \"⟨\" (patt \",\")* patt \"⟩\" | \"(\" patt \")\"\n```\n-/")]
        []
        []
        []
        [(Command.unsafe "unsafe")]
        [])
       (Command.def
        "def"
        (Command.declId `rcases_patt_parse_list_rest [])
        (Command.optDeclSig
         []
         [(Term.typeSpec
           ":"
           (Term.arrow
            `rcases_patt
            "→"
            (Term.app
             `parser
             [(Term.app (Tactic.Tactic.Rcases.«termlistΣ» "listΣ") [`rcases_patt])])))])
        (Command.declValEqns
         (Term.matchAltsWhereDecls
          (Term.matchAlts
           [(Term.matchAlt
             "|"
             [[`pat]]
             "=>"
             («term_<|>_»
              («term_*>_»
               (Term.app `tk [(str "\"|\"")])
               "*>"
               («term_<$>_» (Term.app `List.cons [`pat]) "<$>" `rcases_patt_parse_list'))
              "<|>"
              («term_<|>_»
               («term_*>_»
                (Term.app `tk [(str "\"|-\"")])
                "*>"
                («term_<$>_»
                 (Term.app `List.cons [`pat])
                 "<$>"
                 (Term.app `rcases_patt_parse_list_rest [`rcases_patt.clear])))
               "<|>"
               (Term.app `pure [(«term[_]» "[" [`pat] "]")]))))])
          []))
        []
        []
        []))]
     "end"
     []
     [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValEqns', expected 'Lean.Parser.Command.declValSimple'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|>_»
       («term_*>_»
        (Term.app `tk [(str "\"|\"")])
        "*>"
        («term_<$>_» (Term.app `List.cons [`pat]) "<$>" `rcases_patt_parse_list'))
       "<|>"
       («term_<|>_»
        («term_*>_»
         (Term.app `tk [(str "\"|-\"")])
         "*>"
         («term_<$>_»
          (Term.app `List.cons [`pat])
          "<$>"
          (Term.app `rcases_patt_parse_list_rest [`rcases_patt.clear])))
        "<|>"
        (Term.app `pure [(«term[_]» "[" [`pat] "]")])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|>_»
       («term_*>_»
        (Term.app `tk [(str "\"|-\"")])
        "*>"
        («term_<$>_»
         (Term.app `List.cons [`pat])
         "<$>"
         (Term.app `rcases_patt_parse_list_rest [`rcases_patt.clear])))
       "<|>"
       (Term.app `pure [(«term[_]» "[" [`pat] "]")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `pure [(«term[_]» "[" [`pat] "]")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term[_]»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term[_]»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term[_]» "[" [`pat] "]")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `pat
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `pure
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 20 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 20, term))
      («term_*>_»
       (Term.app `tk [(str "\"|-\"")])
       "*>"
       («term_<$>_»
        (Term.app `List.cons [`pat])
        "<$>"
        (Term.app `rcases_patt_parse_list_rest [`rcases_patt.clear])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<$>_»
       (Term.app `List.cons [`pat])
       "<$>"
       (Term.app `rcases_patt_parse_list_rest [`rcases_patt.clear]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `rcases_patt_parse_list_rest [`rcases_patt.clear])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rcases_patt.clear
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `rcases_patt_parse_list_rest
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 100 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 100, term))
      (Term.app `List.cons [`pat])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `pat
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `List.cons
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 101 >? 1022, (some 1023, term) <=? (some 100, term)
[PrettyPrinter.parenthesize] ...precedences are 61 >? 100, (some 100, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 60, term))
      (Term.app `tk [(str "\"|-\"")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'str', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'str', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (str "\"|-\"")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `tk
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 60 >? 1022, (some 1023, term) <=? (some 60, term)
[PrettyPrinter.parenthesize] ...precedences are 21 >? 60, (some 61, term) <=? (some 20, term)
[PrettyPrinter.parenthesize] ...precedences are 20 >? 20, (some 20, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 20, term))
      («term_*>_»
       (Term.app `tk [(str "\"|\"")])
       "*>"
       («term_<$>_» (Term.app `List.cons [`pat]) "<$>" `rcases_patt_parse_list'))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<$>_» (Term.app `List.cons [`pat]) "<$>" `rcases_patt_parse_list')
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rcases_patt_parse_list'
[PrettyPrinter.parenthesize] ...precedences are 100 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 100, term))
      (Term.app `List.cons [`pat])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `pat
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `List.cons
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 101 >? 1022, (some 1023, term) <=? (some 100, term)
[PrettyPrinter.parenthesize] ...precedences are 61 >? 100, (some 100, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 60, term))
      (Term.app `tk [(str "\"|\"")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'str', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'str', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (str "\"|\"")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `tk
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 60 >? 1022, (some 1023, term) <=? (some 60, term)
[PrettyPrinter.parenthesize] ...precedences are 21 >? 60, (some 61, term) <=? (some 20, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 20, (some 20, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `pat
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.arrow
       `rcases_patt
       "→"
       (Term.app `parser [(Term.app (Tactic.Tactic.Rcases.«termlistΣ» "listΣ") [`rcases_patt])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `parser [(Term.app (Tactic.Tactic.Rcases.«termlistΣ» "listΣ") [`rcases_patt])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Tactic.Tactic.Rcases.«termlistΣ» "listΣ") [`rcases_patt])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rcases_patt
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Tactic.Tactic.Rcases.«termlistΣ» "listΣ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Tactic.Tactic.Rcases.«termlistΣ»', expected 'Tactic.Tactic.Rcases.termlistΣ._@.Tactic.Rcases._hyg.7'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
mutual
  /--
          * `rcases_patt_parse_hi` will parse a high precedence `rcases` pattern, `patt_hi`.
            This means only tuples and identifiers are allowed; alternations and type ascriptions
            require `(...)` instead, which switches to `patt`.
          * `rcases_patt_parse` will parse a low precedence `rcases` pattern, `patt`. This consists of a
            `patt_med` (which deals with alternations), optionally followed by a `: ty` type ascription. The
            expression `ty` is at `texpr` precedence because it can appear at the end of a tactic, for
            example in `rcases e with x : ty <|> skip`.
          * `rcases_patt_parse_list` will parse an alternation list, `patt_med`, one or more `patt`
            patterns separated by `|`. It does not parse a `:` at the end, so that `a | b : ty` parses as
            `(a | b) : ty` where `a | b` is the `patt_med` part.
          * `rcases_patt_parse_list_rest a` parses an alternation list after the initial pattern, `| b | c`.
          
          ```lean
          patt ::= patt_med (":" expr)?
          patt_med ::= (patt_hi "|")* patt_hi
          patt_hi ::= id | "rfl" | "_" | "@" patt_hi | "⟨" (patt ",")* patt "⟩" | "(" patt ")"
          ```
          -/
        unsafe
      def
        rcases_patt_parse_hi'
        : parser rcases_patt
        |
          x
          =>
          brackets "(" ")" rcases_patt_parse'
              <|>
              rcases_patt.tuple <$> brackets "⟨" "⟩" sep_by tk "," rcases_patt_parse'
                <|>
                tk "-" $> rcases_patt.clear
                  <|>
                  tk "@" *> rcases_patt.explicit <$> rcases_patt_parse_hi'
                    <|>
                    rcases_patt.one <$> ident_
            x
    /--
          * `rcases_patt_parse_hi` will parse a high precedence `rcases` pattern, `patt_hi`.
            This means only tuples and identifiers are allowed; alternations and type ascriptions
            require `(...)` instead, which switches to `patt`.
          * `rcases_patt_parse` will parse a low precedence `rcases` pattern, `patt`. This consists of a
            `patt_med` (which deals with alternations), optionally followed by a `: ty` type ascription. The
            expression `ty` is at `texpr` precedence because it can appear at the end of a tactic, for
            example in `rcases e with x : ty <|> skip`.
          * `rcases_patt_parse_list` will parse an alternation list, `patt_med`, one or more `patt`
            patterns separated by `|`. It does not parse a `:` at the end, so that `a | b : ty` parses as
            `(a | b) : ty` where `a | b` is the `patt_med` part.
          * `rcases_patt_parse_list_rest a` parses an alternation list after the initial pattern, `| b | c`.
          
          ```lean
          patt ::= patt_med (":" expr)?
          patt_med ::= (patt_hi "|")* patt_hi
          patt_hi ::= id | "rfl" | "_" | "@" patt_hi | "⟨" (patt ",")* patt "⟩" | "(" patt ")"
          ```
          -/
        unsafe
      def
        rcases_patt_parse'
        : parser rcases_patt
        |
          x
          =>
          do
              let pat ← rcases_patt.alts' <$> rcases_patt_parse_list'
                tk ":" *> pat <$> texpr <|> pure pat
            x
    /--
          * `rcases_patt_parse_hi` will parse a high precedence `rcases` pattern, `patt_hi`.
            This means only tuples and identifiers are allowed; alternations and type ascriptions
            require `(...)` instead, which switches to `patt`.
          * `rcases_patt_parse` will parse a low precedence `rcases` pattern, `patt`. This consists of a
            `patt_med` (which deals with alternations), optionally followed by a `: ty` type ascription. The
            expression `ty` is at `texpr` precedence because it can appear at the end of a tactic, for
            example in `rcases e with x : ty <|> skip`.
          * `rcases_patt_parse_list` will parse an alternation list, `patt_med`, one or more `patt`
            patterns separated by `|`. It does not parse a `:` at the end, so that `a | b : ty` parses as
            `(a | b) : ty` where `a | b` is the `patt_med` part.
          * `rcases_patt_parse_list_rest a` parses an alternation list after the initial pattern, `| b | c`.
          
          ```lean
          patt ::= patt_med (":" expr)?
          patt_med ::= (patt_hi "|")* patt_hi
          patt_hi ::= id | "rfl" | "_" | "@" patt_hi | "⟨" (patt ",")* patt "⟩" | "(" patt ")"
          ```
          -/
        unsafe
      def
        rcases_patt_parse_list'
        : parser listΣ rcases_patt
        | x => rcases_patt_parse_hi' >>= rcases_patt_parse_list_rest x
    /--
          * `rcases_patt_parse_hi` will parse a high precedence `rcases` pattern, `patt_hi`.
            This means only tuples and identifiers are allowed; alternations and type ascriptions
            require `(...)` instead, which switches to `patt`.
          * `rcases_patt_parse` will parse a low precedence `rcases` pattern, `patt`. This consists of a
            `patt_med` (which deals with alternations), optionally followed by a `: ty` type ascription. The
            expression `ty` is at `texpr` precedence because it can appear at the end of a tactic, for
            example in `rcases e with x : ty <|> skip`.
          * `rcases_patt_parse_list` will parse an alternation list, `patt_med`, one or more `patt`
            patterns separated by `|`. It does not parse a `:` at the end, so that `a | b : ty` parses as
            `(a | b) : ty` where `a | b` is the `patt_med` part.
          * `rcases_patt_parse_list_rest a` parses an alternation list after the initial pattern, `| b | c`.
          
          ```lean
          patt ::= patt_med (":" expr)?
          patt_med ::= (patt_hi "|")* patt_hi
          patt_hi ::= id | "rfl" | "_" | "@" patt_hi | "⟨" (patt ",")* patt "⟩" | "(" patt ")"
          ```
          -/
        unsafe
      def
        rcases_patt_parse_list_rest
        : rcases_patt → parser listΣ rcases_patt
        |
          pat
          =>
          tk "|" *> List.cons pat <$> rcases_patt_parse_list'
            <|>
            tk "|-" *> List.cons pat <$> rcases_patt_parse_list_rest rcases_patt.clear
              <|>
              pure [ pat ]
  end
#align tactic.rcases_patt_parse_hi' tactic.rcases_patt_parse_hi'
#align tactic.rcases_patt_parse' tactic.rcases_patt_parse'
#align tactic.rcases_patt_parse_list' tactic.rcases_patt_parse_list'
#align tactic.rcases_patt_parse_list_rest tactic.rcases_patt_parse_list_rest

/-- `rcases_patt_parse_hi` will parse a high precedence `rcases` pattern, `patt_hi`.
This means only tuples and identifiers are allowed; alternations and type ascriptions
require `(...)` instead, which switches to `patt`.
```lean
patt_hi ::= id | "rfl" | "_" | "@" patt_hi | "⟨" (patt ",")* patt "⟩" | "(" patt ")"
```
-/
unsafe def rcases_patt_parse_hi :=
  with_desc "patt_hi" rcases_patt_parse_hi'
#align tactic.rcases_patt_parse_hi tactic.rcases_patt_parse_hi

/-- `rcases_patt_parse` will parse a low precedence `rcases` pattern, `patt`. This consists of a
`patt_med` (which deals with alternations), optionally followed by a `: ty` type ascription. The
expression `ty` is at `texpr` precedence because it can appear at the end of a tactic, for
example in `rcases e with x : ty <|> skip`.
```lean
patt ::= patt_med (":" expr)?
```
-/
unsafe def rcases_patt_parse :=
  with_desc "patt" rcases_patt_parse'
#align tactic.rcases_patt_parse tactic.rcases_patt_parse

/-- `rcases_patt_parse_list` will parse an alternation list, `patt_med`, one or more `patt`
patterns separated by `|`. It does not parse a `:` at the end, so that `a | b : ty` parses as
`(a | b) : ty` where `a | b` is the `patt_med` part.
```lean
patt_med ::= (patt_hi "|")* patt_hi
```
-/
unsafe def rcases_patt_parse_list :=
  with_desc "patt_med" rcases_patt_parse_list'
#align tactic.rcases_patt_parse_list tactic.rcases_patt_parse_list

/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `parser.optional -/
/-- Parse the optional depth argument `(: n)?` of `rcases?` and `rintro?`, with default depth 5. -/
unsafe def rcases_parse_depth : parser Nat := do
  let o ← parser.optional (tk ":" *> small_nat)
  pure <| o 5
#align tactic.rcases_parse_depth tactic.rcases_parse_depth

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "The arguments to `rcases`, which in fact dispatch to several other tactics.\n* `rcases? expr (: n)?` or `rcases? ⟨expr, ...⟩ (: n)?` calls `rcases_hint`\n* `rcases? ⟨expr, ...⟩ (: n)?` calls `rcases_hint_many`\n* `rcases (h :)? expr (with patt)?` calls `rcases`\n* `rcases ⟨expr, ...⟩ (with patt)?` calls `rcases_many`\n-/")]
      []
      []
      []
      [(Command.unsafe "unsafe")]
      [])
     (Command.inductive
      "inductive"
      (Command.declId `rcases_args [])
      (Command.optDeclSig [] [])
      []
      [(Command.ctor
        []
        "|"
        (Command.declModifiers [] [] [] [] [] [])
        `hint
        (Command.optDeclSig
         [(Term.explicitBinder
           "("
           [`tgt]
           [":" (Term.app `Sum [`pexpr (Term.app `List [`pexpr])])]
           []
           ")")
          (Term.explicitBinder "(" [`depth] [":" `Nat] [] ")")]
         []))
       (Command.ctor
        []
        "|"
        (Command.declModifiers [] [] [] [] [] [])
        `rcases
        (Command.optDeclSig
         [(Term.explicitBinder "(" [`name] [":" (Term.app `Option [`Name])] [] ")")
          (Term.explicitBinder "(" [`tgt] [":" `pexpr] [] ")")
          (Term.explicitBinder "(" [`pat] [":" `rcases_patt] [] ")")]
         []))
       (Command.ctor
        []
        "|"
        (Command.declModifiers [] [] [] [] [] [])
        `rcases_many
        (Command.optDeclSig
         [(Term.explicitBinder
           "("
           [`tgt]
           [":" (Term.app (Tactic.Tactic.Rcases.«termlistΠ» "listΠ") [`pexpr])]
           []
           ")")
          (Term.explicitBinder "(" [`pat] [":" `rcases_patt] [] ")")]
         []))]
      []
      (Command.optDeriving ["deriving" [(group `has_reflect [])]])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.inductive', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.inductive', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.inductive', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.inductive', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.inductive', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.inductive', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.inductive', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rcases_patt
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Tactic.Tactic.Rcases.«termlistΠ» "listΠ") [`pexpr])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `pexpr
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Tactic.Tactic.Rcases.«termlistΠ» "listΠ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Tactic.Tactic.Rcases.«termlistΠ»', expected 'Tactic.Tactic.Rcases.termlistΠ._@.Tactic.Rcases._hyg.324'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.inductive', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.inductive', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
      The arguments to `rcases`, which in fact dispatch to several other tactics.
      * `rcases? expr (: n)?` or `rcases? ⟨expr, ...⟩ (: n)?` calls `rcases_hint`
      * `rcases? ⟨expr, ...⟩ (: n)?` calls `rcases_hint_many`
      * `rcases (h :)? expr (with patt)?` calls `rcases`
      * `rcases ⟨expr, ...⟩ (with patt)?` calls `rcases_many`
      -/
    unsafe
  inductive
    rcases_args
    | hint ( tgt : Sum pexpr List pexpr ) ( depth : Nat )
      | rcases ( name : Option Name ) ( tgt : pexpr ) ( pat : rcases_patt )
      | rcases_many ( tgt : listΠ pexpr ) ( pat : rcases_patt )
    deriving has_reflect
#align tactic.rcases_args tactic.rcases_args

/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `parser.optional -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `parser.optional -/
/-- Syntax for a `rcases` pattern:
* `rcases? expr (: n)?`
* `rcases (h :)? expr (with patt_list (: expr)?)?`. -/
unsafe def rcases_parse : parser rcases_args :=
  (with_desc "('?' expr (: n)?) | ((h :)? expr (with patt)?)") do
    let hint ← parser.optional (tk "?")
    let p ← Sum.inr <$> brackets "⟨" "⟩" (sep_by (tk ",") (parser.pexpr 0)) <|> Sum.inl <$> texpr
    match hint with
      | none => do
        let p ←
          (do
                let Sum.inl (expr.local_const h _ _ _) ← pure p
                tk ":" *> (@Sum.inl _ (Sum pexpr (List pexpr)) ∘ Prod.mk h) <$> texpr) <|>
              pure (Sum.inr p)
        let ids ← parser.optional (tk "with" *> rcases_patt_parse)
        let ids := ids (rcases_patt.tuple [])
        pure <|
            match p with
            | Sum.inl (Name, tgt) => rcases_args.rcases (some Name) tgt ids
            | Sum.inr (Sum.inl tgt) => rcases_args.rcases none tgt ids
            | Sum.inr (Sum.inr tgts) => rcases_args.rcases_many tgts ids
      | some _ => do
        let depth ← rcases_parse_depth
        pure <| rcases_args.hint p depth
#align tactic.rcases_parse tactic.rcases_parse

/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `parser.many -/
/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.mutual
     "mutual"
     [(Command.declaration
       (Command.declModifiers
        [(Command.docComment
          "/--"
          "`rintro_patt_parse_hi` and `rintro_patt_parse` are like `rcases_patt_parse`, but is used for\nparsing top level `rintro` patterns, which allow sequences like `(x y : t)` in addition to simple\n`rcases` patterns.\n\n* `rintro_patt_parse_hi` will parse a high precedence `rcases` pattern, `rintro_patt_hi` below.\n  This means only tuples and identifiers are allowed; alternations and type ascriptions\n  require `(...)` instead, which switches to `patt`.\n* `rintro_patt_parse` will parse a low precedence `rcases` pattern, `rintro_patt` below.\n  This consists of either a sequence of patterns `p1 p2 p3` or an alternation list `p1 | p2 | p3`\n  treated as a single pattern, optionally followed by a `: ty` type ascription, which applies to\n  every pattern in the list.\n* `rintro_patt_parse_low` parses `rintro_patt_low`, which is the same as `rintro_patt_parse tt` but\n  it does not permit an unparenthesized alternation list, it must have the form `p1 p2 p3 (: ty)?`.\n\n```lean\nrintro_patt ::= (rintro_patt_hi+ | patt_med) (\":\" expr)?\nrintro_patt_low ::= rintro_patt_hi* (\":\" expr)?\nrintro_patt_hi ::= patt_hi | \"(\" rintro_patt \")\"\n```\n-/")]
        []
        []
        []
        [(Command.unsafe "unsafe")]
        [])
       (Command.def
        "def"
        (Command.declId `rintro_patt_parse_hi' [])
        (Command.optDeclSig
         []
         [(Term.typeSpec
           ":"
           (Term.app
            `parser
            [(Term.app (Tactic.Tactic.Rcases.«termlistΠ» "listΠ") [`rcases_patt])]))])
        (Command.declValEqns
         (Term.matchAltsWhereDecls
          (Term.matchAlts
           [(Term.matchAlt
             "|"
             [[`x]]
             "=>"
             (Term.app
              («term_<|>_»
               (Term.app
                `brackets
                [(str "\"(\"") (str "\")\"") (Term.app `rintro_patt_parse' [`true])])
               "<|>"
               (Term.do
                "do"
                (Term.doSeqIndent
                 [(Term.doSeqItem
                   (Term.doLetArrow
                    "let"
                    []
                    (Term.doIdDecl `p [] "←" (Term.doExpr `rcases_patt_parse_hi)))
                   [])
                  (Term.doSeqItem (Term.doExpr (Term.app `pure [(«term[_]» "[" [`p] "]")])) [])])))
              [`x]))])
          []))
        []
        []
        []))
      (Command.declaration
       (Command.declModifiers
        [(Command.docComment
          "/--"
          "`rintro_patt_parse_hi` and `rintro_patt_parse` are like `rcases_patt_parse`, but is used for\nparsing top level `rintro` patterns, which allow sequences like `(x y : t)` in addition to simple\n`rcases` patterns.\n\n* `rintro_patt_parse_hi` will parse a high precedence `rcases` pattern, `rintro_patt_hi` below.\n  This means only tuples and identifiers are allowed; alternations and type ascriptions\n  require `(...)` instead, which switches to `patt`.\n* `rintro_patt_parse` will parse a low precedence `rcases` pattern, `rintro_patt` below.\n  This consists of either a sequence of patterns `p1 p2 p3` or an alternation list `p1 | p2 | p3`\n  treated as a single pattern, optionally followed by a `: ty` type ascription, which applies to\n  every pattern in the list.\n* `rintro_patt_parse_low` parses `rintro_patt_low`, which is the same as `rintro_patt_parse tt` but\n  it does not permit an unparenthesized alternation list, it must have the form `p1 p2 p3 (: ty)?`.\n\n```lean\nrintro_patt ::= (rintro_patt_hi+ | patt_med) (\":\" expr)?\nrintro_patt_low ::= rintro_patt_hi* (\":\" expr)?\nrintro_patt_hi ::= patt_hi | \"(\" rintro_patt \")\"\n```\n-/")]
        []
        []
        []
        [(Command.unsafe "unsafe")]
        [])
       (Command.def
        "def"
        (Command.declId `rintro_patt_parse' [])
        (Command.optDeclSig
         []
         [(Term.typeSpec
           ":"
           (Term.arrow
            `Bool
            "→"
            (Term.app
             `parser
             [(Term.app (Tactic.Tactic.Rcases.«termlistΠ» "listΠ") [`rcases_patt])])))])
        (Command.declValEqns
         (Term.matchAltsWhereDecls
          (Term.matchAlts
           [(Term.matchAlt
             "|"
             [[`med]]
             "=>"
             (Term.do
              "do"
              (Term.doSeqIndent
               [(Term.doSeqItem
                 (Term.doLetArrow
                  "let"
                  []
                  (Term.doIdDecl
                   `ll
                   []
                   "←"
                   (Term.doExpr (Term.app `parser.many [`rintro_patt_parse_hi']))))
                 [])
                (Term.doSeqItem
                 (Term.doLetArrow
                  "let"
                  []
                  (Term.doIdDecl
                   `pats
                   []
                   "←"
                   (Term.doExpr
                    (Term.match
                     "match"
                     []
                     []
                     [(Term.matchDiscr [] `med) "," (Term.matchDiscr [] (Term.proj `ll "." `join))]
                     "with"
                     (Term.matchAlts
                      [(Term.matchAlt "|" [[`tt "," («term[_]» "[" [] "]")]] "=>" `failure)
                       (Term.matchAlt
                        "|"
                        [[`tt "," («term[_]» "[" [`pat] "]")]]
                        "=>"
                        (Term.do
                         "do"
                         (Term.doSeqIndent
                          [(Term.doSeqItem
                            (Term.doLetArrow
                             "let"
                             []
                             (Term.doIdDecl
                              `l
                              []
                              "←"
                              (Term.doExpr (Term.app `rcases_patt_parse_list_rest [`pat]))))
                            [])
                           (Term.doSeqItem
                            (Term.doExpr
                             (Term.app
                              `pure
                              [(«term[_]» "[" [(Term.app `rcases_patt.alts' [`l])] "]")]))
                            [])])))
                       (Term.matchAlt
                        "|"
                        [[(Term.hole "_") "," `pats]]
                        "=>"
                        (Term.app `pure [`pats]))])))))
                 [])
                (Term.doSeqItem
                 (Term.doExpr
                  («term_<|>_»
                   (Term.do
                    "do"
                    (Term.doSeqIndent
                     [(Term.doSeqItem (Term.doExpr (Term.app `tk [(str "\":\"")])) [])
                      (Term.doSeqItem
                       (Term.doLetArrow "let" [] (Term.doIdDecl `e [] "←" (Term.doExpr `texpr)))
                       [])
                      (Term.doSeqItem
                       (Term.doExpr
                        (Term.app
                         `pure
                         [(Term.app
                           `pats
                           [(Term.fun
                             "fun"
                             (Term.basicFun
                              [`p]
                              []
                              "=>"
                              (Term.app `rcases_patt.typed [`p `e])))])]))
                       [])]))
                   "<|>"
                   (Term.app `pure [`pats])))
                 [])])))])
          []))
        []
        []
        []))]
     "end"
     []
     [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValEqns', expected 'Lean.Parser.Command.declValSimple'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.do
       "do"
       (Term.doSeqIndent
        [(Term.doSeqItem
          (Term.doLetArrow
           "let"
           []
           (Term.doIdDecl
            `ll
            []
            "←"
            (Term.doExpr (Term.app `parser.many [`rintro_patt_parse_hi']))))
          [])
         (Term.doSeqItem
          (Term.doLetArrow
           "let"
           []
           (Term.doIdDecl
            `pats
            []
            "←"
            (Term.doExpr
             (Term.match
              "match"
              []
              []
              [(Term.matchDiscr [] `med) "," (Term.matchDiscr [] (Term.proj `ll "." `join))]
              "with"
              (Term.matchAlts
               [(Term.matchAlt "|" [[`tt "," («term[_]» "[" [] "]")]] "=>" `failure)
                (Term.matchAlt
                 "|"
                 [[`tt "," («term[_]» "[" [`pat] "]")]]
                 "=>"
                 (Term.do
                  "do"
                  (Term.doSeqIndent
                   [(Term.doSeqItem
                     (Term.doLetArrow
                      "let"
                      []
                      (Term.doIdDecl
                       `l
                       []
                       "←"
                       (Term.doExpr (Term.app `rcases_patt_parse_list_rest [`pat]))))
                     [])
                    (Term.doSeqItem
                     (Term.doExpr
                      (Term.app `pure [(«term[_]» "[" [(Term.app `rcases_patt.alts' [`l])] "]")]))
                     [])])))
                (Term.matchAlt
                 "|"
                 [[(Term.hole "_") "," `pats]]
                 "=>"
                 (Term.app `pure [`pats]))])))))
          [])
         (Term.doSeqItem
          (Term.doExpr
           («term_<|>_»
            (Term.do
             "do"
             (Term.doSeqIndent
              [(Term.doSeqItem (Term.doExpr (Term.app `tk [(str "\":\"")])) [])
               (Term.doSeqItem
                (Term.doLetArrow "let" [] (Term.doIdDecl `e [] "←" (Term.doExpr `texpr)))
                [])
               (Term.doSeqItem
                (Term.doExpr
                 (Term.app
                  `pure
                  [(Term.app
                    `pats
                    [(Term.fun
                      "fun"
                      (Term.basicFun [`p] [] "=>" (Term.app `rcases_patt.typed [`p `e])))])]))
                [])]))
            "<|>"
            (Term.app `pure [`pats])))
          [])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doSeqIndent', expected 'Lean.Parser.Term.doSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|>_»
       (Term.do
        "do"
        (Term.doSeqIndent
         [(Term.doSeqItem (Term.doExpr (Term.app `tk [(str "\":\"")])) [])
          (Term.doSeqItem
           (Term.doLetArrow "let" [] (Term.doIdDecl `e [] "←" (Term.doExpr `texpr)))
           [])
          (Term.doSeqItem
           (Term.doExpr
            (Term.app
             `pure
             [(Term.app
               `pats
               [(Term.fun
                 "fun"
                 (Term.basicFun [`p] [] "=>" (Term.app `rcases_patt.typed [`p `e])))])]))
           [])]))
       "<|>"
       (Term.app `pure [`pats]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `pure [`pats])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `pats
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `pure
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 20 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 20, term))
      (Term.do
       "do"
       (Term.doSeqIndent
        [(Term.doSeqItem (Term.doExpr (Term.app `tk [(str "\":\"")])) [])
         (Term.doSeqItem
          (Term.doLetArrow "let" [] (Term.doIdDecl `e [] "←" (Term.doExpr `texpr)))
          [])
         (Term.doSeqItem
          (Term.doExpr
           (Term.app
            `pure
            [(Term.app
              `pats
              [(Term.fun
                "fun"
                (Term.basicFun [`p] [] "=>" (Term.app `rcases_patt.typed [`p `e])))])]))
          [])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doSeqIndent', expected 'Lean.Parser.Term.doSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `pure
       [(Term.app
         `pats
         [(Term.fun "fun" (Term.basicFun [`p] [] "=>" (Term.app `rcases_patt.typed [`p `e])))])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `pats
       [(Term.fun "fun" (Term.basicFun [`p] [] "=>" (Term.app `rcases_patt.typed [`p `e])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun "fun" (Term.basicFun [`p] [] "=>" (Term.app `rcases_patt.typed [`p `e])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `rcases_patt.typed [`p `e])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `e
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `rcases_patt.typed
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `pats
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `pats
      [(Term.fun "fun" (Term.basicFun [`p] [] "=>" (Term.app `rcases_patt.typed [`p `e])))])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `pure
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, doElem))
      `texpr
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, doElem)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, doElem))
      (Term.app `tk [(str "\":\"")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'str', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'str', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (str "\":\"")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `tk
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1023, doElem)
[PrettyPrinter.parenthesize] ...precedences are 21 >? 1023, (some 0, term) <=? (some 20, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.do
      "do"
      (Term.doSeqIndent
       [(Term.doSeqItem (Term.doExpr (Term.app `tk [(str "\":\"")])) [])
        (Term.doSeqItem
         (Term.doLetArrow "let" [] (Term.doIdDecl `e [] "←" (Term.doExpr `texpr)))
         [])
        (Term.doSeqItem
         (Term.doExpr
          (Term.app
           `pure
           [(Term.paren
             "("
             (Term.app
              `pats
              [(Term.fun "fun" (Term.basicFun [`p] [] "=>" (Term.app `rcases_patt.typed [`p `e])))])
             ")")]))
         [])]))
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 20, (some 20, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, doElem))
      (Term.match
       "match"
       []
       []
       [(Term.matchDiscr [] `med) "," (Term.matchDiscr [] (Term.proj `ll "." `join))]
       "with"
       (Term.matchAlts
        [(Term.matchAlt "|" [[`tt "," («term[_]» "[" [] "]")]] "=>" `failure)
         (Term.matchAlt
          "|"
          [[`tt "," («term[_]» "[" [`pat] "]")]]
          "=>"
          (Term.do
           "do"
           (Term.doSeqIndent
            [(Term.doSeqItem
              (Term.doLetArrow
               "let"
               []
               (Term.doIdDecl
                `l
                []
                "←"
                (Term.doExpr (Term.app `rcases_patt_parse_list_rest [`pat]))))
              [])
             (Term.doSeqItem
              (Term.doExpr
               (Term.app `pure [(«term[_]» "[" [(Term.app `rcases_patt.alts' [`l])] "]")]))
              [])])))
         (Term.matchAlt "|" [[(Term.hole "_") "," `pats]] "=>" (Term.app `pure [`pats]))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `pure [`pats])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `pats
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `pure
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `pats
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.do
       "do"
       (Term.doSeqIndent
        [(Term.doSeqItem
          (Term.doLetArrow
           "let"
           []
           (Term.doIdDecl `l [] "←" (Term.doExpr (Term.app `rcases_patt_parse_list_rest [`pat]))))
          [])
         (Term.doSeqItem
          (Term.doExpr (Term.app `pure [(«term[_]» "[" [(Term.app `rcases_patt.alts' [`l])] "]")]))
          [])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doSeqIndent', expected 'Lean.Parser.Term.doSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `pure [(«term[_]» "[" [(Term.app `rcases_patt.alts' [`l])] "]")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term[_]»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term[_]»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term[_]» "[" [(Term.app `rcases_patt.alts' [`l])] "]")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `rcases_patt.alts' [`l])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `l
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `rcases_patt.alts'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `pure
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, doElem))
      (Term.app `rcases_patt_parse_list_rest [`pat])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `pat
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `rcases_patt_parse_list_rest
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, doElem)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1023, (some 0,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term[_]» "[" [`pat] "]")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `pat
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `tt
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      `failure
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term[_]» "[" [] "]")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `tt
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `ll "." `join)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `ll
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `med
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, doElem)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, doElem))
      (Term.app `parser.many [`rintro_patt_parse_hi'])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rintro_patt_parse_hi'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `parser.many
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, doElem)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1023, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `med
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.arrow
       `Bool
       "→"
       (Term.app `parser [(Term.app (Tactic.Tactic.Rcases.«termlistΠ» "listΠ") [`rcases_patt])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `parser [(Term.app (Tactic.Tactic.Rcases.«termlistΠ» "listΠ") [`rcases_patt])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Tactic.Tactic.Rcases.«termlistΠ» "listΠ") [`rcases_patt])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rcases_patt
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Tactic.Tactic.Rcases.«termlistΠ» "listΠ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Tactic.Tactic.Rcases.«termlistΠ»', expected 'Tactic.Tactic.Rcases.termlistΠ._@.Tactic.Rcases._hyg.324'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
mutual
  /--
          `rintro_patt_parse_hi` and `rintro_patt_parse` are like `rcases_patt_parse`, but is used for
          parsing top level `rintro` patterns, which allow sequences like `(x y : t)` in addition to simple
          `rcases` patterns.
          
          * `rintro_patt_parse_hi` will parse a high precedence `rcases` pattern, `rintro_patt_hi` below.
            This means only tuples and identifiers are allowed; alternations and type ascriptions
            require `(...)` instead, which switches to `patt`.
          * `rintro_patt_parse` will parse a low precedence `rcases` pattern, `rintro_patt` below.
            This consists of either a sequence of patterns `p1 p2 p3` or an alternation list `p1 | p2 | p3`
            treated as a single pattern, optionally followed by a `: ty` type ascription, which applies to
            every pattern in the list.
          * `rintro_patt_parse_low` parses `rintro_patt_low`, which is the same as `rintro_patt_parse tt` but
            it does not permit an unparenthesized alternation list, it must have the form `p1 p2 p3 (: ty)?`.
          
          ```lean
          rintro_patt ::= (rintro_patt_hi+ | patt_med) (":" expr)?
          rintro_patt_low ::= rintro_patt_hi* (":" expr)?
          rintro_patt_hi ::= patt_hi | "(" rintro_patt ")"
          ```
          -/
        unsafe
      def
        rintro_patt_parse_hi'
        : parser listΠ rcases_patt
        |
          x
          =>
          brackets "(" ")" rintro_patt_parse' true <|> do let p ← rcases_patt_parse_hi pure [ p ] x
    /--
          `rintro_patt_parse_hi` and `rintro_patt_parse` are like `rcases_patt_parse`, but is used for
          parsing top level `rintro` patterns, which allow sequences like `(x y : t)` in addition to simple
          `rcases` patterns.
          
          * `rintro_patt_parse_hi` will parse a high precedence `rcases` pattern, `rintro_patt_hi` below.
            This means only tuples and identifiers are allowed; alternations and type ascriptions
            require `(...)` instead, which switches to `patt`.
          * `rintro_patt_parse` will parse a low precedence `rcases` pattern, `rintro_patt` below.
            This consists of either a sequence of patterns `p1 p2 p3` or an alternation list `p1 | p2 | p3`
            treated as a single pattern, optionally followed by a `: ty` type ascription, which applies to
            every pattern in the list.
          * `rintro_patt_parse_low` parses `rintro_patt_low`, which is the same as `rintro_patt_parse tt` but
            it does not permit an unparenthesized alternation list, it must have the form `p1 p2 p3 (: ty)?`.
          
          ```lean
          rintro_patt ::= (rintro_patt_hi+ | patt_med) (":" expr)?
          rintro_patt_low ::= rintro_patt_hi* (":" expr)?
          rintro_patt_hi ::= patt_hi | "(" rintro_patt ")"
          ```
          -/
        unsafe
      def
        rintro_patt_parse'
        : Bool → parser listΠ rcases_patt
        |
          med
          =>
          do
            let ll ← parser.many rintro_patt_parse_hi'
              let
                pats
                  ←
                  match
                    med , ll . join
                    with
                    | tt , [ ] => failure
                      |
                        tt , [ pat ]
                        =>
                        do let l ← rcases_patt_parse_list_rest pat pure [ rcases_patt.alts' l ]
                      | _ , pats => pure pats
              do tk ":" let e ← texpr pure pats fun p => rcases_patt.typed p e <|> pure pats
  end
#align tactic.rintro_patt_parse_hi' tactic.rintro_patt_parse_hi'
#align tactic.rintro_patt_parse' tactic.rintro_patt_parse'

/-- `rintro_patt_parse_hi` will parse a high precedence `rcases` pattern, `rintro_patt_hi` below.
This means only tuples and identifiers are allowed; alternations and type ascriptions
require `(...)` instead, which switches to `patt`.
```lean
rintro_patt_hi ::= patt_hi | "(" rintro_patt ")"
```
-/
unsafe def rintro_patt_parse_hi :=
  with_desc "rintro_patt_hi" rintro_patt_parse_hi'
#align tactic.rintro_patt_parse_hi tactic.rintro_patt_parse_hi

/-- `rintro_patt_parse` will parse a low precedence `rcases` pattern, `rintro_patt` below.
This consists of either a sequence of patterns `p1 p2 p3` or an alternation list `p1 | p2 | p3`
treated as a single pattern, optionally followed by a `: ty` type ascription, which applies to
every pattern in the list.
```lean
rintro_patt ::= (rintro_patt_hi+ | patt_med) (":" expr)?
```
-/
unsafe def rintro_patt_parse :=
  with_desc "rintro_patt" <| rintro_patt_parse' true
#align tactic.rintro_patt_parse tactic.rintro_patt_parse

/--
`rintro_patt_parse_low` parses `rintro_patt_low`, which is the same as `rintro_patt_parse tt` but
it does not permit an unparenthesized alternation list, it must have the form `p1 p2 p3 (: ty)?`.
```lean
rintro_patt_low ::= rintro_patt_hi* (":" expr)?
```
-/
unsafe def rintro_patt_parse_low :=
  with_desc "rintro_patt_low" <| rintro_patt_parse' false
#align tactic.rintro_patt_parse_low tactic.rintro_patt_parse_low

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment "/--" "Syntax for a `rintro` pattern: `('?' (: n)?) | rintro_patt`. -/")]
      []
      []
      []
      [(Command.unsafe "unsafe")]
      [])
     (Command.def
      "def"
      (Command.declId `rintro_parse [])
      (Command.optDeclSig
       []
       [(Term.typeSpec
         ":"
         (Term.app
          `parser
          [(Term.app
            `Sum
            [(Term.app (Tactic.Tactic.Rcases.«termlistΠ» "listΠ") [`rcases_patt]) `Nat])]))])
      (Command.declValSimple
       ":="
       («term_<|_»
        (Term.app `with_desc [(str "\"('?' (: n)?) | patt*\"")])
        "<|"
        («term_<|>_»
         («term_>>_»
          (Term.app `tk [(str "\"?\"")])
          ">>"
          («term_<$>_» `Sum.inr "<$>" `rcases_parse_depth))
         "<|>"
         («term_<$>_» `Sum.inl "<$>" `rintro_patt_parse_low)))
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_»
       (Term.app `with_desc [(str "\"('?' (: n)?) | patt*\"")])
       "<|"
       («term_<|>_»
        («term_>>_»
         (Term.app `tk [(str "\"?\"")])
         ">>"
         («term_<$>_» `Sum.inr "<$>" `rcases_parse_depth))
        "<|>"
        («term_<$>_» `Sum.inl "<$>" `rintro_patt_parse_low)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|>_»
       («term_>>_»
        (Term.app `tk [(str "\"?\"")])
        ">>"
        («term_<$>_» `Sum.inr "<$>" `rcases_parse_depth))
       "<|>"
       («term_<$>_» `Sum.inl "<$>" `rintro_patt_parse_low))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<$>_» `Sum.inl "<$>" `rintro_patt_parse_low)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rintro_patt_parse_low
[PrettyPrinter.parenthesize] ...precedences are 100 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 100, term))
      `Sum.inl
[PrettyPrinter.parenthesize] ...precedences are 101 >? 1024, (none,
     [anonymous]) <=? (some 100, term)
[PrettyPrinter.parenthesize] ...precedences are 20 >? 100, (some 100, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 20, term))
      («term_>>_»
       (Term.app `tk [(str "\"?\"")])
       ">>"
       («term_<$>_» `Sum.inr "<$>" `rcases_parse_depth))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<$>_» `Sum.inr "<$>" `rcases_parse_depth)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rcases_parse_depth
[PrettyPrinter.parenthesize] ...precedences are 100 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 100, term))
      `Sum.inr
[PrettyPrinter.parenthesize] ...precedences are 101 >? 1024, (none,
     [anonymous]) <=? (some 100, term)
[PrettyPrinter.parenthesize] ...precedences are 60 >? 100, (some 100, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 60, term))
      (Term.app `tk [(str "\"?\"")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'str', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'str', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (str "\"?\"")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `tk
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 61 >? 1022, (some 1023, term) <=? (some 60, term)
[PrettyPrinter.parenthesize] ...precedences are 21 >? 60, (some 60, term) <=? (some 20, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 20, (some 20, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      (Term.app `with_desc [(str "\"('?' (: n)?) | patt*\"")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'str', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'str', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (str "\"('?' (: n)?) | patt*\"")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `with_desc
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 10, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app
       `parser
       [(Term.app
         `Sum
         [(Term.app (Tactic.Tactic.Rcases.«termlistΠ» "listΠ") [`rcases_patt]) `Nat])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Sum [(Term.app (Tactic.Tactic.Rcases.«termlistΠ» "listΠ") [`rcases_patt]) `Nat])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Nat
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app (Tactic.Tactic.Rcases.«termlistΠ» "listΠ") [`rcases_patt])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rcases_patt
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Tactic.Tactic.Rcases.«termlistΠ» "listΠ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Tactic.Tactic.Rcases.«termlistΠ»', expected 'Tactic.Tactic.Rcases.termlistΠ._@.Tactic.Rcases._hyg.324'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/-- Syntax for a `rintro` pattern: `('?' (: n)?) | rintro_patt`. -/ unsafe
  def
    rintro_parse
    : parser Sum listΠ rcases_patt Nat
    :=
      with_desc "('?' (: n)?) | patt*"
        <|
        tk "?" >> Sum.inr <$> rcases_parse_depth <|> Sum.inl <$> rintro_patt_parse_low
#align tactic.rintro_parse tactic.rintro_parse

namespace Interactive

open Interactive Interactive.Types Expr

/--
`rcases` is a tactic that will perform `cases` recursively, according to a pattern. It is used to
destructure hypotheses or expressions composed of inductive types like `h1 : a ∧ b ∧ c ∨ d` or
`h2 : ∃ x y, trans_rel R x y`. Usual usage might be `rcases h1 with ⟨ha, hb, hc⟩ | hd` or
`rcases h2 with ⟨x, y, _ | ⟨z, hxz, hzy⟩⟩` for these examples.

Each element of an `rcases` pattern is matched against a particular local hypothesis (most of which
are generated during the execution of `rcases` and represent individual elements destructured from
the input expression). An `rcases` pattern has the following grammar:

* A name like `x`, which names the active hypothesis as `x`.
* A blank `_`, which does nothing (letting the automatic naming system used by `cases` name the
  hypothesis).
* A hyphen `-`, which clears the active hypothesis and any dependents.
* The keyword `rfl`, which expects the hypothesis to be `h : a = b`, and calls `subst` on the
  hypothesis (which has the effect of replacing `b` with `a` everywhere or vice versa).
* A type ascription `p : ty`, which sets the type of the hypothesis to `ty` and then matches it
  against `p`. (Of course, `ty` must unify with the actual type of `h` for this to work.)
* A tuple pattern `⟨p1, p2, p3⟩`, which matches a constructor with many arguments, or a series
  of nested conjunctions or existentials. For example if the active hypothesis is `a ∧ b ∧ c`,
  then the conjunction will be destructured, and `p1` will be matched against `a`, `p2` against `b`
  and so on.
* A `@` before a tuple pattern as in `@⟨p1, p2, p3⟩` will bind all arguments in the constructor,
  while leaving the `@` off will only use the patterns on the explicit arguments.
* An alteration pattern `p1 | p2 | p3`, which matches an inductive type with multiple constructors,
  or a nested disjunction like `a ∨ b ∨ c`.

A pattern like `⟨a, b, c⟩ | ⟨d, e⟩` will do a split over the inductive datatype,
naming the first three parameters of the first constructor as `a,b,c` and the
first two of the second constructor `d,e`. If the list is not as long as the
number of arguments to the constructor or the number of constructors, the
remaining variables will be automatically named. If there are nested brackets
such as `⟨⟨a⟩, b | c⟩ | d` then these will cause more case splits as necessary.
If there are too many arguments, such as `⟨a, b, c⟩` for splitting on
`∃ x, ∃ y, p x`, then it will be treated as `⟨a, ⟨b, c⟩⟩`, splitting the last
parameter as necessary.

`rcases` also has special support for quotient types: quotient induction into Prop works like
matching on the constructor `quot.mk`.

`rcases h : e with PAT` will do the same as `rcases e with PAT` with the exception that an
assumption `h : e = PAT` will be added to the context.

`rcases? e` will perform case splits on `e` in the same way as `rcases e`,
but rather than accepting a pattern, it does a maximal cases and prints the
pattern that would produce this case splitting. The default maximum depth is 5,
but this can be modified with `rcases? e : n`.
-/
unsafe def rcases : parse rcases_parse → tactic Unit
  | rcases_args.rcases h p ids => tactic.rcases h p ids
  | rcases_args.rcases_many ps ids => tactic.rcases_many ps ids
  | rcases_args.hint p depth => do
    let (pe, patt) ←
      match p with
        | Sum.inl p => Prod.mk <$> pp p <*> rcases_hint p depth
        | Sum.inr ps => do
          let patts ← rcases_hint_many ps depth
          let pes ← ps.mmap pp
          pure (format.bracket "⟨" "⟩" (format.comma_separated pes), rcases_patt.tuple patts)
    let ppat ← pp patt
    trace <| ↑"Try this: rcases " ++ pe ++ " with " ++ ppat
#align tactic.interactive.rcases tactic.interactive.rcases

add_tactic_doc
  { Name := "rcases"
    category := DocCategory.tactic
    declNames := [`tactic.interactive.rcases]
    tags := ["induction"] }

/-- The `rintro` tactic is a combination of the `intros` tactic with `rcases` to
allow for destructuring patterns while introducing variables. See `rcases` for
a description of supported patterns. For example, `rintro (a | ⟨b, c⟩) ⟨d, e⟩`
will introduce two variables, and then do case splits on both of them producing
two subgoals, one with variables `a d e` and the other with `b c d e`.

`rintro`, unlike `rcases`, also supports the form `(x y : ty)` for introducing
and type-ascripting multiple variables at once, similar to binders.

`rintro?` will introduce and case split on variables in the same way as
`rintro`, but will also print the `rintro` invocation that would have the same
result. Like `rcases?`, `rintro? : n` allows for modifying the
depth of splitting; the default is 5.

`rintros` is an alias for `rintro`.
-/
unsafe def rintro : parse rintro_parse → tactic Unit
  | Sum.inl [] => intros []
  | Sum.inl l => tactic.rintro l
  | Sum.inr depth => do
    let ps ← tactic.rintro_hint depth
    let fs ←
      ps.mmap fun p => do
          let f ← pp <| p.format true
          pure <| format.space ++ format.group f
    trace <| ↑"Try this: rintro" ++ format.join fs
#align tactic.interactive.rintro tactic.interactive.rintro

/-- Alias for `rintro`. -/
unsafe def rintros :=
  rintro
#align tactic.interactive.rintros tactic.interactive.rintros

add_tactic_doc
  { Name := "rintro"
    category := DocCategory.tactic
    declNames := [`tactic.interactive.rintro, `tactic.interactive.rintros]
    tags := ["induction"]
    inheritDescriptionFrom := `tactic.interactive.rintro }

/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `parser.optional -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `parser.optional -/
/-- Parses `patt? (: expr)? (:= expr)?`, the arguments for `obtain`.
 (This is almost the same as `rcases_patt_parse`,
but it allows the pattern part to be empty.) -/
unsafe def obtain_parse :
    parser ((Option rcases_patt × Option pexpr) × Option (Sum pexpr (List pexpr))) :=
  (with_desc "patt? (: expr)? (:= expr)?") do
    let (pat, tp) ←
      (do
            let pat ← rcases_patt_parse
            pure <|
                match pat with
                | rcases_patt.typed pat tp => (some pat, some tp)
                | _ => (some pat, none)) <|>
          Prod.mk none <$> parser.optional (tk ":" >> texpr)
    Prod.mk (pat, tp) <$>
        parser.optional do
          tk ":="
          guard tp >> Sum.inr <$> brackets "⟨" "⟩" (sep_by (tk ",") (parser.pexpr 0)) <|>
              Sum.inl <$> texpr
#align tactic.interactive.obtain_parse tactic.interactive.obtain_parse

/-- The `obtain` tactic is a combination of `have` and `rcases`. See `rcases` for
a description of supported patterns.

```lean
obtain ⟨patt⟩ : type,
{ ... }
```
is equivalent to
```lean
have h : type,
{ ... },
rcases h with ⟨patt⟩
```

The syntax `obtain ⟨patt⟩ : type := proof` is also supported.

If `⟨patt⟩` is omitted, `rcases` will try to infer the pattern.

If `type` is omitted, `:= proof` is required.
-/
unsafe def obtain : parse obtain_parse → tactic Unit
  | ((pat, _), some (Sum.inr val)) => tactic.rcases_many val (pat.getOrElse default)
  | ((pat, none), some (Sum.inl val)) => tactic.rcases none val (pat.getOrElse default)
  | ((pat, some tp), some (Sum.inl val)) =>
    tactic.rcases none val <| (pat.getOrElse default).typed tp
  | ((pat, some tp), none) => do
    let nm ← mk_fresh_name
    let e ← to_expr tp >>= assert nm
    let g :: gs ← get_goals
    set_goals gs
    tactic.rcases none ``($(e)) (pat (rcases_patt.one `this))
    let gs ← get_goals
    set_goals (g :: gs)
  | ((pat, none), none) =>
    fail <|
      "`obtain` requires either an expected type or a value.\n" ++
        "usage: `obtain ⟨patt⟩? : type (:= val)?` or `obtain ⟨patt⟩? (: type)? := val`"
#align tactic.interactive.obtain tactic.interactive.obtain

add_tactic_doc
  { Name := "obtain"
    category := DocCategory.tactic
    declNames := [`tactic.interactive.obtain]
    tags := ["induction"] }

/-- The `rsuffices` tactic is an alternative version of `suffices`, that allows the usage
of any syntax that would be valid in an `obtain` block. This tactic just calls `obtain`
on the expression, and then `rotate 1`.
-/
unsafe def rsuffices (h : parse obtain_parse) : tactic Unit :=
  focus1 <| obtain h >> tactic.rotate 1
#align tactic.interactive.rsuffices tactic.interactive.rsuffices

add_tactic_doc
  { Name := "rsuffices"
    category := DocCategory.tactic
    declNames := [`tactic.interactive.rsuffices]
    tags := ["induction"] }

/--
The `rsufficesI` tactic is an instance-cache aware version of `rsuffices`; it resets the instance
cache on the resulting goals.
-/
unsafe def rsufficesI (h : parse obtain_parse) : tactic Unit :=
  andthen (rsuffices h) resetI
#align tactic.interactive.rsufficesI tactic.interactive.rsufficesI

add_tactic_doc
  { Name := "rsufficesI"
    category := DocCategory.tactic
    declNames := [`tactic.interactive.rsufficesI]
    tags := ["induction", "type class"] }

end Interactive

end Tactic

