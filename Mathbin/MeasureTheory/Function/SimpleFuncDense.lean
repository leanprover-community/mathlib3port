/-
Copyright (c) 2019 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Yury Kudryashov, Heather Macbeth

! This file was ported from Lean 3 source module measure_theory.function.simple_func_dense
! leanprover-community/mathlib commit 6d0adfa76594f304b4650d098273d4366edeb61b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.MeasureTheory.Integral.Lebesgue

/-!
# Density of simple functions

Show that each Borel measurable function can be approximated pointwise
by a sequence of simple functions.

## Main definitions

* `measure_theory.simple_func.nearest_pt (e : ℕ → α) (N : ℕ) : α →ₛ ℕ`: the `simple_func` sending
  each `x : α` to the point `e k` which is the nearest to `x` among `e 0`, ..., `e N`.
* `measure_theory.simple_func.approx_on (f : β → α) (hf : measurable f) (s : set α) (y₀ : α)
  (h₀ : y₀ ∈ s) [separable_space s] (n : ℕ) : β →ₛ α` : a simple function that takes values in `s`
  and approximates `f`.

## Main results

* `tendsto_approx_on` (pointwise convergence): If `f x ∈ s`, then the sequence of simple
  approximations `measure_theory.simple_func.approx_on f hf s y₀ h₀ n`, evaluated at `x`,
  tends to `f x` as `n` tends to `∞`.

## Notations

* `α →ₛ β` (local notation): the type of simple functions `α → β`.
-/


open Set Function Filter TopologicalSpace Ennreal Emetric Finset

open Classical TopologicalSpace Ennreal MeasureTheory BigOperators

variable {α β ι E F 𝕜 : Type _}

noncomputable section

namespace MeasureTheory

-- mathport name: «expr →ₛ »
local infixr:25 " →ₛ " => SimpleFunc

namespace SimpleFunc

/-! ### Pointwise approximation by simple functions -/


variable [MeasurableSpace α] [PseudoEmetricSpace α] [OpensMeasurableSpace α]

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "`nearest_pt_ind e N x` is the index `k` such that `e k` is the nearest point to `x` among the\npoints `e 0`, ..., `e N`. If more than one point are at the same distance from `x`, then\n`nearest_pt_ind e N x` returns the least of their indexes. -/")]
      []
      []
      [(Command.noncomputable "noncomputable")]
      []
      [])
     (Command.def
      "def"
      (Command.declId `nearestPtInd [])
      (Command.optDeclSig
       [(Term.explicitBinder "(" [`e] [":" (Term.arrow (termℕ "ℕ") "→" `α)] [] ")")]
       [(Term.typeSpec
         ":"
         (Term.arrow
          (termℕ "ℕ")
          "→"
          (MeasureTheory.MeasureTheory.Function.SimpleFuncDense.«term_→ₛ_»
           `α
           " →ₛ "
           (termℕ "ℕ"))))])
      (Command.declValEqns
       (Term.matchAltsWhereDecls
        (Term.matchAlts
         [(Term.matchAlt "|" [[(num "0")]] "=>" (Term.app `const [`α (num "0")]))
          (Term.matchAlt
           "|"
           [[(«term_+_» `N "+" (num "1"))]]
           "=>"
           (Term.app
            `piecewise
            [(Set.Data.Set.Lattice.«term⋂_,_»
              "⋂"
              (Std.ExtendedBinder.extBinders
               (Std.ExtendedBinder.extBinder
                (Lean.binderIdent `k)
                [(Std.ExtendedBinder.«binderTerm≤_» "≤" `N)]))
              ", "
              (Set.«term{_|_}»
               "{"
               (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) [])
               "|"
               («term_<_»
                (Term.app `edist [(Term.app `e [(«term_+_» `N "+" (num "1"))]) `x])
                "<"
                (Term.app `edist [(Term.app `e [`k]) `x]))
               "}"))
             (Term.app
              `MeasurableSet.Inter
              [(Term.fun
                "fun"
                (Term.basicFun
                 [`k]
                 []
                 "=>"
                 (Term.app
                  `MeasurableSet.Inter
                  [(Term.fun
                    "fun"
                    (Term.basicFun
                     [`hk]
                     []
                     "=>"
                     (Term.app
                      `measurable_set_lt
                      [`measurable_edist_right `measurable_edist_right])))])))])
             («term_<|_» (Term.app `const [`α]) "<|" («term_+_» `N "+" (num "1")))
             (Term.app `nearest_pt_ind [`N])]))])
        []))
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValEqns', expected 'Lean.Parser.Command.declValSimple'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `piecewise
       [(Set.Data.Set.Lattice.«term⋂_,_»
         "⋂"
         (Std.ExtendedBinder.extBinders
          (Std.ExtendedBinder.extBinder
           (Lean.binderIdent `k)
           [(Std.ExtendedBinder.«binderTerm≤_» "≤" `N)]))
         ", "
         (Set.«term{_|_}»
          "{"
          (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) [])
          "|"
          («term_<_»
           (Term.app `edist [(Term.app `e [(«term_+_» `N "+" (num "1"))]) `x])
           "<"
           (Term.app `edist [(Term.app `e [`k]) `x]))
          "}"))
        (Term.app
         `MeasurableSet.Inter
         [(Term.fun
           "fun"
           (Term.basicFun
            [`k]
            []
            "=>"
            (Term.app
             `MeasurableSet.Inter
             [(Term.fun
               "fun"
               (Term.basicFun
                [`hk]
                []
                "=>"
                (Term.app
                 `measurable_set_lt
                 [`measurable_edist_right `measurable_edist_right])))])))])
        («term_<|_» (Term.app `const [`α]) "<|" («term_+_» `N "+" (num "1")))
        (Term.app `nearest_pt_ind [`N])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `nearest_pt_ind [`N])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `N
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `nearest_pt_ind
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `nearest_pt_ind [`N]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_<|_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_<|_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      («term_<|_» (Term.app `const [`α]) "<|" («term_+_» `N "+" (num "1")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_» `N "+" (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `N
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      (Term.app `const [`α])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `α
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `const
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 10, (some 10, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_<|_» (Term.app `const [`α]) "<|" («term_+_» `N "+" (num "1")))
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       `MeasurableSet.Inter
       [(Term.fun
         "fun"
         (Term.basicFun
          [`k]
          []
          "=>"
          (Term.app
           `MeasurableSet.Inter
           [(Term.fun
             "fun"
             (Term.basicFun
              [`hk]
              []
              "=>"
              (Term.app
               `measurable_set_lt
               [`measurable_edist_right `measurable_edist_right])))])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`k]
        []
        "=>"
        (Term.app
         `MeasurableSet.Inter
         [(Term.fun
           "fun"
           (Term.basicFun
            [`hk]
            []
            "=>"
            (Term.app `measurable_set_lt [`measurable_edist_right `measurable_edist_right])))])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `MeasurableSet.Inter
       [(Term.fun
         "fun"
         (Term.basicFun
          [`hk]
          []
          "=>"
          (Term.app `measurable_set_lt [`measurable_edist_right `measurable_edist_right])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`hk]
        []
        "=>"
        (Term.app `measurable_set_lt [`measurable_edist_right `measurable_edist_right])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `measurable_set_lt [`measurable_edist_right `measurable_edist_right])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `measurable_edist_right
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `measurable_edist_right
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `measurable_set_lt
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hk
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `MeasurableSet.Inter
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `MeasurableSet.Inter
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `MeasurableSet.Inter
      [(Term.fun
        "fun"
        (Term.basicFun
         [`k]
         []
         "=>"
         (Term.app
          `MeasurableSet.Inter
          [(Term.fun
            "fun"
            (Term.basicFun
             [`hk]
             []
             "=>"
             (Term.app `measurable_set_lt [`measurable_edist_right `measurable_edist_right])))])))])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.Data.Set.Lattice.«term⋂_,_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.Data.Set.Lattice.«term⋂_,_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Set.Data.Set.Lattice.«term⋂_,_»
       "⋂"
       (Std.ExtendedBinder.extBinders
        (Std.ExtendedBinder.extBinder
         (Lean.binderIdent `k)
         [(Std.ExtendedBinder.«binderTerm≤_» "≤" `N)]))
       ", "
       (Set.«term{_|_}»
        "{"
        (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) [])
        "|"
        («term_<_»
         (Term.app `edist [(Term.app `e [(«term_+_» `N "+" (num "1"))]) `x])
         "<"
         (Term.app `edist [(Term.app `e [`k]) `x]))
        "}"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Set.«term{_|_}»
       "{"
       (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) [])
       "|"
       («term_<_»
        (Term.app `edist [(Term.app `e [(«term_+_» `N "+" (num "1"))]) `x])
        "<"
        (Term.app `edist [(Term.app `e [`k]) `x]))
       "}")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<_»
       (Term.app `edist [(Term.app `e [(«term_+_» `N "+" (num "1"))]) `x])
       "<"
       (Term.app `edist [(Term.app `e [`k]) `x]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `edist [(Term.app `e [`k]) `x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `e [`k])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `e
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `e [`k]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `edist
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app `edist [(Term.app `e [(«term_+_» `N "+" (num "1"))]) `x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `e [(«term_+_» `N "+" (num "1"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_+_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_+_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_» `N "+" (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `N
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_+_» `N "+" (num "1")) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `e
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `e [(Term.paren "(" («term_+_» `N "+" (num "1")) ")")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `edist
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Std.ExtendedBinder.«binderTerm≤_»', expected 'group'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `N
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Set.Data.Set.Lattice.«term⋂_,_»
      "⋂"
      (Std.ExtendedBinder.extBinders
       (Std.ExtendedBinder.extBinder
        (Lean.binderIdent `k)
        [(Std.ExtendedBinder.«binderTerm≤_» "≤" `N)]))
      ", "
      (Set.«term{_|_}»
       "{"
       (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) [])
       "|"
       («term_<_»
        (Term.app
         `edist
         [(Term.paren "(" (Term.app `e [(Term.paren "(" («term_+_» `N "+" (num "1")) ")")]) ")")
          `x])
        "<"
        (Term.app `edist [(Term.paren "(" (Term.app `e [`k]) ")") `x]))
       "}"))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `piecewise
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_» `N "+" (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `N
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app `const [`α (num "0")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `α
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `const
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.arrow
       (termℕ "ℕ")
       "→"
       (MeasureTheory.MeasureTheory.Function.SimpleFuncDense.«term_→ₛ_» `α " →ₛ " (termℕ "ℕ")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (MeasureTheory.MeasureTheory.Function.SimpleFuncDense.«term_→ₛ_» `α " →ₛ " (termℕ "ℕ"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'MeasureTheory.MeasureTheory.Function.SimpleFuncDense.«term_→ₛ_»', expected 'MeasureTheory.MeasureTheory.Function.SimpleFuncDense.term_→ₛ_._@.MeasureTheory.Function.SimpleFuncDense._hyg.9'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
      `nearest_pt_ind e N x` is the index `k` such that `e k` is the nearest point to `x` among the
      points `e 0`, ..., `e N`. If more than one point are at the same distance from `x`, then
      `nearest_pt_ind e N x` returns the least of their indexes. -/
    noncomputable
  def
    nearestPtInd
    ( e : ℕ → α ) : ℕ → α →ₛ ℕ
    | 0 => const α 0
      |
        N + 1
        =>
        piecewise
          ⋂ k ≤ N , { x | edist e N + 1 x < edist e k x }
            MeasurableSet.Inter
              fun
                k
                  =>
                  MeasurableSet.Inter
                    fun hk => measurable_set_lt measurable_edist_right measurable_edist_right
            const α <| N + 1
            nearest_pt_ind N
#align measure_theory.simple_func.nearest_pt_ind MeasureTheory.SimpleFunc.nearestPtInd

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "`nearest_pt e N x` is the nearest point to `x` among the points `e 0`, ..., `e N`. If more than\none point are at the same distance from `x`, then `nearest_pt e N x` returns the point with the\nleast possible index. -/")]
      []
      []
      [(Command.noncomputable "noncomputable")]
      []
      [])
     (Command.def
      "def"
      (Command.declId `nearestPt [])
      (Command.optDeclSig
       [(Term.explicitBinder "(" [`e] [":" (Term.arrow (termℕ "ℕ") "→" `α)] [] ")")
        (Term.explicitBinder "(" [`N] [":" (termℕ "ℕ")] [] ")")]
       [(Term.typeSpec
         ":"
         (MeasureTheory.MeasureTheory.Function.SimpleFuncDense.«term_→ₛ_» `α " →ₛ " `α))])
      (Command.declValSimple
       ":="
       (Term.app (Term.proj (Term.app `nearestPtInd [`e `N]) "." `map) [`e])
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj (Term.app `nearestPtInd [`e `N]) "." `map) [`e])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `e
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app `nearestPtInd [`e `N]) "." `map)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `nearestPtInd [`e `N])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `N
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `e
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `nearestPtInd
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `nearestPtInd [`e `N]) ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (MeasureTheory.MeasureTheory.Function.SimpleFuncDense.«term_→ₛ_» `α " →ₛ " `α)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'MeasureTheory.MeasureTheory.Function.SimpleFuncDense.«term_→ₛ_»', expected 'MeasureTheory.MeasureTheory.Function.SimpleFuncDense.term_→ₛ_._@.MeasureTheory.Function.SimpleFuncDense._hyg.9'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
      `nearest_pt e N x` is the nearest point to `x` among the points `e 0`, ..., `e N`. If more than
      one point are at the same distance from `x`, then `nearest_pt e N x` returns the point with the
      least possible index. -/
    noncomputable
  def nearestPt ( e : ℕ → α ) ( N : ℕ ) : α →ₛ α := nearestPtInd e N . map e
#align measure_theory.simple_func.nearest_pt MeasureTheory.SimpleFunc.nearestPt

@[simp]
theorem nearest_pt_ind_zero (e : ℕ → α) : nearestPtInd e 0 = const α 0 :=
  rfl
#align measure_theory.simple_func.nearest_pt_ind_zero MeasureTheory.SimpleFunc.nearest_pt_ind_zero

@[simp]
theorem nearest_pt_zero (e : ℕ → α) : nearestPt e 0 = const α (e 0) :=
  rfl
#align measure_theory.simple_func.nearest_pt_zero MeasureTheory.SimpleFunc.nearest_pt_zero

theorem nearest_pt_ind_succ (e : ℕ → α) (N : ℕ) (x : α) :
    nearestPtInd e (N + 1) x =
      if ∀ k ≤ N, edist (e (N + 1)) x < edist (e k) x then N + 1 else nearestPtInd e N x :=
  by
  simp only [nearest_pt_ind, coe_piecewise, Set.piecewise]
  congr
  simp
#align measure_theory.simple_func.nearest_pt_ind_succ MeasureTheory.SimpleFunc.nearest_pt_ind_succ

theorem nearest_pt_ind_le (e : ℕ → α) (N : ℕ) (x : α) : nearestPtInd e N x ≤ N :=
  by
  induction' N with N ihN; · simp
  simp only [nearest_pt_ind_succ]
  split_ifs
  exacts[le_rfl, ihN.trans N.le_succ]
#align measure_theory.simple_func.nearest_pt_ind_le MeasureTheory.SimpleFunc.nearest_pt_ind_le

theorem edist_nearest_pt_le (e : ℕ → α) (x : α) {k N : ℕ} (hk : k ≤ N) :
    edist (nearestPt e N x) x ≤ edist (e k) x :=
  by
  induction' N with N ihN generalizing k
  · simp [nonpos_iff_eq_zero.1 hk, le_refl]
  · simp only [nearest_pt, nearest_pt_ind_succ, map_apply]
    split_ifs
    · rcases hk.eq_or_lt with (rfl | hk)
      exacts[le_rfl, (h k (Nat.lt_succ_iff.1 hk)).le]
    · push_neg  at h
      rcases h with ⟨l, hlN, hxl⟩
      rcases hk.eq_or_lt with (rfl | hk)
      exacts[(ihN hlN).trans hxl, ihN (Nat.lt_succ_iff.1 hk)]
#align measure_theory.simple_func.edist_nearest_pt_le MeasureTheory.SimpleFunc.edist_nearest_pt_le

theorem tendsto_nearest_pt {e : ℕ → α} {x : α} (hx : x ∈ closure (range e)) :
    Tendsto (fun N => nearestPt e N x) atTop (𝓝 x) :=
  by
  refine' (at_top_basis.tendsto_iff nhds_basis_eball).2 fun ε hε => _
  rcases Emetric.mem_closure_iff.1 hx ε hε with ⟨_, ⟨N, rfl⟩, hN⟩
  rw [edist_comm] at hN
  exact ⟨N, trivial, fun n hn => (edist_nearest_pt_le e x hn).trans_lt hN⟩
#align measure_theory.simple_func.tendsto_nearest_pt MeasureTheory.SimpleFunc.tendsto_nearest_pt

variable [MeasurableSpace β] {f : β → α}

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "Approximate a measurable function by a sequence of simple functions `F n` such that\n`F n x ∈ s`. -/")]
      []
      []
      [(Command.noncomputable "noncomputable")]
      []
      [])
     (Command.def
      "def"
      (Command.declId `approxOn [])
      (Command.optDeclSig
       [(Term.explicitBinder "(" [`f] [":" (Term.arrow `β "→" `α)] [] ")")
        (Term.explicitBinder "(" [`hf] [":" (Term.app `Measurable [`f])] [] ")")
        (Term.explicitBinder "(" [`s] [":" (Term.app `Set [`α])] [] ")")
        (Term.explicitBinder "(" [`y₀] [":" `α] [] ")")
        (Term.explicitBinder "(" [`h₀] [":" («term_∈_» `y₀ "∈" `s)] [] ")")
        (Term.instBinder "[" [] (Term.app `SeparableSpace [`s]) "]")
        (Term.explicitBinder "(" [`n] [":" (termℕ "ℕ")] [] ")")]
       [(Term.typeSpec
         ":"
         (MeasureTheory.MeasureTheory.Function.SimpleFuncDense.«term_→ₛ_» `β " →ₛ " `α))])
      (Command.declValSimple
       ":="
       (Std.Tactic.haveI
        "haveI"
        (Term.haveDecl
         (Term.haveIdDecl
          []
          [(Term.typeSpec ":" (Term.app `Nonempty [`s]))]
          ":="
          (Term.anonymousCtor "⟨" [(Term.anonymousCtor "⟨" [`y₀ "," `h₀] "⟩")] "⟩")))
        []
        (Term.app
         `comp
         [(Term.app
           `nearest_pt
           [(Term.typeAscription
             "("
             (Term.fun
              "fun"
              (Term.basicFun
               [`k]
               []
               "=>"
               (Term.app `Nat.casesOn [`k `y₀ («term_∘_» `coe "∘" (Term.app `dense_seq [`s]))])))
             ":"
             [(Term.arrow (termℕ "ℕ") "→" `α)]
             ")")
            `n])
          `f
          `hf]))
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.haveI
       "haveI"
       (Term.haveDecl
        (Term.haveIdDecl
         []
         [(Term.typeSpec ":" (Term.app `Nonempty [`s]))]
         ":="
         (Term.anonymousCtor "⟨" [(Term.anonymousCtor "⟨" [`y₀ "," `h₀] "⟩")] "⟩")))
       []
       (Term.app
        `comp
        [(Term.app
          `nearest_pt
          [(Term.typeAscription
            "("
            (Term.fun
             "fun"
             (Term.basicFun
              [`k]
              []
              "=>"
              (Term.app `Nat.casesOn [`k `y₀ («term_∘_» `coe "∘" (Term.app `dense_seq [`s]))])))
            ":"
            [(Term.arrow (termℕ "ℕ") "→" `α)]
            ")")
           `n])
         `f
         `hf]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `comp
       [(Term.app
         `nearest_pt
         [(Term.typeAscription
           "("
           (Term.fun
            "fun"
            (Term.basicFun
             [`k]
             []
             "=>"
             (Term.app `Nat.casesOn [`k `y₀ («term_∘_» `coe "∘" (Term.app `dense_seq [`s]))])))
           ":"
           [(Term.arrow (termℕ "ℕ") "→" `α)]
           ")")
          `n])
        `f
        `hf])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hf
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       `nearest_pt
       [(Term.typeAscription
         "("
         (Term.fun
          "fun"
          (Term.basicFun
           [`k]
           []
           "=>"
           (Term.app `Nat.casesOn [`k `y₀ («term_∘_» `coe "∘" (Term.app `dense_seq [`s]))])))
         ":"
         [(Term.arrow (termℕ "ℕ") "→" `α)]
         ")")
        `n])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.typeAscription
       "("
       (Term.fun
        "fun"
        (Term.basicFun
         [`k]
         []
         "=>"
         (Term.app `Nat.casesOn [`k `y₀ («term_∘_» `coe "∘" (Term.app `dense_seq [`s]))])))
       ":"
       [(Term.arrow (termℕ "ℕ") "→" `α)]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.arrow (termℕ "ℕ") "→" `α)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `α
[PrettyPrinter.parenthesize] ...precedences are 25 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
      (termℕ "ℕ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 25, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 25, (some 25, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`k]
        []
        "=>"
        (Term.app `Nat.casesOn [`k `y₀ («term_∘_» `coe "∘" (Term.app `dense_seq [`s]))])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Nat.casesOn [`k `y₀ («term_∘_» `coe "∘" (Term.app `dense_seq [`s]))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_∘_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_∘_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∘_» `coe "∘" (Term.app `dense_seq [`s]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `dense_seq [`s])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `s
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `dense_seq
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 90 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 90, term))
      `coe
[PrettyPrinter.parenthesize] ...precedences are 91 >? 1024, (none, [anonymous]) <=? (some 90, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 90, (some 90, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_∘_» `coe "∘" (Term.app `dense_seq [`s]))
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `y₀
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `k
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Nat.casesOn
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `nearest_pt
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `nearest_pt
      [(Term.typeAscription
        "("
        (Term.fun
         "fun"
         (Term.basicFun
          [`k]
          []
          "=>"
          (Term.app
           `Nat.casesOn
           [`k `y₀ (Term.paren "(" («term_∘_» `coe "∘" (Term.app `dense_seq [`s])) ")")])))
        ":"
        [(Term.arrow (termℕ "ℕ") "→" `α)]
        ")")
       `n])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `comp
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [(Term.anonymousCtor "⟨" [`y₀ "," `h₀] "⟩")] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [`y₀ "," `h₀] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h₀
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y₀
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Nonempty [`s])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `s
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Nonempty
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (MeasureTheory.MeasureTheory.Function.SimpleFuncDense.«term_→ₛ_» `β " →ₛ " `α)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'MeasureTheory.MeasureTheory.Function.SimpleFuncDense.«term_→ₛ_»', expected 'MeasureTheory.MeasureTheory.Function.SimpleFuncDense.term_→ₛ_._@.MeasureTheory.Function.SimpleFuncDense._hyg.9'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
      Approximate a measurable function by a sequence of simple functions `F n` such that
      `F n x ∈ s`. -/
    noncomputable
  def
    approxOn
    ( f : β → α )
        ( hf : Measurable f )
        ( s : Set α )
        ( y₀ : α )
        ( h₀ : y₀ ∈ s )
        [ SeparableSpace s ]
        ( n : ℕ )
      : β →ₛ α
    :=
      haveI
        : Nonempty s := ⟨ ⟨ y₀ , h₀ ⟩ ⟩
        comp nearest_pt ( fun k => Nat.casesOn k y₀ coe ∘ dense_seq s : ℕ → α ) n f hf
#align measure_theory.simple_func.approx_on MeasureTheory.SimpleFunc.approxOn

@[simp]
theorem approx_on_zero {f : β → α} (hf : Measurable f) {s : Set α} {y₀ : α} (h₀ : y₀ ∈ s)
    [SeparableSpace s] (x : β) : approxOn f hf s y₀ h₀ 0 x = y₀ :=
  rfl
#align measure_theory.simple_func.approx_on_zero MeasureTheory.SimpleFunc.approx_on_zero

theorem approx_on_mem {f : β → α} (hf : Measurable f) {s : Set α} {y₀ : α} (h₀ : y₀ ∈ s)
    [SeparableSpace s] (n : ℕ) (x : β) : approxOn f hf s y₀ h₀ n x ∈ s :=
  by
  haveI : Nonempty s := ⟨⟨y₀, h₀⟩⟩
  suffices ∀ n, (Nat.casesOn n y₀ (coe ∘ dense_seq s) : α) ∈ s by apply this
  rintro (_ | n)
  exacts[h₀, Subtype.mem _]
#align measure_theory.simple_func.approx_on_mem MeasureTheory.SimpleFunc.approx_on_mem

@[simp]
theorem approx_on_comp {γ : Type _} [MeasurableSpace γ] {f : β → α} (hf : Measurable f) {g : γ → β}
    (hg : Measurable g) {s : Set α} {y₀ : α} (h₀ : y₀ ∈ s) [SeparableSpace s] (n : ℕ) :
    approxOn (f ∘ g) (hf.comp hg) s y₀ h₀ n = (approxOn f hf s y₀ h₀ n).comp g hg :=
  rfl
#align measure_theory.simple_func.approx_on_comp MeasureTheory.SimpleFunc.approx_on_comp

theorem tendsto_approx_on {f : β → α} (hf : Measurable f) {s : Set α} {y₀ : α} (h₀ : y₀ ∈ s)
    [SeparableSpace s] {x : β} (hx : f x ∈ closure s) :
    Tendsto (fun n => approxOn f hf s y₀ h₀ n x) atTop (𝓝 <| f x) :=
  by
  haveI : Nonempty s := ⟨⟨y₀, h₀⟩⟩
  rw [← @Subtype.range_coe _ s, ← image_univ, ← (dense_range_dense_seq s).closure_eq] at hx
  simp only [approx_on, coe_comp]
  refine' tendsto_nearest_pt (closure_minimal _ is_closed_closure hx)
  simp only [Nat.range_casesOn, closure_union, range_comp coe]
  exact
    subset.trans (image_closure_subset_closure_image continuous_subtype_coe)
      (subset_union_right _ _)
#align measure_theory.simple_func.tendsto_approx_on MeasureTheory.SimpleFunc.tendsto_approx_on

theorem edist_approx_on_mono {f : β → α} (hf : Measurable f) {s : Set α} {y₀ : α} (h₀ : y₀ ∈ s)
    [SeparableSpace s] (x : β) {m n : ℕ} (h : m ≤ n) :
    edist (approxOn f hf s y₀ h₀ n x) (f x) ≤ edist (approxOn f hf s y₀ h₀ m x) (f x) :=
  by
  dsimp only [approx_on, coe_comp, (· ∘ ·)]
  exact edist_nearest_pt_le _ _ ((nearest_pt_ind_le _ _ _).trans h)
#align measure_theory.simple_func.edist_approx_on_mono MeasureTheory.SimpleFunc.edist_approx_on_mono

theorem edist_approx_on_le {f : β → α} (hf : Measurable f) {s : Set α} {y₀ : α} (h₀ : y₀ ∈ s)
    [SeparableSpace s] (x : β) (n : ℕ) : edist (approxOn f hf s y₀ h₀ n x) (f x) ≤ edist y₀ (f x) :=
  edist_approx_on_mono hf h₀ x (zero_le n)
#align measure_theory.simple_func.edist_approx_on_le MeasureTheory.SimpleFunc.edist_approx_on_le

theorem edist_approx_on_y0_le {f : β → α} (hf : Measurable f) {s : Set α} {y₀ : α} (h₀ : y₀ ∈ s)
    [SeparableSpace s] (x : β) (n : ℕ) :
    edist y₀ (approxOn f hf s y₀ h₀ n x) ≤ edist y₀ (f x) + edist y₀ (f x) :=
  calc
    edist y₀ (approxOn f hf s y₀ h₀ n x) ≤
        edist y₀ (f x) + edist (approxOn f hf s y₀ h₀ n x) (f x) :=
      edist_triangle_right _ _ _
    _ ≤ edist y₀ (f x) + edist y₀ (f x) := add_le_add_left (edist_approx_on_le hf h₀ x n) _
    
#align
  measure_theory.simple_func.edist_approx_on_y0_le MeasureTheory.SimpleFunc.edist_approx_on_y0_le

end SimpleFunc

end MeasureTheory

