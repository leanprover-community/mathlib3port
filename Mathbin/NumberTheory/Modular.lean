/-
Copyright (c) 2021 Alex Kontorovich and Heather Macbeth and Marc Masdeu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Kontorovich, Heather Macbeth, Marc Masdeu

! This file was ported from Lean 3 source module number_theory.modular
! leanprover-community/mathlib commit 6afc9b06856ad973f6a2619e3e8a0a8d537a58f2
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.Complex.UpperHalfPlane.Basic
import Mathbin.LinearAlgebra.GeneralLinearGroup

/-!
# The action of the modular group SL(2, ℤ) on the upper half-plane

We define the action of `SL(2,ℤ)` on `ℍ` (via restriction of the `SL(2,ℝ)` action in
`analysis.complex.upper_half_plane`). We then define the standard fundamental domain
(`modular_group.fd`, `𝒟`) for this action and show
(`modular_group.exists_smul_mem_fd`) that any point in `ℍ` can be
moved inside `𝒟`.

## Main definitions

The standard (closed) fundamental domain of the action of `SL(2,ℤ)` on `ℍ`, denoted `𝒟`:
`fd := {z | 1 ≤ (z : ℂ).norm_sq ∧ |z.re| ≤ (1 : ℝ) / 2}`

The standard open fundamental domain of the action of `SL(2,ℤ)` on `ℍ`, denoted `𝒟ᵒ`:
`fdo := {z | 1 < (z : ℂ).norm_sq ∧ |z.re| < (1 : ℝ) / 2}`

These notations are localized in the `modular` locale and can be enabled via `open_locale modular`.

## Main results

Any `z : ℍ` can be moved to `𝒟` by an element of `SL(2,ℤ)`:
`exists_smul_mem_fd (z : ℍ) : ∃ g : SL(2,ℤ), g • z ∈ 𝒟`

If both `z` and `γ • z` are in the open domain `𝒟ᵒ` then `z = γ • z`:
`eq_smul_self_of_mem_fdo_mem_fdo {z : ℍ} {g : SL(2,ℤ)} (hz : z ∈ 𝒟ᵒ) (hg : g • z ∈ 𝒟ᵒ) : z = g • z`

# Discussion

Standard proofs make use of the identity

`g • z = a / c - 1 / (c (cz + d))`

for `g = [[a, b], [c, d]]` in `SL(2)`, but this requires separate handling of whether `c = 0`.
Instead, our proof makes use of the following perhaps novel identity (see
`modular_group.smul_eq_lc_row0_add`):

`g • z = (a c + b d) / (c^2 + d^2) + (d z - c) / ((c^2 + d^2) (c z + d))`

where there is no issue of division by zero.

Another feature is that we delay until the very end the consideration of special matrices
`T=[[1,1],[0,1]]` (see `modular_group.T`) and `S=[[0,-1],[1,0]]` (see `modular_group.S`), by
instead using abstract theory on the properness of certain maps (phrased in terms of the filters
`filter.cocompact`, `filter.cofinite`, etc) to deduce existence theorems, first to prove the
existence of `g` maximizing `(g•z).im` (see `modular_group.exists_max_im`), and then among
those, to minimize `|(g•z).re|` (see `modular_group.exists_row_one_eq_and_min_re`).
-/


/- Disable these instances as they are not the simp-normal form, and having them disabled ensures
we state lemmas in this file without spurious `coe_fn` terms. -/
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToFun

attribute [-instance] Matrix.GeneralLinearGroup.hasCoeToFun

open Complex hiding abs_two

open Matrix hiding mul_smul

open Matrix.SpecialLinearGroup UpperHalfPlane

noncomputable section

-- mathport name: «exprSL( , )»
local notation "SL(" n ", " R ")" => SpecialLinearGroup (Fin n) R

-- mathport name: «expr↑ₘ »
local prefix:1024 "↑ₘ" => @coe _ (Matrix (Fin 2) (Fin 2) ℤ) _

open UpperHalfPlane ComplexConjugate

attribute [local instance] Fintype.card_fin_even

namespace ModularGroup

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.variable
     "variable"
     [(Term.implicitBinder
       "{"
       [`g]
       [":" (NumberTheory.Modular.«termSL(_,_)» "SL(" (num "2") ", " (termℤ "ℤ") ")")]
       "}")
      (Term.explicitBinder
       "("
       [`z]
       [":" (UpperHalfPlane.Analysis.Complex.UpperHalfPlane.Basic.upper_half_plane "ℍ")]
       []
       ")")])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (UpperHalfPlane.Analysis.Complex.UpperHalfPlane.Basic.upper_half_plane "ℍ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.implicitBinder', expected 'Lean.Parser.Term.explicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.implicitBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (NumberTheory.Modular.«termSL(_,_)» "SL(" (num "2") ", " (termℤ "ℤ") ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.Modular.«termSL(_,_)»', expected 'NumberTheory.Modular.termSL(_,_)._@.NumberTheory.Modular._hyg.8'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.implicitBinder', expected 'Lean.Parser.Term.instBinder'-/-- failed to format: format: uncaught backtrack exception
variable { g : SL( 2 , ℤ ) } ( z : ℍ )

section BottomRow

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "The two numbers `c`, `d` in the \"bottom_row\" of `g=[[*,*],[c,d]]` in `SL(2, ℤ)` are coprime. -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `bottom_row_coprime [])
      (Command.declSig
       [(Term.implicitBinder "{" [`R] [":" (Term.type "Type" [(Level.hole "_")])] "}")
        (Term.instBinder "[" [] (Term.app `CommRing [`R]) "]")
        (Term.explicitBinder
         "("
         [`g]
         [":" (NumberTheory.Modular.«termSL(_,_)» "SL(" (num "2") ", " `R ")")]
         []
         ")")]
       (Term.typeSpec
        ":"
        (Term.app
         `IsCoprime
         [(Term.app
           (Term.typeAscription
            "("
            (coeNotation "↑" `g)
            ":"
            [(Term.app `Matrix [(Term.app `Fin [(num "2")]) (Term.app `Fin [(num "2")]) `R])]
            ")")
           [(num "1") (num "0")])
          (Term.app
           (Term.typeAscription
            "("
            (coeNotation "↑" `g)
            ":"
            [(Term.app `Matrix [(Term.app `Fin [(num "2")]) (Term.app `Fin [(num "2")]) `R])]
            ")")
           [(num "1") (num "1")])])))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Mathlib.Tactic.«tacticUse_,,»
            "use"
            [(«term-_»
              "-"
              (Term.app
               (Term.typeAscription
                "("
                (coeNotation "↑" `g)
                ":"
                [(Term.app `Matrix [(Term.app `Fin [(num "2")]) (Term.app `Fin [(num "2")]) `R])]
                ")")
               [(num "0") (num "1")]))
             ","
             (Term.app
              (Term.typeAscription
               "("
               (coeNotation "↑" `g)
               ":"
               [(Term.app `Matrix [(Term.app `Fin [(num "2")]) (Term.app `Fin [(num "2")]) `R])]
               ")")
              [(num "0") (num "0")])])
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [] `add_comm)
              ","
              (Tactic.rwRule [] `neg_mul)
              ","
              (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `sub_eq_add_neg)
              ","
              (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `det_fin_two)]
             "]")
            [])
           []
           (Tactic.exact "exact" `g.det_coe)])))
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
         [(Mathlib.Tactic.«tacticUse_,,»
           "use"
           [(«term-_»
             "-"
             (Term.app
              (Term.typeAscription
               "("
               (coeNotation "↑" `g)
               ":"
               [(Term.app `Matrix [(Term.app `Fin [(num "2")]) (Term.app `Fin [(num "2")]) `R])]
               ")")
              [(num "0") (num "1")]))
            ","
            (Term.app
             (Term.typeAscription
              "("
              (coeNotation "↑" `g)
              ":"
              [(Term.app `Matrix [(Term.app `Fin [(num "2")]) (Term.app `Fin [(num "2")]) `R])]
              ")")
             [(num "0") (num "0")])])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `add_comm)
             ","
             (Tactic.rwRule [] `neg_mul)
             ","
             (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `sub_eq_add_neg)
             ","
             (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `det_fin_two)]
            "]")
           [])
          []
          (Tactic.exact "exact" `g.det_coe)])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" `g.det_coe)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g.det_coe
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `add_comm)
         ","
         (Tactic.rwRule [] `neg_mul)
         ","
         (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `sub_eq_add_neg)
         ","
         (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `det_fin_two)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `det_fin_two
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `sub_eq_add_neg
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `neg_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `add_comm
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.«tacticUse_,,»
       "use"
       [(«term-_»
         "-"
         (Term.app
          (Term.typeAscription
           "("
           (coeNotation "↑" `g)
           ":"
           [(Term.app `Matrix [(Term.app `Fin [(num "2")]) (Term.app `Fin [(num "2")]) `R])]
           ")")
          [(num "0") (num "1")]))
        ","
        (Term.app
         (Term.typeAscription
          "("
          (coeNotation "↑" `g)
          ":"
          [(Term.app `Matrix [(Term.app `Fin [(num "2")]) (Term.app `Fin [(num "2")]) `R])]
          ")")
         [(num "0") (num "0")])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.typeAscription
        "("
        (coeNotation "↑" `g)
        ":"
        [(Term.app `Matrix [(Term.app `Fin [(num "2")]) (Term.app `Fin [(num "2")]) `R])]
        ")")
       [(num "0") (num "0")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.typeAscription
       "("
       (coeNotation "↑" `g)
       ":"
       [(Term.app `Matrix [(Term.app `Fin [(num "2")]) (Term.app `Fin [(num "2")]) `R])]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Matrix [(Term.app `Fin [(num "2")]) (Term.app `Fin [(num "2")]) `R])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `R
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `Fin [(num "2")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Fin
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `Fin [(num "2")]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `Fin [(num "2")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Fin
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `Fin [(num "2")]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Matrix
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (coeNotation "↑" `g)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 1024, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term-_»
       "-"
       (Term.app
        (Term.typeAscription
         "("
         (coeNotation "↑" `g)
         ":"
         [(Term.app `Matrix [(Term.app `Fin [(num "2")]) (Term.app `Fin [(num "2")]) `R])]
         ")")
        [(num "0") (num "1")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.typeAscription
        "("
        (coeNotation "↑" `g)
        ":"
        [(Term.app `Matrix [(Term.app `Fin [(num "2")]) (Term.app `Fin [(num "2")]) `R])]
        ")")
       [(num "0") (num "1")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.typeAscription
       "("
       (coeNotation "↑" `g)
       ":"
       [(Term.app `Matrix [(Term.app `Fin [(num "2")]) (Term.app `Fin [(num "2")]) `R])]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Matrix [(Term.app `Fin [(num "2")]) (Term.app `Fin [(num "2")]) `R])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `R
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `Fin [(num "2")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Fin
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `Fin [(num "2")]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `Fin [(num "2")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Fin
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `Fin [(num "2")]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Matrix
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (coeNotation "↑" `g)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 1024, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 75 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 75, (some 75, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app
       `IsCoprime
       [(Term.app
         (Term.typeAscription
          "("
          (coeNotation "↑" `g)
          ":"
          [(Term.app `Matrix [(Term.app `Fin [(num "2")]) (Term.app `Fin [(num "2")]) `R])]
          ")")
         [(num "1") (num "0")])
        (Term.app
         (Term.typeAscription
          "("
          (coeNotation "↑" `g)
          ":"
          [(Term.app `Matrix [(Term.app `Fin [(num "2")]) (Term.app `Fin [(num "2")]) `R])]
          ")")
         [(num "1") (num "1")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.typeAscription
        "("
        (coeNotation "↑" `g)
        ":"
        [(Term.app `Matrix [(Term.app `Fin [(num "2")]) (Term.app `Fin [(num "2")]) `R])]
        ")")
       [(num "1") (num "1")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.typeAscription
       "("
       (coeNotation "↑" `g)
       ":"
       [(Term.app `Matrix [(Term.app `Fin [(num "2")]) (Term.app `Fin [(num "2")]) `R])]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Matrix [(Term.app `Fin [(num "2")]) (Term.app `Fin [(num "2")]) `R])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `R
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `Fin [(num "2")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Fin
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `Fin [(num "2")]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `Fin [(num "2")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Fin
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `Fin [(num "2")]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Matrix
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (coeNotation "↑" `g)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 1024, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      (Term.typeAscription
       "("
       (coeNotation "↑" `g)
       ":"
       [(Term.app
         `Matrix
         [(Term.paren "(" (Term.app `Fin [(num "2")]) ")")
          (Term.paren "(" (Term.app `Fin [(num "2")]) ")")
          `R])]
       ")")
      [(num "1") (num "1")])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       (Term.typeAscription
        "("
        (coeNotation "↑" `g)
        ":"
        [(Term.app `Matrix [(Term.app `Fin [(num "2")]) (Term.app `Fin [(num "2")]) `R])]
        ")")
       [(num "1") (num "0")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.typeAscription
       "("
       (coeNotation "↑" `g)
       ":"
       [(Term.app `Matrix [(Term.app `Fin [(num "2")]) (Term.app `Fin [(num "2")]) `R])]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Matrix [(Term.app `Fin [(num "2")]) (Term.app `Fin [(num "2")]) `R])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `R
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `Fin [(num "2")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Fin
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `Fin [(num "2")]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `Fin [(num "2")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Fin
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `Fin [(num "2")]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Matrix
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (coeNotation "↑" `g)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 1024, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      (Term.typeAscription
       "("
       (coeNotation "↑" `g)
       ":"
       [(Term.app
         `Matrix
         [(Term.paren "(" (Term.app `Fin [(num "2")]) ")")
          (Term.paren "(" (Term.app `Fin [(num "2")]) ")")
          `R])]
       ")")
      [(num "1") (num "0")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `IsCoprime
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (NumberTheory.Modular.«termSL(_,_)» "SL(" (num "2") ", " `R ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.Modular.«termSL(_,_)»', expected 'NumberTheory.Modular.termSL(_,_)._@.NumberTheory.Modular._hyg.8'
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
/-- The two numbers `c`, `d` in the "bottom_row" of `g=[[*,*],[c,d]]` in `SL(2, ℤ)` are coprime. -/
  theorem
    bottom_row_coprime
    { R : Type _ } [ CommRing R ] ( g : SL( 2 , R ) )
      : IsCoprime ( ↑ g : Matrix Fin 2 Fin 2 R ) 1 0 ( ↑ g : Matrix Fin 2 Fin 2 R ) 1 1
    :=
      by
        use - ( ↑ g : Matrix Fin 2 Fin 2 R ) 0 1 , ( ↑ g : Matrix Fin 2 Fin 2 R ) 0 0
          rw [ add_comm , neg_mul , ← sub_eq_add_neg , ← det_fin_two ]
          exact g.det_coe
#align modular_group.bottom_row_coprime ModularGroup.bottom_row_coprime

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "Every pair `![c, d]` of coprime integers is the \"bottom_row\" of some element `g=[[*,*],[c,d]]`\nof `SL(2,ℤ)`. -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `bottom_row_surj [])
      (Command.declSig
       [(Term.implicitBinder "{" [`R] [":" (Term.type "Type" [(Level.hole "_")])] "}")
        (Term.instBinder "[" [] (Term.app `CommRing [`R]) "]")]
       (Term.typeSpec
        ":"
        (Term.app
         `Set.SurjOn
         [(Term.fun
           "fun"
           (Term.basicFun
            [`g]
            [(Term.typeSpec ":" (NumberTheory.Modular.«termSL(_,_)» "SL(" (num "2") ", " `R ")"))]
            "=>"
            (Term.app
             (Term.explicit "@" `coe)
             [(Term.hole "_")
              (Term.app `Matrix [(Term.app `Fin [(num "2")]) (Term.app `Fin [(num "2")]) `R])
              (Term.hole "_")
              `g
              (num "1")])))
          `Set.univ
          (Set.«term{_|_}»
           "{"
           (Std.ExtendedBinder.extBinder (Lean.binderIdent `cd) [])
           "|"
           (Term.app `IsCoprime [(Term.app `cd [(num "0")]) (Term.app `cd [(num "1")])])
           "}")])))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Std.Tactic.rintro
            "rintro"
            [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `cd))
             (Std.Tactic.RCases.rintroPat.one
              (Std.Tactic.RCases.rcasesPat.tuple
               "⟨"
               [(Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `b₀)])
                 [])
                ","
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `a)])
                 [])
                ","
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `gcd_eqn)])
                 [])]
               "⟩"))]
            [])
           []
           (Tactic.tacticLet_
            "let"
            (Term.letDecl
             (Term.letIdDecl
              `A
              []
              []
              ":="
              (Term.app
               `of
               [(Matrix.Data.Fin.VecNotation.«term![_,»
                 "!["
                 [(Matrix.Data.Fin.VecNotation.«term![_,» "![" [`a "," («term-_» "-" `b₀)] "]")
                  ","
                  `cd]
                 "]")]))))
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`det_A_1 []]
              [(Term.typeSpec ":" («term_=_» (Term.app `det [`A]) "=" (num "1")))]
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(convert "convert" [] `gcd_eqn [])
                  []
                  (Tactic.simp
                   "simp"
                   []
                   []
                   []
                   ["["
                    [(Tactic.simpLemma [] [] `A)
                     ","
                     (Tactic.simpLemma [] [] `det_fin_two)
                     ","
                     (Tactic.simpLemma
                      []
                      []
                      (Term.typeAscription
                       "("
                       (Term.byTactic
                        "by"
                        (Tactic.tacticSeq
                         (Tactic.tacticSeq1Indented [(Mathlib.Tactic.RingNF.ring "ring")])))
                       ":"
                       [(«term_=_»
                         («term_+_»
                          («term_*_» `a "*" (Term.app `cd [(num "1")]))
                          "+"
                          («term_*_» `b₀ "*" (Term.app `cd [(num "0")])))
                         "="
                         («term_+_»
                          («term_*_» `b₀ "*" (Term.app `cd [(num "0")]))
                          "+"
                          («term_*_» `a "*" (Term.app `cd [(num "1")]))))]
                       ")"))]
                    "]"]
                   [])]))))))
           []
           (Tactic.refine'
            "refine'"
            (Term.anonymousCtor
             "⟨"
             [(Term.anonymousCtor "⟨" [`A "," `det_A_1] "⟩")
              ","
              (Term.app `Set.mem_univ [(Term.hole "_")])
              ","
              (Term.hole "_")]
             "⟩"))
           []
           (Tactic.«tactic_<;>_»
            (Std.Tactic.Ext.«tacticExt___:_» "ext" [] [])
            "<;>"
            (Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `A)] "]"] []))])))
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
         [(Std.Tactic.rintro
           "rintro"
           [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `cd))
            (Std.Tactic.RCases.rintroPat.one
             (Std.Tactic.RCases.rcasesPat.tuple
              "⟨"
              [(Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `b₀)])
                [])
               ","
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `a)])
                [])
               ","
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `gcd_eqn)])
                [])]
              "⟩"))]
           [])
          []
          (Tactic.tacticLet_
           "let"
           (Term.letDecl
            (Term.letIdDecl
             `A
             []
             []
             ":="
             (Term.app
              `of
              [(Matrix.Data.Fin.VecNotation.«term![_,»
                "!["
                [(Matrix.Data.Fin.VecNotation.«term![_,» "![" [`a "," («term-_» "-" `b₀)] "]")
                 ","
                 `cd]
                "]")]))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`det_A_1 []]
             [(Term.typeSpec ":" («term_=_» (Term.app `det [`A]) "=" (num "1")))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(convert "convert" [] `gcd_eqn [])
                 []
                 (Tactic.simp
                  "simp"
                  []
                  []
                  []
                  ["["
                   [(Tactic.simpLemma [] [] `A)
                    ","
                    (Tactic.simpLemma [] [] `det_fin_two)
                    ","
                    (Tactic.simpLemma
                     []
                     []
                     (Term.typeAscription
                      "("
                      (Term.byTactic
                       "by"
                       (Tactic.tacticSeq
                        (Tactic.tacticSeq1Indented [(Mathlib.Tactic.RingNF.ring "ring")])))
                      ":"
                      [(«term_=_»
                        («term_+_»
                         («term_*_» `a "*" (Term.app `cd [(num "1")]))
                         "+"
                         («term_*_» `b₀ "*" (Term.app `cd [(num "0")])))
                        "="
                        («term_+_»
                         («term_*_» `b₀ "*" (Term.app `cd [(num "0")]))
                         "+"
                         («term_*_» `a "*" (Term.app `cd [(num "1")]))))]
                      ")"))]
                   "]"]
                  [])]))))))
          []
          (Tactic.refine'
           "refine'"
           (Term.anonymousCtor
            "⟨"
            [(Term.anonymousCtor "⟨" [`A "," `det_A_1] "⟩")
             ","
             (Term.app `Set.mem_univ [(Term.hole "_")])
             ","
             (Term.hole "_")]
            "⟩"))
          []
          (Tactic.«tactic_<;>_»
           (Std.Tactic.Ext.«tacticExt___:_» "ext" [] [])
           "<;>"
           (Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `A)] "]"] []))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.«tactic_<;>_»
       (Std.Tactic.Ext.«tacticExt___:_» "ext" [] [])
       "<;>"
       (Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `A)] "]"] []))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `A)] "]"] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `A
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 2 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
      (Std.Tactic.Ext.«tacticExt___:_» "ext" [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine'
       "refine'"
       (Term.anonymousCtor
        "⟨"
        [(Term.anonymousCtor "⟨" [`A "," `det_A_1] "⟩")
         ","
         (Term.app `Set.mem_univ [(Term.hole "_")])
         ","
         (Term.hole "_")]
        "⟩"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.anonymousCtor "⟨" [`A "," `det_A_1] "⟩")
        ","
        (Term.app `Set.mem_univ [(Term.hole "_")])
        ","
        (Term.hole "_")]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Set.mem_univ [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Set.mem_univ
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [`A "," `det_A_1] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `det_A_1
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `A
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`det_A_1 []]
         [(Term.typeSpec ":" («term_=_» (Term.app `det [`A]) "=" (num "1")))]
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(convert "convert" [] `gcd_eqn [])
             []
             (Tactic.simp
              "simp"
              []
              []
              []
              ["["
               [(Tactic.simpLemma [] [] `A)
                ","
                (Tactic.simpLemma [] [] `det_fin_two)
                ","
                (Tactic.simpLemma
                 []
                 []
                 (Term.typeAscription
                  "("
                  (Term.byTactic
                   "by"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented [(Mathlib.Tactic.RingNF.ring "ring")])))
                  ":"
                  [(«term_=_»
                    («term_+_»
                     («term_*_» `a "*" (Term.app `cd [(num "1")]))
                     "+"
                     («term_*_» `b₀ "*" (Term.app `cd [(num "0")])))
                    "="
                    («term_+_»
                     («term_*_» `b₀ "*" (Term.app `cd [(num "0")]))
                     "+"
                     («term_*_» `a "*" (Term.app `cd [(num "1")]))))]
                  ")"))]
               "]"]
              [])]))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(convert "convert" [] `gcd_eqn [])
          []
          (Tactic.simp
           "simp"
           []
           []
           []
           ["["
            [(Tactic.simpLemma [] [] `A)
             ","
             (Tactic.simpLemma [] [] `det_fin_two)
             ","
             (Tactic.simpLemma
              []
              []
              (Term.typeAscription
               "("
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented [(Mathlib.Tactic.RingNF.ring "ring")])))
               ":"
               [(«term_=_»
                 («term_+_»
                  («term_*_» `a "*" (Term.app `cd [(num "1")]))
                  "+"
                  («term_*_» `b₀ "*" (Term.app `cd [(num "0")])))
                 "="
                 («term_+_»
                  («term_*_» `b₀ "*" (Term.app `cd [(num "0")]))
                  "+"
                  («term_*_» `a "*" (Term.app `cd [(num "1")]))))]
               ")"))]
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
        [(Tactic.simpLemma [] [] `A)
         ","
         (Tactic.simpLemma [] [] `det_fin_two)
         ","
         (Tactic.simpLemma
          []
          []
          (Term.typeAscription
           "("
           (Term.byTactic
            "by"
            (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Mathlib.Tactic.RingNF.ring "ring")])))
           ":"
           [(«term_=_»
             («term_+_»
              («term_*_» `a "*" (Term.app `cd [(num "1")]))
              "+"
              («term_*_» `b₀ "*" (Term.app `cd [(num "0")])))
             "="
             («term_+_»
              («term_*_» `b₀ "*" (Term.app `cd [(num "0")]))
              "+"
              («term_*_» `a "*" (Term.app `cd [(num "1")]))))]
           ")"))]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription
       "("
       (Term.byTactic
        "by"
        (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Mathlib.Tactic.RingNF.ring "ring")])))
       ":"
       [(«term_=_»
         («term_+_»
          («term_*_» `a "*" (Term.app `cd [(num "1")]))
          "+"
          («term_*_» `b₀ "*" (Term.app `cd [(num "0")])))
         "="
         («term_+_»
          («term_*_» `b₀ "*" (Term.app `cd [(num "0")]))
          "+"
          («term_*_» `a "*" (Term.app `cd [(num "1")]))))]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       («term_+_»
        («term_*_» `a "*" (Term.app `cd [(num "1")]))
        "+"
        («term_*_» `b₀ "*" (Term.app `cd [(num "0")])))
       "="
       («term_+_»
        («term_*_» `b₀ "*" (Term.app `cd [(num "0")]))
        "+"
        («term_*_» `a "*" (Term.app `cd [(num "1")]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_»
       («term_*_» `b₀ "*" (Term.app `cd [(num "0")]))
       "+"
       («term_*_» `a "*" (Term.app `cd [(num "1")])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_» `a "*" (Term.app `cd [(num "1")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `cd [(num "1")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `cd
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `a
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      («term_*_» `b₀ "*" (Term.app `cd [(num "0")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `cd [(num "0")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `cd
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `b₀
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 65 >? 70, (some 71, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      («term_+_»
       («term_*_» `a "*" (Term.app `cd [(num "1")]))
       "+"
       («term_*_» `b₀ "*" (Term.app `cd [(num "0")])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_» `b₀ "*" (Term.app `cd [(num "0")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `cd [(num "0")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `cd
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `b₀
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      («term_*_» `a "*" (Term.app `cd [(num "1")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `cd [(num "1")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `cd
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `a
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 65 >? 70, (some 71, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 65, (some 66, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Mathlib.Tactic.RingNF.ring "ring")])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.RingNF.ring "ring")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `det_fin_two
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `A
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (convert "convert" [] `gcd_eqn [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `gcd_eqn
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_» (Term.app `det [`A]) "=" (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app `det [`A])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `A
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `det
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticLet_
       "let"
       (Term.letDecl
        (Term.letIdDecl
         `A
         []
         []
         ":="
         (Term.app
          `of
          [(Matrix.Data.Fin.VecNotation.«term![_,»
            "!["
            [(Matrix.Data.Fin.VecNotation.«term![_,» "![" [`a "," («term-_» "-" `b₀)] "]") "," `cd]
            "]")]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `of
       [(Matrix.Data.Fin.VecNotation.«term![_,»
         "!["
         [(Matrix.Data.Fin.VecNotation.«term![_,» "![" [`a "," («term-_» "-" `b₀)] "]") "," `cd]
         "]")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Matrix.Data.Fin.VecNotation.«term![_,»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Matrix.Data.Fin.VecNotation.«term![_,»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Matrix.Data.Fin.VecNotation.«term![_,»
       "!["
       [(Matrix.Data.Fin.VecNotation.«term![_,» "![" [`a "," («term-_» "-" `b₀)] "]") "," `cd]
       "]")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `cd
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Matrix.Data.Fin.VecNotation.«term![_,» "![" [`a "," («term-_» "-" `b₀)] "]")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term-_» "-" `b₀)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `b₀
[PrettyPrinter.parenthesize] ...precedences are 75 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 75, (some 75, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `of
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.rintro
       "rintro"
       [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `cd))
        (Std.Tactic.RCases.rintroPat.one
         (Std.Tactic.RCases.rcasesPat.tuple
          "⟨"
          [(Std.Tactic.RCases.rcasesPatLo
            (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `b₀)])
            [])
           ","
           (Std.Tactic.RCases.rcasesPatLo
            (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `a)])
            [])
           ","
           (Std.Tactic.RCases.rcasesPatLo
            (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `gcd_eqn)])
            [])]
          "⟩"))]
       [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app
       `Set.SurjOn
       [(Term.fun
         "fun"
         (Term.basicFun
          [`g]
          [(Term.typeSpec ":" (NumberTheory.Modular.«termSL(_,_)» "SL(" (num "2") ", " `R ")"))]
          "=>"
          (Term.app
           (Term.explicit "@" `coe)
           [(Term.hole "_")
            (Term.app `Matrix [(Term.app `Fin [(num "2")]) (Term.app `Fin [(num "2")]) `R])
            (Term.hole "_")
            `g
            (num "1")])))
        `Set.univ
        (Set.«term{_|_}»
         "{"
         (Std.ExtendedBinder.extBinder (Lean.binderIdent `cd) [])
         "|"
         (Term.app `IsCoprime [(Term.app `cd [(num "0")]) (Term.app `cd [(num "1")])])
         "}")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Set.«term{_|_}»
       "{"
       (Std.ExtendedBinder.extBinder (Lean.binderIdent `cd) [])
       "|"
       (Term.app `IsCoprime [(Term.app `cd [(num "0")]) (Term.app `cd [(num "1")])])
       "}")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `IsCoprime [(Term.app `cd [(num "0")]) (Term.app `cd [(num "1")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `cd [(num "1")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `cd
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `cd [(num "1")]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `cd [(num "0")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `cd
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `cd [(num "0")]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `IsCoprime
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      `Set.univ
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.fun
       "fun"
       (Term.basicFun
        [`g]
        [(Term.typeSpec ":" (NumberTheory.Modular.«termSL(_,_)» "SL(" (num "2") ", " `R ")"))]
        "=>"
        (Term.app
         (Term.explicit "@" `coe)
         [(Term.hole "_")
          (Term.app `Matrix [(Term.app `Fin [(num "2")]) (Term.app `Fin [(num "2")]) `R])
          (Term.hole "_")
          `g
          (num "1")])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.explicit "@" `coe)
       [(Term.hole "_")
        (Term.app `Matrix [(Term.app `Fin [(num "2")]) (Term.app `Fin [(num "2")]) `R])
        (Term.hole "_")
        `g
        (num "1")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.app `Matrix [(Term.app `Fin [(num "2")]) (Term.app `Fin [(num "2")]) `R])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `R
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `Fin [(num "2")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Fin
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `Fin [(num "2")]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `Fin [(num "2")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Fin
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `Fin [(num "2")]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Matrix
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `Matrix
      [(Term.paren "(" (Term.app `Fin [(num "2")]) ")")
       (Term.paren "(" (Term.app `Fin [(num "2")]) ")")
       `R])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.explicit "@" `coe)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `coe
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (some 1024,
     term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (NumberTheory.Modular.«termSL(_,_)» "SL(" (num "2") ", " `R ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.Modular.«termSL(_,_)»', expected 'NumberTheory.Modular.termSL(_,_)._@.NumberTheory.Modular._hyg.8'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    Every pair `![c, d]` of coprime integers is the "bottom_row" of some element `g=[[*,*],[c,d]]`
    of `SL(2,ℤ)`. -/
  theorem
    bottom_row_surj
    { R : Type _ } [ CommRing R ]
      :
        Set.SurjOn
          fun g : SL( 2 , R ) => @ coe _ Matrix Fin 2 Fin 2 R _ g 1
            Set.univ
            { cd | IsCoprime cd 0 cd 1 }
    :=
      by
        rintro cd ⟨ b₀ , a , gcd_eqn ⟩
          let A := of ![ ![ a , - b₀ ] , cd ]
          have
            det_A_1
              : det A = 1
              :=
              by
                convert gcd_eqn
                  simp
                    [ A , det_fin_two , ( by ring : a * cd 1 + b₀ * cd 0 = b₀ * cd 0 + a * cd 1 ) ]
          refine' ⟨ ⟨ A , det_A_1 ⟩ , Set.mem_univ _ , _ ⟩
          ext <;> simp [ A ]
#align modular_group.bottom_row_surj ModularGroup.bottom_row_surj

end BottomRow

section TendstoLemmas

open Filter ContinuousLinearMap

attribute [local simp] coe_smul

/-- The function `(c,d) → |cz+d|^2` is proper, that is, preimages of bounded-above sets are finite.
-/
theorem tendsto_norm_sq_coprime_pair :
    Filter.Tendsto (fun p : Fin 2 → ℤ => ((p 0 : ℂ) * z + p 1).normSq) cofinite atTop :=
  by
  -- using this instance rather than the automatic `function.module` makes unification issues in
  -- `linear_equiv.closed_embedding_of_injective` less bad later in the proof.
  letI : Module ℝ (Fin 2 → ℝ) := NormedSpace.toModule
  let π₀ : (Fin 2 → ℝ) →ₗ[ℝ] ℝ := LinearMap.proj 0
  let π₁ : (Fin 2 → ℝ) →ₗ[ℝ] ℝ := LinearMap.proj 1
  let f : (Fin 2 → ℝ) →ₗ[ℝ] ℂ := π₀.smul_right (z : ℂ) + π₁.smul_right 1
  have f_def : ⇑f = fun p : Fin 2 → ℝ => (p 0 : ℂ) * ↑z + p 1 :=
    by
    ext1
    dsimp only [LinearMap.coe_proj, real_smul, LinearMap.coe_smul_right, LinearMap.add_apply]
    rw [mul_one]
  have :
    (fun p : Fin 2 → ℤ => norm_sq ((p 0 : ℂ) * ↑z + ↑(p 1))) =
      norm_sq ∘ f ∘ fun p : Fin 2 → ℤ => (coe : ℤ → ℝ) ∘ p :=
    by
    ext1
    rw [f_def]
    dsimp only [Function.comp]
    rw [of_real_int_cast, of_real_int_cast]
  rw [this]
  have hf : f.ker = ⊥ :=
    by
    let g : ℂ →ₗ[ℝ] Fin 2 → ℝ :=
      LinearMap.pi ![im_lm, im_lm.comp ((z : ℂ) • ((conj_ae : ℂ →ₐ[ℝ] ℂ) : ℂ →ₗ[ℝ] ℂ))]
    suffices ((z : ℂ).im⁻¹ • g).comp f = LinearMap.id by exact LinearMap.ker_eq_bot_of_inverse this
    apply LinearMap.ext
    intro c
    have hz : (z : ℂ).im ≠ 0 := z.2.ne'
    rw [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply]
    ext i
    dsimp only [g, Pi.smul_apply, LinearMap.pi_apply, smul_eq_mul]
    fin_cases i
    · show (z : ℂ).im⁻¹ * (f c).im = c 0
      rw [f_def, add_im, of_real_mul_im, of_real_im, add_zero, mul_left_comm, inv_mul_cancel hz,
        mul_one]
    · show (z : ℂ).im⁻¹ * ((z : ℂ) * conj (f c)).im = c 1
      rw [f_def, RingHom.map_add, RingHom.map_mul, mul_add, mul_left_comm, mul_conj, conj_of_real,
        conj_of_real, ← of_real_mul, add_im, of_real_im, zero_add, inv_mul_eq_iff_eq_mul₀ hz]
      simp only [of_real_im, of_real_re, mul_im, zero_add, mul_zero]
  have hf' : ClosedEmbedding f :=
    by
    -- for some reason we get a timeout if we try and apply this lemma in a more sensible way
    have := @LinearEquiv.closed_embedding_of_injective ℝ _ (Fin 2 → ℝ) _ (id _) ℂ _ _ _ _
    rotate_left 2
    exact f
    exact this hf
  have h₂ : tendsto (fun p : Fin 2 → ℤ => (coe : ℤ → ℝ) ∘ p) cofinite (cocompact _) :=
    by
    convert tendsto.pi_map_Coprod fun i => Int.tendsto_coe_cofinite
    · rw [Coprod_cofinite]
    · rw [Coprod_cocompact]
  exact tendsto_norm_sq_cocompact_at_top.comp (hf'.tendsto_cocompact.comp h₂)
#align modular_group.tendsto_norm_sq_coprime_pair ModularGroup.tendsto_norm_sq_coprime_pair

/-- Given `coprime_pair` `p=(c,d)`, the matrix `[[a,b],[*,*]]` is sent to `a*c+b*d`.
  This is the linear map version of this operation.
-/
def lcRow0 (p : Fin 2 → ℤ) : Matrix (Fin 2) (Fin 2) ℝ →ₗ[ℝ] ℝ :=
  ((p 0 : ℝ) • LinearMap.proj 0 + (p 1 : ℝ) • LinearMap.proj 1 : (Fin 2 → ℝ) →ₗ[ℝ] ℝ).comp
    (LinearMap.proj 0)
#align modular_group.lc_row0 ModularGroup.lcRow0

@[simp]
theorem lc_row0_apply (p : Fin 2 → ℤ) (g : Matrix (Fin 2) (Fin 2) ℝ) :
    lcRow0 p g = p 0 * g 0 0 + p 1 * g 0 1 :=
  rfl
#align modular_group.lc_row0_apply ModularGroup.lc_row0_apply

/-- Linear map sending the matrix [a, b; c, d] to the matrix [ac₀ + bd₀, - ad₀ + bc₀; c, d], for
some fixed `(c₀, d₀)`. -/
@[simps]
def lcRow0Extend {cd : Fin 2 → ℤ} (hcd : IsCoprime (cd 0) (cd 1)) :
    Matrix (Fin 2) (Fin 2) ℝ ≃ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℝ :=
  LinearEquiv.piCongrRight
    ![by
      refine'
        LinearMap.GeneralLinearGroup.generalLinearEquiv ℝ (Fin 2 → ℝ)
          (general_linear_group.to_linear (plane_conformal_matrix (cd 0 : ℝ) (-(cd 1 : ℝ)) _))
      norm_cast
      rw [neg_sq]
      exact hcd.sq_add_sq_ne_zero, LinearEquiv.refl ℝ (Fin 2 → ℝ)]
#align modular_group.lc_row0_extend ModularGroup.lcRow0Extend

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "The map `lc_row0` is proper, that is, preimages of cocompact sets are finite in\n`[[* , *], [c, d]]`.-/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `tendsto_lc_row0 [])
      (Command.declSig
       [(Term.implicitBinder
         "{"
         [`cd]
         [":" (Term.arrow (Term.app `Fin [(num "2")]) "→" (termℤ "ℤ"))]
         "}")
        (Term.explicitBinder
         "("
         [`hcd]
         [":" (Term.app `IsCoprime [(Term.app `cd [(num "0")]) (Term.app `cd [(num "1")])])]
         []
         ")")]
       (Term.typeSpec
        ":"
        (Term.app
         `Tendsto
         [(Term.fun
           "fun"
           (Term.basicFun
            [`g]
            [(Term.typeSpec
              ":"
              («term{_:_//_}»
               "{"
               `g
               [":" (NumberTheory.Modular.«termSL(_,_)» "SL(" (num "2") ", " (termℤ "ℤ") ")")]
               "//"
               («term_=_» (Term.app (NumberTheory.Modular.«term↑ₘ_» "↑ₘ" `g) [(num "1")]) "=" `cd)
               "}"))]
            "=>"
            (Term.app
             `lcRow0
             [`cd
              (coeNotation
               "↑"
               (Term.typeAscription
                "("
                (coeNotation "↑" `g)
                ":"
                [(NumberTheory.Modular.«termSL(_,_)»
                  "SL("
                  (num "2")
                  ", "
                  (Data.Real.Basic.termℝ "ℝ")
                  ")")]
                ")"))])))
          `cofinite
          (Term.app `cocompact [(Data.Real.Basic.termℝ "ℝ")])])))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.tacticLet_
            "let"
            (Term.letDecl
             (Term.letIdDecl
              `mB
              []
              [(Term.typeSpec
                ":"
                (Term.arrow
                 (Data.Real.Basic.termℝ "ℝ")
                 "→"
                 (Term.app
                  `Matrix
                  [(Term.app `Fin [(num "2")])
                   (Term.app `Fin [(num "2")])
                   (Data.Real.Basic.termℝ "ℝ")])))]
              ":="
              (Term.fun
               "fun"
               (Term.basicFun
                [`t]
                []
                "=>"
                (Term.app
                 `of
                 [(Matrix.Data.Fin.VecNotation.«term![_,»
                   "!["
                   [(Matrix.Data.Fin.VecNotation.«term![_,»
                     "!["
                     [`t
                      ","
                      (Term.typeAscription
                       "("
                       («term-_» "-" (Term.typeAscription "(" (num "1") ":" [(termℤ "ℤ")] ")"))
                       ":"
                       [(Data.Real.Basic.termℝ "ℝ")]
                       ")")]
                     "]")
                    ","
                    («term_∘_» `coe "∘" `cd)]
                   "]")]))))))
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`hmB []]
              [(Term.typeSpec ":" (Term.app `Continuous [`mB]))]
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Tactic.refine' "refine'" (Term.app `continuous_matrix [(Term.hole "_")]))
                  []
                  (Tactic.simp
                   "simp"
                   []
                   []
                   ["only"]
                   ["["
                    [(Tactic.simpLemma [] [] `Fin.forall_fin_two)
                     ","
                     (Tactic.simpLemma [] [] `mB)
                     ","
                     (Tactic.simpLemma [] [] `continuous_const)
                     ","
                     (Tactic.simpLemma [] [] `continuous_id')
                     ","
                     (Tactic.simpLemma [] [] `of_apply)
                     ","
                     (Tactic.simpLemma [] [] `cons_val_zero)
                     ","
                     (Tactic.simpLemma [] [] `cons_val_one)
                     ","
                     (Tactic.simpLemma [] [] `and_self_iff)]
                    "]"]
                   [])]))))))
           []
           (Tactic.refine'
            "refine'"
            (Term.app
             `Filter.Tendsto.of_tendsto_comp
             [(Term.hole "_") (Term.app `comap_cocompact_le [`hmB])]))
           []
           (Tactic.tacticLet_
            "let"
            (Term.letDecl
             (Term.letIdDecl
              `f₁
              []
              [(Term.typeSpec
                ":"
                (Term.arrow
                 (NumberTheory.Modular.«termSL(_,_)» "SL(" (num "2") ", " (termℤ "ℤ") ")")
                 "→"
                 (Term.app
                  `Matrix
                  [(Term.app `Fin [(num "2")])
                   (Term.app `Fin [(num "2")])
                   (Data.Real.Basic.termℝ "ℝ")])))]
              ":="
              (Term.fun
               "fun"
               (Term.basicFun
                [`g]
                []
                "=>"
                (Term.app
                 `Matrix.map
                 [(Term.typeAscription
                   "("
                   (coeNotation "↑" `g)
                   ":"
                   [(Term.app `Matrix [(Term.hole "_") (Term.hole "_") (termℤ "ℤ")])]
                   ")")
                  (Term.typeAscription
                   "("
                   `coe
                   ":"
                   [(Term.arrow (termℤ "ℤ") "→" (Data.Real.Basic.termℝ "ℝ"))]
                   ")")]))))))
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`cocompact_ℝ_to_cofinite_ℤ_matrix []]
              [(Term.typeSpec
                ":"
                (Term.app
                 `tendsto
                 [(Term.fun
                   "fun"
                   (Term.basicFun
                    [`m]
                    [(Term.typeSpec
                      ":"
                      (Term.app
                       `Matrix
                       [(Term.app `Fin [(num "2")]) (Term.app `Fin [(num "2")]) (termℤ "ℤ")]))]
                    "=>"
                    (Term.app
                     `Matrix.map
                     [`m
                      (Term.typeAscription
                       "("
                       `coe
                       ":"
                       [(Term.arrow (termℤ "ℤ") "→" (Data.Real.Basic.termℝ "ℝ"))]
                       ")")])))
                  `cofinite
                  (Term.app `cocompact [(Term.hole "_")])]))]
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
                    ["only"]
                    [(Tactic.simpArgs
                      "["
                      [(Tactic.simpLemma [] [] `Coprod_cofinite)
                       ","
                       (Tactic.simpLemma [] [] `Coprod_cocompact)]
                      "]")]
                    ["using"
                     (Term.app
                      `tendsto.pi_map_Coprod
                      [(Term.fun
                        "fun"
                        (Term.basicFun
                         [`i]
                         [(Term.typeSpec ":" (Term.app `Fin [(num "2")]))]
                         "=>"
                         (Term.app
                          `tendsto.pi_map_Coprod
                          [(Term.fun
                            "fun"
                            (Term.basicFun
                             [`j]
                             [(Term.typeSpec ":" (Term.app `Fin [(num "2")]))]
                             "=>"
                             `Int.tendsto_coe_cofinite))])))])]))]))))))
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`hf₁ []]
              [(Term.typeSpec
                ":"
                (Term.app `tendsto [`f₁ `cofinite (Term.app `cocompact [(Term.hole "_")])]))]
              ":="
              (Term.app
               `cocompact_ℝ_to_cofinite_ℤ_matrix.comp
               [`subtype.coe_injective.tendsto_cofinite]))))
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`hf₂ []]
              [(Term.typeSpec ":" (Term.app `ClosedEmbedding [(Term.app `lc_row0_extend [`hcd])]))]
              ":="
              (Term.proj
               (Term.proj
                (Term.proj (Term.app `lc_row0_extend [`hcd]) "." `toContinuousLinearEquiv)
                "."
                `toHomeomorph)
               "."
               `ClosedEmbedding))))
           []
           (convert
            "convert"
            []
            (Term.app
             `hf₂.tendsto_cocompact.comp
             [(Term.app `hf₁.comp [`subtype.coe_injective.tendsto_cofinite])])
            ["using" (num "1")])
           []
           (Std.Tactic.Ext.«tacticExt___:_»
            "ext"
            [(Std.Tactic.RCases.rintroPat.binder
              "("
              [(Std.Tactic.RCases.rintroPat.one
                (Std.Tactic.RCases.rcasesPat.tuple
                 "⟨"
                 [(Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `g)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                   [])]
                 "⟩"))
               (Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `i))
               (Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `j))]
              []
              ")")]
            [":" (num "3")])
           []
           (Std.Tactic.seq_focus
            (Lean.Elab.Tactic.finCases "fin_cases" [`i] [])
            "<;>"
            "["
            [(Lean.Elab.Tactic.finCases "fin_cases" [`j] []) "," (Tactic.skip "skip")]
            "]")
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.simp
              "simp"
              []
              []
              ["only"]
              ["["
               [(Tactic.simpLemma [] [] `mB)
                ","
                (Tactic.simpLemma [] [] `mul_vec)
                ","
                (Tactic.simpLemma [] [] `dot_product)
                ","
                (Tactic.simpLemma [] [] `Fin.sum_univ_two)
                ","
                (Tactic.simpLemma [] [] `_root_.coe_coe)
                ","
                (Tactic.simpLemma [] [] `coe_matrix_coe)
                ","
                (Tactic.simpLemma [] [] `Int.coe_castRingHom)
                ","
                (Tactic.simpLemma [] [] `lc_row0_apply)
                ","
                (Tactic.simpLemma [] [] `Function.comp_apply)
                ","
                (Tactic.simpLemma [] [] `cons_val_zero)
                ","
                (Tactic.simpLemma [] [] `lc_row0_extend_apply)
                ","
                (Tactic.simpLemma [] [] `LinearMap.GeneralLinearGroup.coe_fn_general_linear_equiv)
                ","
                (Tactic.simpLemma [] [] `general_linear_group.to_linear_apply)
                ","
                (Tactic.simpLemma [] [] `coe_plane_conformal_matrix)
                ","
                (Tactic.simpLemma [] [] `neg_neg)
                ","
                (Tactic.simpLemma [] [] `mul_vec_lin_apply)
                ","
                (Tactic.simpLemma [] [] `cons_val_one)
                ","
                (Tactic.simpLemma [] [] `head_cons)
                ","
                (Tactic.simpLemma [] [] `of_apply)]
               "]"]
              [])])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(convert
              "convert"
              []
              (Term.app
               `congr_arg
               [(Term.fun
                 "fun"
                 (Term.basicFun
                  [`n]
                  [(Term.typeSpec ":" (termℤ "ℤ"))]
                  "=>"
                  (Term.typeAscription
                   "("
                   («term-_» "-" `n)
                   ":"
                   [(Data.Real.Basic.termℝ "ℝ")]
                   ")")))
                `g.det_coe.symm])
              ["using" (num "1")])
             []
             (Tactic.simp
              "simp"
              []
              []
              ["only"]
              ["["
               [(Tactic.simpLemma [] [] `f₁)
                ","
                (Tactic.simpLemma [] [] `mul_vec)
                ","
                (Tactic.simpLemma [] [] `dot_product)
                ","
                (Tactic.simpLemma [] [] `Fin.sum_univ_two)
                ","
                (Tactic.simpLemma [] [] `Matrix.det_fin_two)
                ","
                (Tactic.simpLemma [] [] `Function.comp_apply)
                ","
                (Tactic.simpLemma [] [] `Subtype.coe_mk)
                ","
                (Tactic.simpLemma [] [] `lc_row0_extend_apply)
                ","
                (Tactic.simpLemma [] [] `cons_val_zero)
                ","
                (Tactic.simpLemma [] [] `LinearMap.GeneralLinearGroup.coe_fn_general_linear_equiv)
                ","
                (Tactic.simpLemma [] [] `general_linear_group.to_linear_apply)
                ","
                (Tactic.simpLemma [] [] `coe_plane_conformal_matrix)
                ","
                (Tactic.simpLemma [] [] `mul_vec_lin_apply)
                ","
                (Tactic.simpLemma [] [] `cons_val_one)
                ","
                (Tactic.simpLemma [] [] `head_cons)
                ","
                (Tactic.simpLemma [] [] `map_apply)
                ","
                (Tactic.simpLemma [] [] `neg_mul)
                ","
                (Tactic.simpLemma [] [] `Int.cast_sub)
                ","
                (Tactic.simpLemma [] [] `Int.cast_mul)
                ","
                (Tactic.simpLemma [] [] `neg_sub)
                ","
                (Tactic.simpLemma [] [] `of_apply)]
               "]"]
              [])
             []
             (Mathlib.Tactic.RingNF.ring "ring")])
           []
           (tactic__ (cdotTk (patternIgnore (token.«· » "·"))) [(Tactic.tacticRfl "rfl")])])))
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
         [(Tactic.tacticLet_
           "let"
           (Term.letDecl
            (Term.letIdDecl
             `mB
             []
             [(Term.typeSpec
               ":"
               (Term.arrow
                (Data.Real.Basic.termℝ "ℝ")
                "→"
                (Term.app
                 `Matrix
                 [(Term.app `Fin [(num "2")])
                  (Term.app `Fin [(num "2")])
                  (Data.Real.Basic.termℝ "ℝ")])))]
             ":="
             (Term.fun
              "fun"
              (Term.basicFun
               [`t]
               []
               "=>"
               (Term.app
                `of
                [(Matrix.Data.Fin.VecNotation.«term![_,»
                  "!["
                  [(Matrix.Data.Fin.VecNotation.«term![_,»
                    "!["
                    [`t
                     ","
                     (Term.typeAscription
                      "("
                      («term-_» "-" (Term.typeAscription "(" (num "1") ":" [(termℤ "ℤ")] ")"))
                      ":"
                      [(Data.Real.Basic.termℝ "ℝ")]
                      ")")]
                    "]")
                   ","
                   («term_∘_» `coe "∘" `cd)]
                  "]")]))))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`hmB []]
             [(Term.typeSpec ":" (Term.app `Continuous [`mB]))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.refine' "refine'" (Term.app `continuous_matrix [(Term.hole "_")]))
                 []
                 (Tactic.simp
                  "simp"
                  []
                  []
                  ["only"]
                  ["["
                   [(Tactic.simpLemma [] [] `Fin.forall_fin_two)
                    ","
                    (Tactic.simpLemma [] [] `mB)
                    ","
                    (Tactic.simpLemma [] [] `continuous_const)
                    ","
                    (Tactic.simpLemma [] [] `continuous_id')
                    ","
                    (Tactic.simpLemma [] [] `of_apply)
                    ","
                    (Tactic.simpLemma [] [] `cons_val_zero)
                    ","
                    (Tactic.simpLemma [] [] `cons_val_one)
                    ","
                    (Tactic.simpLemma [] [] `and_self_iff)]
                   "]"]
                  [])]))))))
          []
          (Tactic.refine'
           "refine'"
           (Term.app
            `Filter.Tendsto.of_tendsto_comp
            [(Term.hole "_") (Term.app `comap_cocompact_le [`hmB])]))
          []
          (Tactic.tacticLet_
           "let"
           (Term.letDecl
            (Term.letIdDecl
             `f₁
             []
             [(Term.typeSpec
               ":"
               (Term.arrow
                (NumberTheory.Modular.«termSL(_,_)» "SL(" (num "2") ", " (termℤ "ℤ") ")")
                "→"
                (Term.app
                 `Matrix
                 [(Term.app `Fin [(num "2")])
                  (Term.app `Fin [(num "2")])
                  (Data.Real.Basic.termℝ "ℝ")])))]
             ":="
             (Term.fun
              "fun"
              (Term.basicFun
               [`g]
               []
               "=>"
               (Term.app
                `Matrix.map
                [(Term.typeAscription
                  "("
                  (coeNotation "↑" `g)
                  ":"
                  [(Term.app `Matrix [(Term.hole "_") (Term.hole "_") (termℤ "ℤ")])]
                  ")")
                 (Term.typeAscription
                  "("
                  `coe
                  ":"
                  [(Term.arrow (termℤ "ℤ") "→" (Data.Real.Basic.termℝ "ℝ"))]
                  ")")]))))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`cocompact_ℝ_to_cofinite_ℤ_matrix []]
             [(Term.typeSpec
               ":"
               (Term.app
                `tendsto
                [(Term.fun
                  "fun"
                  (Term.basicFun
                   [`m]
                   [(Term.typeSpec
                     ":"
                     (Term.app
                      `Matrix
                      [(Term.app `Fin [(num "2")]) (Term.app `Fin [(num "2")]) (termℤ "ℤ")]))]
                   "=>"
                   (Term.app
                    `Matrix.map
                    [`m
                     (Term.typeAscription
                      "("
                      `coe
                      ":"
                      [(Term.arrow (termℤ "ℤ") "→" (Data.Real.Basic.termℝ "ℝ"))]
                      ")")])))
                 `cofinite
                 (Term.app `cocompact [(Term.hole "_")])]))]
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
                   ["only"]
                   [(Tactic.simpArgs
                     "["
                     [(Tactic.simpLemma [] [] `Coprod_cofinite)
                      ","
                      (Tactic.simpLemma [] [] `Coprod_cocompact)]
                     "]")]
                   ["using"
                    (Term.app
                     `tendsto.pi_map_Coprod
                     [(Term.fun
                       "fun"
                       (Term.basicFun
                        [`i]
                        [(Term.typeSpec ":" (Term.app `Fin [(num "2")]))]
                        "=>"
                        (Term.app
                         `tendsto.pi_map_Coprod
                         [(Term.fun
                           "fun"
                           (Term.basicFun
                            [`j]
                            [(Term.typeSpec ":" (Term.app `Fin [(num "2")]))]
                            "=>"
                            `Int.tendsto_coe_cofinite))])))])]))]))))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`hf₁ []]
             [(Term.typeSpec
               ":"
               (Term.app `tendsto [`f₁ `cofinite (Term.app `cocompact [(Term.hole "_")])]))]
             ":="
             (Term.app
              `cocompact_ℝ_to_cofinite_ℤ_matrix.comp
              [`subtype.coe_injective.tendsto_cofinite]))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`hf₂ []]
             [(Term.typeSpec ":" (Term.app `ClosedEmbedding [(Term.app `lc_row0_extend [`hcd])]))]
             ":="
             (Term.proj
              (Term.proj
               (Term.proj (Term.app `lc_row0_extend [`hcd]) "." `toContinuousLinearEquiv)
               "."
               `toHomeomorph)
              "."
              `ClosedEmbedding))))
          []
          (convert
           "convert"
           []
           (Term.app
            `hf₂.tendsto_cocompact.comp
            [(Term.app `hf₁.comp [`subtype.coe_injective.tendsto_cofinite])])
           ["using" (num "1")])
          []
          (Std.Tactic.Ext.«tacticExt___:_»
           "ext"
           [(Std.Tactic.RCases.rintroPat.binder
             "("
             [(Std.Tactic.RCases.rintroPat.one
               (Std.Tactic.RCases.rcasesPat.tuple
                "⟨"
                [(Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `g)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                  [])]
                "⟩"))
              (Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `i))
              (Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `j))]
             []
             ")")]
           [":" (num "3")])
          []
          (Std.Tactic.seq_focus
           (Lean.Elab.Tactic.finCases "fin_cases" [`i] [])
           "<;>"
           "["
           [(Lean.Elab.Tactic.finCases "fin_cases" [`j] []) "," (Tactic.skip "skip")]
           "]")
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.simp
             "simp"
             []
             []
             ["only"]
             ["["
              [(Tactic.simpLemma [] [] `mB)
               ","
               (Tactic.simpLemma [] [] `mul_vec)
               ","
               (Tactic.simpLemma [] [] `dot_product)
               ","
               (Tactic.simpLemma [] [] `Fin.sum_univ_two)
               ","
               (Tactic.simpLemma [] [] `_root_.coe_coe)
               ","
               (Tactic.simpLemma [] [] `coe_matrix_coe)
               ","
               (Tactic.simpLemma [] [] `Int.coe_castRingHom)
               ","
               (Tactic.simpLemma [] [] `lc_row0_apply)
               ","
               (Tactic.simpLemma [] [] `Function.comp_apply)
               ","
               (Tactic.simpLemma [] [] `cons_val_zero)
               ","
               (Tactic.simpLemma [] [] `lc_row0_extend_apply)
               ","
               (Tactic.simpLemma [] [] `LinearMap.GeneralLinearGroup.coe_fn_general_linear_equiv)
               ","
               (Tactic.simpLemma [] [] `general_linear_group.to_linear_apply)
               ","
               (Tactic.simpLemma [] [] `coe_plane_conformal_matrix)
               ","
               (Tactic.simpLemma [] [] `neg_neg)
               ","
               (Tactic.simpLemma [] [] `mul_vec_lin_apply)
               ","
               (Tactic.simpLemma [] [] `cons_val_one)
               ","
               (Tactic.simpLemma [] [] `head_cons)
               ","
               (Tactic.simpLemma [] [] `of_apply)]
              "]"]
             [])])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(convert
             "convert"
             []
             (Term.app
              `congr_arg
              [(Term.fun
                "fun"
                (Term.basicFun
                 [`n]
                 [(Term.typeSpec ":" (termℤ "ℤ"))]
                 "=>"
                 (Term.typeAscription "(" («term-_» "-" `n) ":" [(Data.Real.Basic.termℝ "ℝ")] ")")))
               `g.det_coe.symm])
             ["using" (num "1")])
            []
            (Tactic.simp
             "simp"
             []
             []
             ["only"]
             ["["
              [(Tactic.simpLemma [] [] `f₁)
               ","
               (Tactic.simpLemma [] [] `mul_vec)
               ","
               (Tactic.simpLemma [] [] `dot_product)
               ","
               (Tactic.simpLemma [] [] `Fin.sum_univ_two)
               ","
               (Tactic.simpLemma [] [] `Matrix.det_fin_two)
               ","
               (Tactic.simpLemma [] [] `Function.comp_apply)
               ","
               (Tactic.simpLemma [] [] `Subtype.coe_mk)
               ","
               (Tactic.simpLemma [] [] `lc_row0_extend_apply)
               ","
               (Tactic.simpLemma [] [] `cons_val_zero)
               ","
               (Tactic.simpLemma [] [] `LinearMap.GeneralLinearGroup.coe_fn_general_linear_equiv)
               ","
               (Tactic.simpLemma [] [] `general_linear_group.to_linear_apply)
               ","
               (Tactic.simpLemma [] [] `coe_plane_conformal_matrix)
               ","
               (Tactic.simpLemma [] [] `mul_vec_lin_apply)
               ","
               (Tactic.simpLemma [] [] `cons_val_one)
               ","
               (Tactic.simpLemma [] [] `head_cons)
               ","
               (Tactic.simpLemma [] [] `map_apply)
               ","
               (Tactic.simpLemma [] [] `neg_mul)
               ","
               (Tactic.simpLemma [] [] `Int.cast_sub)
               ","
               (Tactic.simpLemma [] [] `Int.cast_mul)
               ","
               (Tactic.simpLemma [] [] `neg_sub)
               ","
               (Tactic.simpLemma [] [] `of_apply)]
              "]"]
             [])
            []
            (Mathlib.Tactic.RingNF.ring "ring")])
          []
          (tactic__ (cdotTk (patternIgnore (token.«· » "·"))) [(Tactic.tacticRfl "rfl")])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__ (cdotTk (patternIgnore (token.«· » "·"))) [(Tactic.tacticRfl "rfl")])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticRfl "rfl")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(convert
         "convert"
         []
         (Term.app
          `congr_arg
          [(Term.fun
            "fun"
            (Term.basicFun
             [`n]
             [(Term.typeSpec ":" (termℤ "ℤ"))]
             "=>"
             (Term.typeAscription "(" («term-_» "-" `n) ":" [(Data.Real.Basic.termℝ "ℝ")] ")")))
           `g.det_coe.symm])
         ["using" (num "1")])
        []
        (Tactic.simp
         "simp"
         []
         []
         ["only"]
         ["["
          [(Tactic.simpLemma [] [] `f₁)
           ","
           (Tactic.simpLemma [] [] `mul_vec)
           ","
           (Tactic.simpLemma [] [] `dot_product)
           ","
           (Tactic.simpLemma [] [] `Fin.sum_univ_two)
           ","
           (Tactic.simpLemma [] [] `Matrix.det_fin_two)
           ","
           (Tactic.simpLemma [] [] `Function.comp_apply)
           ","
           (Tactic.simpLemma [] [] `Subtype.coe_mk)
           ","
           (Tactic.simpLemma [] [] `lc_row0_extend_apply)
           ","
           (Tactic.simpLemma [] [] `cons_val_zero)
           ","
           (Tactic.simpLemma [] [] `LinearMap.GeneralLinearGroup.coe_fn_general_linear_equiv)
           ","
           (Tactic.simpLemma [] [] `general_linear_group.to_linear_apply)
           ","
           (Tactic.simpLemma [] [] `coe_plane_conformal_matrix)
           ","
           (Tactic.simpLemma [] [] `mul_vec_lin_apply)
           ","
           (Tactic.simpLemma [] [] `cons_val_one)
           ","
           (Tactic.simpLemma [] [] `head_cons)
           ","
           (Tactic.simpLemma [] [] `map_apply)
           ","
           (Tactic.simpLemma [] [] `neg_mul)
           ","
           (Tactic.simpLemma [] [] `Int.cast_sub)
           ","
           (Tactic.simpLemma [] [] `Int.cast_mul)
           ","
           (Tactic.simpLemma [] [] `neg_sub)
           ","
           (Tactic.simpLemma [] [] `of_apply)]
          "]"]
         [])
        []
        (Mathlib.Tactic.RingNF.ring "ring")])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.RingNF.ring "ring")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["["
        [(Tactic.simpLemma [] [] `f₁)
         ","
         (Tactic.simpLemma [] [] `mul_vec)
         ","
         (Tactic.simpLemma [] [] `dot_product)
         ","
         (Tactic.simpLemma [] [] `Fin.sum_univ_two)
         ","
         (Tactic.simpLemma [] [] `Matrix.det_fin_two)
         ","
         (Tactic.simpLemma [] [] `Function.comp_apply)
         ","
         (Tactic.simpLemma [] [] `Subtype.coe_mk)
         ","
         (Tactic.simpLemma [] [] `lc_row0_extend_apply)
         ","
         (Tactic.simpLemma [] [] `cons_val_zero)
         ","
         (Tactic.simpLemma [] [] `LinearMap.GeneralLinearGroup.coe_fn_general_linear_equiv)
         ","
         (Tactic.simpLemma [] [] `general_linear_group.to_linear_apply)
         ","
         (Tactic.simpLemma [] [] `coe_plane_conformal_matrix)
         ","
         (Tactic.simpLemma [] [] `mul_vec_lin_apply)
         ","
         (Tactic.simpLemma [] [] `cons_val_one)
         ","
         (Tactic.simpLemma [] [] `head_cons)
         ","
         (Tactic.simpLemma [] [] `map_apply)
         ","
         (Tactic.simpLemma [] [] `neg_mul)
         ","
         (Tactic.simpLemma [] [] `Int.cast_sub)
         ","
         (Tactic.simpLemma [] [] `Int.cast_mul)
         ","
         (Tactic.simpLemma [] [] `neg_sub)
         ","
         (Tactic.simpLemma [] [] `of_apply)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `of_apply
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `neg_sub
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Int.cast_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Int.cast_sub
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `neg_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `map_apply
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `head_cons
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `cons_val_one
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_vec_lin_apply
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `coe_plane_conformal_matrix
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `general_linear_group.to_linear_apply
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `LinearMap.GeneralLinearGroup.coe_fn_general_linear_equiv
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `cons_val_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `lc_row0_extend_apply
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Subtype.coe_mk
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Function.comp_apply
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Matrix.det_fin_two
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Fin.sum_univ_two
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `dot_product
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_vec
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f₁
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (convert
       "convert"
       []
       (Term.app
        `congr_arg
        [(Term.fun
          "fun"
          (Term.basicFun
           [`n]
           [(Term.typeSpec ":" (termℤ "ℤ"))]
           "=>"
           (Term.typeAscription "(" («term-_» "-" `n) ":" [(Data.Real.Basic.termℝ "ℝ")] ")")))
         `g.det_coe.symm])
       ["using" (num "1")])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `congr_arg
       [(Term.fun
         "fun"
         (Term.basicFun
          [`n]
          [(Term.typeSpec ":" (termℤ "ℤ"))]
          "=>"
          (Term.typeAscription "(" («term-_» "-" `n) ":" [(Data.Real.Basic.termℝ "ℝ")] ")")))
        `g.det_coe.symm])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g.det_coe.symm
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.fun
       "fun"
       (Term.basicFun
        [`n]
        [(Term.typeSpec ":" (termℤ "ℤ"))]
        "=>"
        (Term.typeAscription "(" («term-_» "-" `n) ":" [(Data.Real.Basic.termℝ "ℝ")] ")")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription "(" («term-_» "-" `n) ":" [(Data.Real.Basic.termℝ "ℝ")] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Real.Basic.termℝ "ℝ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term-_» "-" `n)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 75 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 75, (some 75, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (termℤ "ℤ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.fun
      "fun"
      (Term.basicFun
       [`n]
       [(Term.typeSpec ":" (termℤ "ℤ"))]
       "=>"
       (Term.typeAscription "(" («term-_» "-" `n) ":" [(Data.Real.Basic.termℝ "ℝ")] ")")))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `congr_arg
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
         ["only"]
         ["["
          [(Tactic.simpLemma [] [] `mB)
           ","
           (Tactic.simpLemma [] [] `mul_vec)
           ","
           (Tactic.simpLemma [] [] `dot_product)
           ","
           (Tactic.simpLemma [] [] `Fin.sum_univ_two)
           ","
           (Tactic.simpLemma [] [] `_root_.coe_coe)
           ","
           (Tactic.simpLemma [] [] `coe_matrix_coe)
           ","
           (Tactic.simpLemma [] [] `Int.coe_castRingHom)
           ","
           (Tactic.simpLemma [] [] `lc_row0_apply)
           ","
           (Tactic.simpLemma [] [] `Function.comp_apply)
           ","
           (Tactic.simpLemma [] [] `cons_val_zero)
           ","
           (Tactic.simpLemma [] [] `lc_row0_extend_apply)
           ","
           (Tactic.simpLemma [] [] `LinearMap.GeneralLinearGroup.coe_fn_general_linear_equiv)
           ","
           (Tactic.simpLemma [] [] `general_linear_group.to_linear_apply)
           ","
           (Tactic.simpLemma [] [] `coe_plane_conformal_matrix)
           ","
           (Tactic.simpLemma [] [] `neg_neg)
           ","
           (Tactic.simpLemma [] [] `mul_vec_lin_apply)
           ","
           (Tactic.simpLemma [] [] `cons_val_one)
           ","
           (Tactic.simpLemma [] [] `head_cons)
           ","
           (Tactic.simpLemma [] [] `of_apply)]
          "]"]
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["["
        [(Tactic.simpLemma [] [] `mB)
         ","
         (Tactic.simpLemma [] [] `mul_vec)
         ","
         (Tactic.simpLemma [] [] `dot_product)
         ","
         (Tactic.simpLemma [] [] `Fin.sum_univ_two)
         ","
         (Tactic.simpLemma [] [] `_root_.coe_coe)
         ","
         (Tactic.simpLemma [] [] `coe_matrix_coe)
         ","
         (Tactic.simpLemma [] [] `Int.coe_castRingHom)
         ","
         (Tactic.simpLemma [] [] `lc_row0_apply)
         ","
         (Tactic.simpLemma [] [] `Function.comp_apply)
         ","
         (Tactic.simpLemma [] [] `cons_val_zero)
         ","
         (Tactic.simpLemma [] [] `lc_row0_extend_apply)
         ","
         (Tactic.simpLemma [] [] `LinearMap.GeneralLinearGroup.coe_fn_general_linear_equiv)
         ","
         (Tactic.simpLemma [] [] `general_linear_group.to_linear_apply)
         ","
         (Tactic.simpLemma [] [] `coe_plane_conformal_matrix)
         ","
         (Tactic.simpLemma [] [] `neg_neg)
         ","
         (Tactic.simpLemma [] [] `mul_vec_lin_apply)
         ","
         (Tactic.simpLemma [] [] `cons_val_one)
         ","
         (Tactic.simpLemma [] [] `head_cons)
         ","
         (Tactic.simpLemma [] [] `of_apply)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `of_apply
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `head_cons
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `cons_val_one
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_vec_lin_apply
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `neg_neg
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `coe_plane_conformal_matrix
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `general_linear_group.to_linear_apply
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `LinearMap.GeneralLinearGroup.coe_fn_general_linear_equiv
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `lc_row0_extend_apply
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `cons_val_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Function.comp_apply
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `lc_row0_apply
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Int.coe_castRingHom
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `coe_matrix_coe
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `_root_.coe_coe
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Fin.sum_univ_two
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `dot_product
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_vec
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mB
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.seq_focus
       (Lean.Elab.Tactic.finCases "fin_cases" [`i] [])
       "<;>"
       "["
       [(Lean.Elab.Tactic.finCases "fin_cases" [`j] []) "," (Tactic.skip "skip")]
       "]")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.skip "skip")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Lean.Elab.Tactic.finCases "fin_cases" [`j] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'token.«*»'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `j
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
      (Lean.Elab.Tactic.finCases "fin_cases" [`i] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'token.«*»'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Ext.«tacticExt___:_»
       "ext"
       [(Std.Tactic.RCases.rintroPat.binder
         "("
         [(Std.Tactic.RCases.rintroPat.one
           (Std.Tactic.RCases.rcasesPat.tuple
            "⟨"
            [(Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `g)])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
              [])]
            "⟩"))
          (Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `i))
          (Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `j))]
         []
         ")")]
       [":" (num "3")])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (convert
       "convert"
       []
       (Term.app
        `hf₂.tendsto_cocompact.comp
        [(Term.app `hf₁.comp [`subtype.coe_injective.tendsto_cofinite])])
       ["using" (num "1")])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `hf₂.tendsto_cocompact.comp
       [(Term.app `hf₁.comp [`subtype.coe_injective.tendsto_cofinite])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `hf₁.comp [`subtype.coe_injective.tendsto_cofinite])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `subtype.coe_injective.tendsto_cofinite
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `hf₁.comp
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `hf₁.comp [`subtype.coe_injective.tendsto_cofinite])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `hf₂.tendsto_cocompact.comp
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`hf₂ []]
         [(Term.typeSpec ":" (Term.app `ClosedEmbedding [(Term.app `lc_row0_extend [`hcd])]))]
         ":="
         (Term.proj
          (Term.proj
           (Term.proj (Term.app `lc_row0_extend [`hcd]) "." `toContinuousLinearEquiv)
           "."
           `toHomeomorph)
          "."
          `ClosedEmbedding))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj
       (Term.proj
        (Term.proj (Term.app `lc_row0_extend [`hcd]) "." `toContinuousLinearEquiv)
        "."
        `toHomeomorph)
       "."
       `ClosedEmbedding)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj
       (Term.proj (Term.app `lc_row0_extend [`hcd]) "." `toContinuousLinearEquiv)
       "."
       `toHomeomorph)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj (Term.app `lc_row0_extend [`hcd]) "." `toContinuousLinearEquiv)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `lc_row0_extend [`hcd])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hcd
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `lc_row0_extend
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `lc_row0_extend [`hcd]) ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `ClosedEmbedding [(Term.app `lc_row0_extend [`hcd])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `lc_row0_extend [`hcd])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hcd
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `lc_row0_extend
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `lc_row0_extend [`hcd]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `ClosedEmbedding
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`hf₁ []]
         [(Term.typeSpec
           ":"
           (Term.app `tendsto [`f₁ `cofinite (Term.app `cocompact [(Term.hole "_")])]))]
         ":="
         (Term.app
          `cocompact_ℝ_to_cofinite_ℤ_matrix.comp
          [`subtype.coe_injective.tendsto_cofinite]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `cocompact_ℝ_to_cofinite_ℤ_matrix.comp [`subtype.coe_injective.tendsto_cofinite])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `subtype.coe_injective.tendsto_cofinite
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `cocompact_ℝ_to_cofinite_ℤ_matrix.comp
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `tendsto [`f₁ `cofinite (Term.app `cocompact [(Term.hole "_")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `cocompact [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `cocompact
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `cocompact [(Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `cofinite
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `tendsto
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`cocompact_ℝ_to_cofinite_ℤ_matrix []]
         [(Term.typeSpec
           ":"
           (Term.app
            `tendsto
            [(Term.fun
              "fun"
              (Term.basicFun
               [`m]
               [(Term.typeSpec
                 ":"
                 (Term.app
                  `Matrix
                  [(Term.app `Fin [(num "2")]) (Term.app `Fin [(num "2")]) (termℤ "ℤ")]))]
               "=>"
               (Term.app
                `Matrix.map
                [`m
                 (Term.typeAscription
                  "("
                  `coe
                  ":"
                  [(Term.arrow (termℤ "ℤ") "→" (Data.Real.Basic.termℝ "ℝ"))]
                  ")")])))
             `cofinite
             (Term.app `cocompact [(Term.hole "_")])]))]
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
               ["only"]
               [(Tactic.simpArgs
                 "["
                 [(Tactic.simpLemma [] [] `Coprod_cofinite)
                  ","
                  (Tactic.simpLemma [] [] `Coprod_cocompact)]
                 "]")]
               ["using"
                (Term.app
                 `tendsto.pi_map_Coprod
                 [(Term.fun
                   "fun"
                   (Term.basicFun
                    [`i]
                    [(Term.typeSpec ":" (Term.app `Fin [(num "2")]))]
                    "=>"
                    (Term.app
                     `tendsto.pi_map_Coprod
                     [(Term.fun
                       "fun"
                       (Term.basicFun
                        [`j]
                        [(Term.typeSpec ":" (Term.app `Fin [(num "2")]))]
                        "=>"
                        `Int.tendsto_coe_cofinite))])))])]))]))))))
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
            ["only"]
            [(Tactic.simpArgs
              "["
              [(Tactic.simpLemma [] [] `Coprod_cofinite)
               ","
               (Tactic.simpLemma [] [] `Coprod_cocompact)]
              "]")]
            ["using"
             (Term.app
              `tendsto.pi_map_Coprod
              [(Term.fun
                "fun"
                (Term.basicFun
                 [`i]
                 [(Term.typeSpec ":" (Term.app `Fin [(num "2")]))]
                 "=>"
                 (Term.app
                  `tendsto.pi_map_Coprod
                  [(Term.fun
                    "fun"
                    (Term.basicFun
                     [`j]
                     [(Term.typeSpec ":" (Term.app `Fin [(num "2")]))]
                     "=>"
                     `Int.tendsto_coe_cofinite))])))])]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Simpa.simpa
       "simpa"
       []
       []
       (Std.Tactic.Simpa.simpaArgsRest
        []
        []
        ["only"]
        [(Tactic.simpArgs
          "["
          [(Tactic.simpLemma [] [] `Coprod_cofinite) "," (Tactic.simpLemma [] [] `Coprod_cocompact)]
          "]")]
        ["using"
         (Term.app
          `tendsto.pi_map_Coprod
          [(Term.fun
            "fun"
            (Term.basicFun
             [`i]
             [(Term.typeSpec ":" (Term.app `Fin [(num "2")]))]
             "=>"
             (Term.app
              `tendsto.pi_map_Coprod
              [(Term.fun
                "fun"
                (Term.basicFun
                 [`j]
                 [(Term.typeSpec ":" (Term.app `Fin [(num "2")]))]
                 "=>"
                 `Int.tendsto_coe_cofinite))])))])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `tendsto.pi_map_Coprod
       [(Term.fun
         "fun"
         (Term.basicFun
          [`i]
          [(Term.typeSpec ":" (Term.app `Fin [(num "2")]))]
          "=>"
          (Term.app
           `tendsto.pi_map_Coprod
           [(Term.fun
             "fun"
             (Term.basicFun
              [`j]
              [(Term.typeSpec ":" (Term.app `Fin [(num "2")]))]
              "=>"
              `Int.tendsto_coe_cofinite))])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`i]
        [(Term.typeSpec ":" (Term.app `Fin [(num "2")]))]
        "=>"
        (Term.app
         `tendsto.pi_map_Coprod
         [(Term.fun
           "fun"
           (Term.basicFun
            [`j]
            [(Term.typeSpec ":" (Term.app `Fin [(num "2")]))]
            "=>"
            `Int.tendsto_coe_cofinite))])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `tendsto.pi_map_Coprod
       [(Term.fun
         "fun"
         (Term.basicFun
          [`j]
          [(Term.typeSpec ":" (Term.app `Fin [(num "2")]))]
          "=>"
          `Int.tendsto_coe_cofinite))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`j]
        [(Term.typeSpec ":" (Term.app `Fin [(num "2")]))]
        "=>"
        `Int.tendsto_coe_cofinite))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Int.tendsto_coe_cofinite
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Fin [(num "2")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Fin
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      `j
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `tendsto.pi_map_Coprod
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Fin [(num "2")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Fin
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `tendsto.pi_map_Coprod
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Coprod_cocompact
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Coprod_cofinite
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `tendsto
       [(Term.fun
         "fun"
         (Term.basicFun
          [`m]
          [(Term.typeSpec
            ":"
            (Term.app
             `Matrix
             [(Term.app `Fin [(num "2")]) (Term.app `Fin [(num "2")]) (termℤ "ℤ")]))]
          "=>"
          (Term.app
           `Matrix.map
           [`m
            (Term.typeAscription
             "("
             `coe
             ":"
             [(Term.arrow (termℤ "ℤ") "→" (Data.Real.Basic.termℝ "ℝ"))]
             ")")])))
        `cofinite
        (Term.app `cocompact [(Term.hole "_")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `cocompact [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `cocompact
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `cocompact [(Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `cofinite
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.fun
       "fun"
       (Term.basicFun
        [`m]
        [(Term.typeSpec
          ":"
          (Term.app `Matrix [(Term.app `Fin [(num "2")]) (Term.app `Fin [(num "2")]) (termℤ "ℤ")]))]
        "=>"
        (Term.app
         `Matrix.map
         [`m
          (Term.typeAscription
           "("
           `coe
           ":"
           [(Term.arrow (termℤ "ℤ") "→" (Data.Real.Basic.termℝ "ℝ"))]
           ")")])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Matrix.map
       [`m
        (Term.typeAscription
         "("
         `coe
         ":"
         [(Term.arrow (termℤ "ℤ") "→" (Data.Real.Basic.termℝ "ℝ"))]
         ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription
       "("
       `coe
       ":"
       [(Term.arrow (termℤ "ℤ") "→" (Data.Real.Basic.termℝ "ℝ"))]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.arrow (termℤ "ℤ") "→" (Data.Real.Basic.termℝ "ℝ"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Real.Basic.termℝ "ℝ")
[PrettyPrinter.parenthesize] ...precedences are 25 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
      (termℤ "ℤ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 25, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 25, (some 25, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `coe
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      `m
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Matrix.map
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Matrix [(Term.app `Fin [(num "2")]) (Term.app `Fin [(num "2")]) (termℤ "ℤ")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'termℤ', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'termℤ', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (termℤ "ℤ")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.app `Fin [(num "2")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Fin
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `Fin [(num "2")]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `Fin [(num "2")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Fin
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `Fin [(num "2")]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Matrix
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      `m
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.fun
      "fun"
      (Term.basicFun
       [`m]
       [(Term.typeSpec
         ":"
         (Term.app
          `Matrix
          [(Term.paren "(" (Term.app `Fin [(num "2")]) ")")
           (Term.paren "(" (Term.app `Fin [(num "2")]) ")")
           (termℤ "ℤ")]))]
       "=>"
       (Term.app
        `Matrix.map
        [`m
         (Term.typeAscription
          "("
          `coe
          ":"
          [(Term.arrow (termℤ "ℤ") "→" (Data.Real.Basic.termℝ "ℝ"))]
          ")")])))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `tendsto
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticLet_
       "let"
       (Term.letDecl
        (Term.letIdDecl
         `f₁
         []
         [(Term.typeSpec
           ":"
           (Term.arrow
            (NumberTheory.Modular.«termSL(_,_)» "SL(" (num "2") ", " (termℤ "ℤ") ")")
            "→"
            (Term.app
             `Matrix
             [(Term.app `Fin [(num "2")])
              (Term.app `Fin [(num "2")])
              (Data.Real.Basic.termℝ "ℝ")])))]
         ":="
         (Term.fun
          "fun"
          (Term.basicFun
           [`g]
           []
           "=>"
           (Term.app
            `Matrix.map
            [(Term.typeAscription
              "("
              (coeNotation "↑" `g)
              ":"
              [(Term.app `Matrix [(Term.hole "_") (Term.hole "_") (termℤ "ℤ")])]
              ")")
             (Term.typeAscription
              "("
              `coe
              ":"
              [(Term.arrow (termℤ "ℤ") "→" (Data.Real.Basic.termℝ "ℝ"))]
              ")")]))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`g]
        []
        "=>"
        (Term.app
         `Matrix.map
         [(Term.typeAscription
           "("
           (coeNotation "↑" `g)
           ":"
           [(Term.app `Matrix [(Term.hole "_") (Term.hole "_") (termℤ "ℤ")])]
           ")")
          (Term.typeAscription
           "("
           `coe
           ":"
           [(Term.arrow (termℤ "ℤ") "→" (Data.Real.Basic.termℝ "ℝ"))]
           ")")])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Matrix.map
       [(Term.typeAscription
         "("
         (coeNotation "↑" `g)
         ":"
         [(Term.app `Matrix [(Term.hole "_") (Term.hole "_") (termℤ "ℤ")])]
         ")")
        (Term.typeAscription
         "("
         `coe
         ":"
         [(Term.arrow (termℤ "ℤ") "→" (Data.Real.Basic.termℝ "ℝ"))]
         ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription
       "("
       `coe
       ":"
       [(Term.arrow (termℤ "ℤ") "→" (Data.Real.Basic.termℝ "ℝ"))]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.arrow (termℤ "ℤ") "→" (Data.Real.Basic.termℝ "ℝ"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Real.Basic.termℝ "ℝ")
[PrettyPrinter.parenthesize] ...precedences are 25 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
      (termℤ "ℤ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 25, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 25, (some 25, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `coe
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.typeAscription
       "("
       (coeNotation "↑" `g)
       ":"
       [(Term.app `Matrix [(Term.hole "_") (Term.hole "_") (termℤ "ℤ")])]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Matrix [(Term.hole "_") (Term.hole "_") (termℤ "ℤ")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'termℤ', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'termℤ', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (termℤ "ℤ")
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
      `Matrix
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (coeNotation "↑" `g)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 1024, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Matrix.map
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.arrow
       (NumberTheory.Modular.«termSL(_,_)» "SL(" (num "2") ", " (termℤ "ℤ") ")")
       "→"
       (Term.app
        `Matrix
        [(Term.app `Fin [(num "2")]) (Term.app `Fin [(num "2")]) (Data.Real.Basic.termℝ "ℝ")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Matrix
       [(Term.app `Fin [(num "2")]) (Term.app `Fin [(num "2")]) (Data.Real.Basic.termℝ "ℝ")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Basic.termℝ', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Basic.termℝ', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Real.Basic.termℝ "ℝ")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.app `Fin [(num "2")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Fin
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `Fin [(num "2")]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `Fin [(num "2")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Fin
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `Fin [(num "2")]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Matrix
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 25 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
      (NumberTheory.Modular.«termSL(_,_)» "SL(" (num "2") ", " (termℤ "ℤ") ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.Modular.«termSL(_,_)»', expected 'NumberTheory.Modular.termSL(_,_)._@.NumberTheory.Modular._hyg.8'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letIdDecl', expected 'Lean.Parser.Term.letPatDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letIdDecl', expected 'Lean.Parser.Term.letEqnsDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    The map `lc_row0` is proper, that is, preimages of cocompact sets are finite in
    `[[* , *], [c, d]]`.-/
  theorem
    tendsto_lc_row0
    { cd : Fin 2 → ℤ } ( hcd : IsCoprime cd 0 cd 1 )
      :
        Tendsto
          fun g : { g : SL( 2 , ℤ ) // ↑ₘ g 1 = cd } => lcRow0 cd ↑ ( ↑ g : SL( 2 , ℝ ) )
            cofinite
            cocompact ℝ
    :=
      by
        let
            mB
              : ℝ → Matrix Fin 2 Fin 2 ℝ
              :=
              fun t => of ![ ![ t , ( - ( 1 : ℤ ) : ℝ ) ] , coe ∘ cd ]
          have
            hmB
              : Continuous mB
              :=
              by
                refine' continuous_matrix _
                  simp
                    only
                    [
                      Fin.forall_fin_two
                        ,
                        mB
                        ,
                        continuous_const
                        ,
                        continuous_id'
                        ,
                        of_apply
                        ,
                        cons_val_zero
                        ,
                        cons_val_one
                        ,
                        and_self_iff
                      ]
          refine' Filter.Tendsto.of_tendsto_comp _ comap_cocompact_le hmB
          let
            f₁
              : SL( 2 , ℤ ) → Matrix Fin 2 Fin 2 ℝ
              :=
              fun g => Matrix.map ( ↑ g : Matrix _ _ ℤ ) ( coe : ℤ → ℝ )
          have
            cocompact_ℝ_to_cofinite_ℤ_matrix
              :
                tendsto
                  fun m : Matrix Fin 2 Fin 2 ℤ => Matrix.map m ( coe : ℤ → ℝ ) cofinite cocompact _
              :=
              by
                simpa
                  only
                    [ Coprod_cofinite , Coprod_cocompact ]
                    using
                      tendsto.pi_map_Coprod
                        fun
                          i
                            : Fin 2
                            =>
                            tendsto.pi_map_Coprod fun j : Fin 2 => Int.tendsto_coe_cofinite
          have
            hf₁
              : tendsto f₁ cofinite cocompact _
              :=
              cocompact_ℝ_to_cofinite_ℤ_matrix.comp subtype.coe_injective.tendsto_cofinite
          have
            hf₂
              : ClosedEmbedding lc_row0_extend hcd
              :=
              lc_row0_extend hcd . toContinuousLinearEquiv . toHomeomorph . ClosedEmbedding
          convert hf₂.tendsto_cocompact.comp hf₁.comp subtype.coe_injective.tendsto_cofinite using 1
          ext ( ⟨ g , rfl ⟩ i j ) : 3
          fin_cases i <;> [ fin_cases j , skip ]
          ·
            simp
              only
              [
                mB
                  ,
                  mul_vec
                  ,
                  dot_product
                  ,
                  Fin.sum_univ_two
                  ,
                  _root_.coe_coe
                  ,
                  coe_matrix_coe
                  ,
                  Int.coe_castRingHom
                  ,
                  lc_row0_apply
                  ,
                  Function.comp_apply
                  ,
                  cons_val_zero
                  ,
                  lc_row0_extend_apply
                  ,
                  LinearMap.GeneralLinearGroup.coe_fn_general_linear_equiv
                  ,
                  general_linear_group.to_linear_apply
                  ,
                  coe_plane_conformal_matrix
                  ,
                  neg_neg
                  ,
                  mul_vec_lin_apply
                  ,
                  cons_val_one
                  ,
                  head_cons
                  ,
                  of_apply
                ]
          ·
            convert congr_arg fun n : ℤ => ( - n : ℝ ) g.det_coe.symm using 1
              simp
                only
                [
                  f₁
                    ,
                    mul_vec
                    ,
                    dot_product
                    ,
                    Fin.sum_univ_two
                    ,
                    Matrix.det_fin_two
                    ,
                    Function.comp_apply
                    ,
                    Subtype.coe_mk
                    ,
                    lc_row0_extend_apply
                    ,
                    cons_val_zero
                    ,
                    LinearMap.GeneralLinearGroup.coe_fn_general_linear_equiv
                    ,
                    general_linear_group.to_linear_apply
                    ,
                    coe_plane_conformal_matrix
                    ,
                    mul_vec_lin_apply
                    ,
                    cons_val_one
                    ,
                    head_cons
                    ,
                    map_apply
                    ,
                    neg_mul
                    ,
                    Int.cast_sub
                    ,
                    Int.cast_mul
                    ,
                    neg_sub
                    ,
                    of_apply
                  ]
              ring
          · rfl
#align modular_group.tendsto_lc_row0 ModularGroup.tendsto_lc_row0

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "This replaces `(g•z).re = a/c + *` in the standard theory with the following novel identity:\n  `g • z = (a c + b d) / (c^2 + d^2) + (d z - c) / ((c^2 + d^2) (c z + d))`\n  which does not need to be decomposed depending on whether `c = 0`. -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `smul_eq_lc_row0_add [])
      (Command.declSig
       [(Term.implicitBinder
         "{"
         [`p]
         [":" (Term.arrow (Term.app `Fin [(num "2")]) "→" (termℤ "ℤ"))]
         "}")
        (Term.explicitBinder
         "("
         [`hp]
         [":" (Term.app `IsCoprime [(Term.app `p [(num "0")]) (Term.app `p [(num "1")])])]
         []
         ")")
        (Term.explicitBinder
         "("
         [`hg]
         [":" («term_=_» (Term.app (NumberTheory.Modular.«term↑ₘ_» "↑ₘ" `g) [(num "1")]) "=" `p)]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (coeNotation "↑" (Algebra.Group.Defs.«term_•_» `g " • " `z))
         "="
         («term_+_»
          («term_/_»
           (Term.typeAscription
            "("
            (Term.app
             `lcRow0
             [`p
              (coeNotation
               "↑"
               (Term.typeAscription
                "("
                `g
                ":"
                [(NumberTheory.Modular.«termSL(_,_)»
                  "SL("
                  (num "2")
                  ", "
                  (Data.Real.Basic.termℝ "ℝ")
                  ")")]
                ")"))])
            ":"
            [(Data.Complex.Basic.termℂ "ℂ")]
            ")")
           "/"
           («term_+_»
            («term_^_» (Term.app `p [(num "0")]) "^" (num "2"))
            "+"
            («term_^_» (Term.app `p [(num "1")]) "^" (num "2"))))
          "+"
          («term_/_»
           («term_-_»
            («term_*_»
             (Term.typeAscription
              "("
              (Term.app `p [(num "1")])
              ":"
              [(Data.Complex.Basic.termℂ "ℂ")]
              ")")
             "*"
             `z)
            "-"
            (Term.app `p [(num "0")]))
           "/"
           («term_*_»
            («term_+_»
             («term_^_» (Term.app `p [(num "0")]) "^" (num "2"))
             "+"
             («term_^_» (Term.app `p [(num "1")]) "^" (num "2")))
            "*"
            («term_+_»
             («term_*_» (Term.app `p [(num "0")]) "*" `z)
             "+"
             (Term.app `p [(num "1")]))))))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`nonZ1 []]
              [(Term.typeSpec
                ":"
                («term_≠_»
                 («term_+_»
                  («term_^_»
                   (Term.typeAscription
                    "("
                    (Term.app `p [(num "0")])
                    ":"
                    [(Data.Complex.Basic.termℂ "ℂ")]
                    ")")
                   "^"
                   (num "2"))
                  "+"
                  («term_^_» (Term.app `p [(num "1")]) "^" (num "2")))
                 "≠"
                 (num "0")))]
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Tactic.NormCast.tacticExact_mod_cast_
                   "exact_mod_cast"
                   `hp.sq_add_sq_ne_zero)]))))))
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              []
              [(Term.typeSpec
                ":"
                («term_≠_»
                 («term_∘_»
                  (Term.typeAscription
                   "("
                   `coe
                   ":"
                   [(Term.arrow (termℤ "ℤ") "→" (Data.Real.Basic.termℝ "ℝ"))]
                   ")")
                  "∘"
                  `p)
                 "≠"
                 (num "0")))]
              ":="
              (Term.fun
               "fun"
               (Term.basicFun
                [`h]
                []
                "=>"
                (Term.app
                 `hp.ne_zero
                 [(Term.byTactic
                   "by"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented
                     [(Tactic.«tactic_<;>_»
                       (Std.Tactic.Ext.«tacticExt___:_»
                        "ext"
                        [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `i))]
                        [])
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
                         ["using" (Term.app `congr_fun [`h `i])])))])))]))))))
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`nonZ2 []]
              [(Term.typeSpec
                ":"
                («term_≠_»
                 («term_+_»
                  («term_*_»
                   (Term.typeAscription
                    "("
                    (Term.app `p [(num "0")])
                    ":"
                    [(Data.Complex.Basic.termℂ "ℂ")]
                    ")")
                   "*"
                   `z)
                  "+"
                  (Term.app `p [(num "1")]))
                 "≠"
                 (num "0")))]
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
                    []
                    ["using" (Term.app `linear_ne_zero [(Term.hole "_") `z `this])]))]))))))
           []
           (Tactic.fieldSimp
            "field_simp"
            []
            []
            []
            [(Tactic.simpArgs
              "["
              [(Tactic.simpLemma [] [] `nonZ1)
               ","
               (Tactic.simpLemma [] [] `nonZ2)
               ","
               (Tactic.simpLemma [] [] `denom_ne_zero)
               ","
               (Tactic.simpErase "-" `UpperHalfPlane.denom)
               ","
               (Tactic.simpErase "-" `denom_apply)]
              "]")]
            [])
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule
               []
               (Term.typeAscription
                "("
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])])))
                ":"
                [(«term_=_»
                  («term_-_»
                   («term_*_»
                    (Term.typeAscription
                     "("
                     (Term.app `p [(num "1")])
                     ":"
                     [(Data.Complex.Basic.termℂ "ℂ")]
                     ")")
                    "*"
                    `z)
                   "-"
                   (Term.app `p [(num "0")]))
                  "="
                  («term_*_»
                   («term_-_»
                    («term_*_» (Term.app `p [(num "1")]) "*" `z)
                    "-"
                    (Term.app `p [(num "0")]))
                   "*"
                   (coeNotation
                    "↑"
                    (Term.app
                     `det
                     [(Term.typeAscription
                       "("
                       (coeNotation "↑" `g)
                       ":"
                       [(Term.app
                         `Matrix
                         [(Term.app `Fin [(num "2")]) (Term.app `Fin [(num "2")]) (termℤ "ℤ")])]
                       ")")]))))]
                ")"))]
             "]")
            [])
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `hg)
              ","
              (Tactic.rwRule [] `det_fin_two)]
             "]")
            [])
           []
           (Tactic.simp
            "simp"
            []
            []
            ["only"]
            ["["
             [(Tactic.simpLemma [] [] `Int.coe_castRingHom)
              ","
              (Tactic.simpLemma [] [] `coe_matrix_coe)
              ","
              (Tactic.simpLemma [] [] `Int.cast_mul)
              ","
              (Tactic.simpLemma [] [] `of_real_int_cast)
              ","
              (Tactic.simpLemma [] [] `map_apply)
              ","
              (Tactic.simpLemma [] [] `denom)
              ","
              (Tactic.simpLemma [] [] `Int.cast_sub)
              ","
              (Tactic.simpLemma [] [] `_root_.coe_coe)
              ","
              (Tactic.simpLemma [] [] `coe_GL_pos_coe_GL_coe_matrix)]
             "]"]
            [])
           []
           (Mathlib.Tactic.RingNF.ring "ring")])))
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
         [(Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`nonZ1 []]
             [(Term.typeSpec
               ":"
               («term_≠_»
                («term_+_»
                 («term_^_»
                  (Term.typeAscription
                   "("
                   (Term.app `p [(num "0")])
                   ":"
                   [(Data.Complex.Basic.termℂ "ℂ")]
                   ")")
                  "^"
                  (num "2"))
                 "+"
                 («term_^_» (Term.app `p [(num "1")]) "^" (num "2")))
                "≠"
                (num "0")))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.NormCast.tacticExact_mod_cast_
                  "exact_mod_cast"
                  `hp.sq_add_sq_ne_zero)]))))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             []
             [(Term.typeSpec
               ":"
               («term_≠_»
                («term_∘_»
                 (Term.typeAscription
                  "("
                  `coe
                  ":"
                  [(Term.arrow (termℤ "ℤ") "→" (Data.Real.Basic.termℝ "ℝ"))]
                  ")")
                 "∘"
                 `p)
                "≠"
                (num "0")))]
             ":="
             (Term.fun
              "fun"
              (Term.basicFun
               [`h]
               []
               "=>"
               (Term.app
                `hp.ne_zero
                [(Term.byTactic
                  "by"
                  (Tactic.tacticSeq
                   (Tactic.tacticSeq1Indented
                    [(Tactic.«tactic_<;>_»
                      (Std.Tactic.Ext.«tacticExt___:_»
                       "ext"
                       [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `i))]
                       [])
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
                        ["using" (Term.app `congr_fun [`h `i])])))])))]))))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`nonZ2 []]
             [(Term.typeSpec
               ":"
               («term_≠_»
                («term_+_»
                 («term_*_»
                  (Term.typeAscription
                   "("
                   (Term.app `p [(num "0")])
                   ":"
                   [(Data.Complex.Basic.termℂ "ℂ")]
                   ")")
                  "*"
                  `z)
                 "+"
                 (Term.app `p [(num "1")]))
                "≠"
                (num "0")))]
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
                   []
                   ["using" (Term.app `linear_ne_zero [(Term.hole "_") `z `this])]))]))))))
          []
          (Tactic.fieldSimp
           "field_simp"
           []
           []
           []
           [(Tactic.simpArgs
             "["
             [(Tactic.simpLemma [] [] `nonZ1)
              ","
              (Tactic.simpLemma [] [] `nonZ2)
              ","
              (Tactic.simpLemma [] [] `denom_ne_zero)
              ","
              (Tactic.simpErase "-" `UpperHalfPlane.denom)
              ","
              (Tactic.simpErase "-" `denom_apply)]
             "]")]
           [])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule
              []
              (Term.typeAscription
               "("
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])])))
               ":"
               [(«term_=_»
                 («term_-_»
                  («term_*_»
                   (Term.typeAscription
                    "("
                    (Term.app `p [(num "1")])
                    ":"
                    [(Data.Complex.Basic.termℂ "ℂ")]
                    ")")
                   "*"
                   `z)
                  "-"
                  (Term.app `p [(num "0")]))
                 "="
                 («term_*_»
                  («term_-_»
                   («term_*_» (Term.app `p [(num "1")]) "*" `z)
                   "-"
                   (Term.app `p [(num "0")]))
                  "*"
                  (coeNotation
                   "↑"
                   (Term.app
                    `det
                    [(Term.typeAscription
                      "("
                      (coeNotation "↑" `g)
                      ":"
                      [(Term.app
                        `Matrix
                        [(Term.app `Fin [(num "2")]) (Term.app `Fin [(num "2")]) (termℤ "ℤ")])]
                      ")")]))))]
               ")"))]
            "]")
           [])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `hg)
             ","
             (Tactic.rwRule [] `det_fin_two)]
            "]")
           [])
          []
          (Tactic.simp
           "simp"
           []
           []
           ["only"]
           ["["
            [(Tactic.simpLemma [] [] `Int.coe_castRingHom)
             ","
             (Tactic.simpLemma [] [] `coe_matrix_coe)
             ","
             (Tactic.simpLemma [] [] `Int.cast_mul)
             ","
             (Tactic.simpLemma [] [] `of_real_int_cast)
             ","
             (Tactic.simpLemma [] [] `map_apply)
             ","
             (Tactic.simpLemma [] [] `denom)
             ","
             (Tactic.simpLemma [] [] `Int.cast_sub)
             ","
             (Tactic.simpLemma [] [] `_root_.coe_coe)
             ","
             (Tactic.simpLemma [] [] `coe_GL_pos_coe_GL_coe_matrix)]
            "]"]
           [])
          []
          (Mathlib.Tactic.RingNF.ring "ring")])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.RingNF.ring "ring")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["["
        [(Tactic.simpLemma [] [] `Int.coe_castRingHom)
         ","
         (Tactic.simpLemma [] [] `coe_matrix_coe)
         ","
         (Tactic.simpLemma [] [] `Int.cast_mul)
         ","
         (Tactic.simpLemma [] [] `of_real_int_cast)
         ","
         (Tactic.simpLemma [] [] `map_apply)
         ","
         (Tactic.simpLemma [] [] `denom)
         ","
         (Tactic.simpLemma [] [] `Int.cast_sub)
         ","
         (Tactic.simpLemma [] [] `_root_.coe_coe)
         ","
         (Tactic.simpLemma [] [] `coe_GL_pos_coe_GL_coe_matrix)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `coe_GL_pos_coe_GL_coe_matrix
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `_root_.coe_coe
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Int.cast_sub
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `denom
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `map_apply
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `of_real_int_cast
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Int.cast_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `coe_matrix_coe
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Int.coe_castRingHom
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `hg) "," (Tactic.rwRule [] `det_fin_two)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `det_fin_two
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hg
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule
          []
          (Term.typeAscription
           "("
           (Term.byTactic
            "by"
            (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])])))
           ":"
           [(«term_=_»
             («term_-_»
              («term_*_»
               (Term.typeAscription
                "("
                (Term.app `p [(num "1")])
                ":"
                [(Data.Complex.Basic.termℂ "ℂ")]
                ")")
               "*"
               `z)
              "-"
              (Term.app `p [(num "0")]))
             "="
             («term_*_»
              («term_-_» («term_*_» (Term.app `p [(num "1")]) "*" `z) "-" (Term.app `p [(num "0")]))
              "*"
              (coeNotation
               "↑"
               (Term.app
                `det
                [(Term.typeAscription
                  "("
                  (coeNotation "↑" `g)
                  ":"
                  [(Term.app
                    `Matrix
                    [(Term.app `Fin [(num "2")]) (Term.app `Fin [(num "2")]) (termℤ "ℤ")])]
                  ")")]))))]
           ")"))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription
       "("
       (Term.byTactic
        "by"
        (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])])))
       ":"
       [(«term_=_»
         («term_-_»
          («term_*_»
           (Term.typeAscription
            "("
            (Term.app `p [(num "1")])
            ":"
            [(Data.Complex.Basic.termℂ "ℂ")]
            ")")
           "*"
           `z)
          "-"
          (Term.app `p [(num "0")]))
         "="
         («term_*_»
          («term_-_» («term_*_» (Term.app `p [(num "1")]) "*" `z) "-" (Term.app `p [(num "0")]))
          "*"
          (coeNotation
           "↑"
           (Term.app
            `det
            [(Term.typeAscription
              "("
              (coeNotation "↑" `g)
              ":"
              [(Term.app
                `Matrix
                [(Term.app `Fin [(num "2")]) (Term.app `Fin [(num "2")]) (termℤ "ℤ")])]
              ")")]))))]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       («term_-_»
        («term_*_»
         (Term.typeAscription
          "("
          (Term.app `p [(num "1")])
          ":"
          [(Data.Complex.Basic.termℂ "ℂ")]
          ")")
         "*"
         `z)
        "-"
        (Term.app `p [(num "0")]))
       "="
       («term_*_»
        («term_-_» («term_*_» (Term.app `p [(num "1")]) "*" `z) "-" (Term.app `p [(num "0")]))
        "*"
        (coeNotation
         "↑"
         (Term.app
          `det
          [(Term.typeAscription
            "("
            (coeNotation "↑" `g)
            ":"
            [(Term.app
              `Matrix
              [(Term.app `Fin [(num "2")]) (Term.app `Fin [(num "2")]) (termℤ "ℤ")])]
            ")")]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_»
       («term_-_» («term_*_» (Term.app `p [(num "1")]) "*" `z) "-" (Term.app `p [(num "0")]))
       "*"
       (coeNotation
        "↑"
        (Term.app
         `det
         [(Term.typeAscription
           "("
           (coeNotation "↑" `g)
           ":"
           [(Term.app
             `Matrix
             [(Term.app `Fin [(num "2")]) (Term.app `Fin [(num "2")]) (termℤ "ℤ")])]
           ")")])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (coeNotation
       "↑"
       (Term.app
        `det
        [(Term.typeAscription
          "("
          (coeNotation "↑" `g)
          ":"
          [(Term.app `Matrix [(Term.app `Fin [(num "2")]) (Term.app `Fin [(num "2")]) (termℤ "ℤ")])]
          ")")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `det
       [(Term.typeAscription
         "("
         (coeNotation "↑" `g)
         ":"
         [(Term.app `Matrix [(Term.app `Fin [(num "2")]) (Term.app `Fin [(num "2")]) (termℤ "ℤ")])]
         ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription
       "("
       (coeNotation "↑" `g)
       ":"
       [(Term.app `Matrix [(Term.app `Fin [(num "2")]) (Term.app `Fin [(num "2")]) (termℤ "ℤ")])]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Matrix [(Term.app `Fin [(num "2")]) (Term.app `Fin [(num "2")]) (termℤ "ℤ")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'termℤ', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'termℤ', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (termℤ "ℤ")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.app `Fin [(num "2")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Fin
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `Fin [(num "2")]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `Fin [(num "2")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Fin
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `Fin [(num "2")]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Matrix
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (coeNotation "↑" `g)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 1024, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `det
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `det
      [(Term.typeAscription
        "("
        (coeNotation "↑" `g)
        ":"
        [(Term.app
          `Matrix
          [(Term.paren "(" (Term.app `Fin [(num "2")]) ")")
           (Term.paren "(" (Term.app `Fin [(num "2")]) ")")
           (termℤ "ℤ")])]
        ")")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (some 1024,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      («term_-_» («term_*_» (Term.app `p [(num "1")]) "*" `z) "-" (Term.app `p [(num "0")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `p [(num "0")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      («term_*_» (Term.app `p [(num "1")]) "*" `z)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `z
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (Term.app `p [(num "1")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1022, (some 1023, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 65 >? 70, (some 71, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 65, (some 66, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_-_» («term_*_» (Term.app `p [(num "1")]) "*" `z) "-" (Term.app `p [(num "0")]))
     ")")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      («term_-_»
       («term_*_»
        (Term.typeAscription "(" (Term.app `p [(num "1")]) ":" [(Data.Complex.Basic.termℂ "ℂ")] ")")
        "*"
        `z)
       "-"
       (Term.app `p [(num "0")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `p [(num "0")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      («term_*_»
       (Term.typeAscription "(" (Term.app `p [(num "1")]) ":" [(Data.Complex.Basic.termℂ "ℂ")] ")")
       "*"
       `z)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `z
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (Term.typeAscription "(" (Term.app `p [(num "1")]) ":" [(Data.Complex.Basic.termℂ "ℂ")] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Complex.Basic.termℂ "ℂ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `p [(num "1")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 65 >? 70, (some 71, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 65, (some 66, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] [] [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.fieldSimp
       "field_simp"
       []
       []
       []
       [(Tactic.simpArgs
         "["
         [(Tactic.simpLemma [] [] `nonZ1)
          ","
          (Tactic.simpLemma [] [] `nonZ2)
          ","
          (Tactic.simpLemma [] [] `denom_ne_zero)
          ","
          (Tactic.simpErase "-" `UpperHalfPlane.denom)
          ","
          (Tactic.simpErase "-" `denom_apply)]
         "]")]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpErase', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `denom_apply
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpErase', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `UpperHalfPlane.denom
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `denom_ne_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `nonZ2
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `nonZ1
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`nonZ2 []]
         [(Term.typeSpec
           ":"
           («term_≠_»
            («term_+_»
             («term_*_»
              (Term.typeAscription
               "("
               (Term.app `p [(num "0")])
               ":"
               [(Data.Complex.Basic.termℂ "ℂ")]
               ")")
              "*"
              `z)
             "+"
             (Term.app `p [(num "1")]))
            "≠"
            (num "0")))]
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
               []
               ["using" (Term.app `linear_ne_zero [(Term.hole "_") `z `this])]))]))))))
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
            []
            ["using" (Term.app `linear_ne_zero [(Term.hole "_") `z `this])]))])))
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
        []
        ["using" (Term.app `linear_ne_zero [(Term.hole "_") `z `this])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `linear_ne_zero [(Term.hole "_") `z `this])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `this
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `z
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `linear_ne_zero
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≠_»
       («term_+_»
        («term_*_»
         (Term.typeAscription
          "("
          (Term.app `p [(num "0")])
          ":"
          [(Data.Complex.Basic.termℂ "ℂ")]
          ")")
         "*"
         `z)
        "+"
        (Term.app `p [(num "1")]))
       "≠"
       (num "0"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      («term_+_»
       («term_*_»
        (Term.typeAscription "(" (Term.app `p [(num "0")]) ":" [(Data.Complex.Basic.termℂ "ℂ")] ")")
        "*"
        `z)
       "+"
       (Term.app `p [(num "1")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `p [(num "1")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      («term_*_»
       (Term.typeAscription "(" (Term.app `p [(num "0")]) ":" [(Data.Complex.Basic.termℂ "ℂ")] ")")
       "*"
       `z)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `z
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (Term.typeAscription "(" (Term.app `p [(num "0")]) ":" [(Data.Complex.Basic.termℂ "ℂ")] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Complex.Basic.termℂ "ℂ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `p [(num "0")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 65 >? 70, (some 71, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 65, (some 66, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         []
         [(Term.typeSpec
           ":"
           («term_≠_»
            («term_∘_»
             (Term.typeAscription
              "("
              `coe
              ":"
              [(Term.arrow (termℤ "ℤ") "→" (Data.Real.Basic.termℝ "ℝ"))]
              ")")
             "∘"
             `p)
            "≠"
            (num "0")))]
         ":="
         (Term.fun
          "fun"
          (Term.basicFun
           [`h]
           []
           "=>"
           (Term.app
            `hp.ne_zero
            [(Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.«tactic_<;>_»
                  (Std.Tactic.Ext.«tacticExt___:_»
                   "ext"
                   [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `i))]
                   [])
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
                    ["using" (Term.app `congr_fun [`h `i])])))])))]))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`h]
        []
        "=>"
        (Term.app
         `hp.ne_zero
         [(Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(Tactic.«tactic_<;>_»
               (Std.Tactic.Ext.«tacticExt___:_»
                "ext"
                [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `i))]
                [])
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
                 ["using" (Term.app `congr_fun [`h `i])])))])))])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `hp.ne_zero
       [(Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Tactic.«tactic_<;>_»
             (Std.Tactic.Ext.«tacticExt___:_»
              "ext"
              [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `i))]
              [])
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
               ["using" (Term.app `congr_fun [`h `i])])))])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.«tactic_<;>_»
           (Std.Tactic.Ext.«tacticExt___:_»
            "ext"
            [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `i))]
            [])
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
             ["using" (Term.app `congr_fun [`h `i])])))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.«tactic_<;>_»
       (Std.Tactic.Ext.«tacticExt___:_»
        "ext"
        [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `i))]
        [])
       "<;>"
       (Std.Tactic.Simpa.simpa
        "simpa"
        []
        []
        (Std.Tactic.Simpa.simpaArgsRest [] [] [] [] ["using" (Term.app `congr_fun [`h `i])])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Simpa.simpa
       "simpa"
       []
       []
       (Std.Tactic.Simpa.simpaArgsRest [] [] [] [] ["using" (Term.app `congr_fun [`h `i])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `congr_fun [`h `i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `congr_fun
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 2 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
      (Std.Tactic.Ext.«tacticExt___:_»
       "ext"
       [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `i))]
       [])
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
          (Std.Tactic.Ext.«tacticExt___:_»
           "ext"
           [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `i))]
           [])
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
            ["using" (Term.app `congr_fun [`h `i])])))])))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `hp.ne_zero
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
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≠_»
       («term_∘_»
        (Term.typeAscription
         "("
         `coe
         ":"
         [(Term.arrow (termℤ "ℤ") "→" (Data.Real.Basic.termℝ "ℝ"))]
         ")")
        "∘"
        `p)
       "≠"
       (num "0"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      («term_∘_»
       (Term.typeAscription
        "("
        `coe
        ":"
        [(Term.arrow (termℤ "ℤ") "→" (Data.Real.Basic.termℝ "ℝ"))]
        ")")
       "∘"
       `p)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p
[PrettyPrinter.parenthesize] ...precedences are 90 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 90, term))
      (Term.typeAscription
       "("
       `coe
       ":"
       [(Term.arrow (termℤ "ℤ") "→" (Data.Real.Basic.termℝ "ℝ"))]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.arrow (termℤ "ℤ") "→" (Data.Real.Basic.termℝ "ℝ"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Real.Basic.termℝ "ℝ")
[PrettyPrinter.parenthesize] ...precedences are 25 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
      (termℤ "ℤ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 25, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 25, (some 25, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `coe
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 91 >? 1024, (none, [anonymous]) <=? (some 90, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 90, (some 90, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`nonZ1 []]
         [(Term.typeSpec
           ":"
           («term_≠_»
            («term_+_»
             («term_^_»
              (Term.typeAscription
               "("
               (Term.app `p [(num "0")])
               ":"
               [(Data.Complex.Basic.termℂ "ℂ")]
               ")")
              "^"
              (num "2"))
             "+"
             («term_^_» (Term.app `p [(num "1")]) "^" (num "2")))
            "≠"
            (num "0")))]
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.NormCast.tacticExact_mod_cast_ "exact_mod_cast" `hp.sq_add_sq_ne_zero)]))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.NormCast.tacticExact_mod_cast_ "exact_mod_cast" `hp.sq_add_sq_ne_zero)])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.NormCast.tacticExact_mod_cast_ "exact_mod_cast" `hp.sq_add_sq_ne_zero)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hp.sq_add_sq_ne_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≠_»
       («term_+_»
        («term_^_»
         (Term.typeAscription
          "("
          (Term.app `p [(num "0")])
          ":"
          [(Data.Complex.Basic.termℂ "ℂ")]
          ")")
         "^"
         (num "2"))
        "+"
        («term_^_» (Term.app `p [(num "1")]) "^" (num "2")))
       "≠"
       (num "0"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      («term_+_»
       («term_^_»
        (Term.typeAscription "(" (Term.app `p [(num "0")]) ":" [(Data.Complex.Basic.termℂ "ℂ")] ")")
        "^"
        (num "2"))
       "+"
       («term_^_» (Term.app `p [(num "1")]) "^" (num "2")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_» (Term.app `p [(num "1")]) "^" (num "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Term.app `p [(num "1")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1022, (some 1023, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      («term_^_»
       (Term.typeAscription "(" (Term.app `p [(num "0")]) ":" [(Data.Complex.Basic.termℂ "ℂ")] ")")
       "^"
       (num "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Term.typeAscription "(" (Term.app `p [(num "0")]) ":" [(Data.Complex.Basic.termℂ "ℂ")] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Complex.Basic.termℂ "ℂ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `p [(num "0")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 65 >? 80, (some 80, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 65, (some 66, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (coeNotation "↑" (Algebra.Group.Defs.«term_•_» `g " • " `z))
       "="
       («term_+_»
        («term_/_»
         (Term.typeAscription
          "("
          (Term.app
           `lcRow0
           [`p
            (coeNotation
             "↑"
             (Term.typeAscription
              "("
              `g
              ":"
              [(NumberTheory.Modular.«termSL(_,_)»
                "SL("
                (num "2")
                ", "
                (Data.Real.Basic.termℝ "ℝ")
                ")")]
              ")"))])
          ":"
          [(Data.Complex.Basic.termℂ "ℂ")]
          ")")
         "/"
         («term_+_»
          («term_^_» (Term.app `p [(num "0")]) "^" (num "2"))
          "+"
          («term_^_» (Term.app `p [(num "1")]) "^" (num "2"))))
        "+"
        («term_/_»
         («term_-_»
          («term_*_»
           (Term.typeAscription
            "("
            (Term.app `p [(num "1")])
            ":"
            [(Data.Complex.Basic.termℂ "ℂ")]
            ")")
           "*"
           `z)
          "-"
          (Term.app `p [(num "0")]))
         "/"
         («term_*_»
          («term_+_»
           («term_^_» (Term.app `p [(num "0")]) "^" (num "2"))
           "+"
           («term_^_» (Term.app `p [(num "1")]) "^" (num "2")))
          "*"
          («term_+_» («term_*_» (Term.app `p [(num "0")]) "*" `z) "+" (Term.app `p [(num "1")]))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_»
       («term_/_»
        (Term.typeAscription
         "("
         (Term.app
          `lcRow0
          [`p
           (coeNotation
            "↑"
            (Term.typeAscription
             "("
             `g
             ":"
             [(NumberTheory.Modular.«termSL(_,_)»
               "SL("
               (num "2")
               ", "
               (Data.Real.Basic.termℝ "ℝ")
               ")")]
             ")"))])
         ":"
         [(Data.Complex.Basic.termℂ "ℂ")]
         ")")
        "/"
        («term_+_»
         («term_^_» (Term.app `p [(num "0")]) "^" (num "2"))
         "+"
         («term_^_» (Term.app `p [(num "1")]) "^" (num "2"))))
       "+"
       («term_/_»
        («term_-_»
         («term_*_»
          (Term.typeAscription
           "("
           (Term.app `p [(num "1")])
           ":"
           [(Data.Complex.Basic.termℂ "ℂ")]
           ")")
          "*"
          `z)
         "-"
         (Term.app `p [(num "0")]))
        "/"
        («term_*_»
         («term_+_»
          («term_^_» (Term.app `p [(num "0")]) "^" (num "2"))
          "+"
          («term_^_» (Term.app `p [(num "1")]) "^" (num "2")))
         "*"
         («term_+_» («term_*_» (Term.app `p [(num "0")]) "*" `z) "+" (Term.app `p [(num "1")])))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_/_»
       («term_-_»
        («term_*_»
         (Term.typeAscription
          "("
          (Term.app `p [(num "1")])
          ":"
          [(Data.Complex.Basic.termℂ "ℂ")]
          ")")
         "*"
         `z)
        "-"
        (Term.app `p [(num "0")]))
       "/"
       («term_*_»
        («term_+_»
         («term_^_» (Term.app `p [(num "0")]) "^" (num "2"))
         "+"
         («term_^_» (Term.app `p [(num "1")]) "^" (num "2")))
        "*"
        («term_+_» («term_*_» (Term.app `p [(num "0")]) "*" `z) "+" (Term.app `p [(num "1")]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_»
       («term_+_»
        («term_^_» (Term.app `p [(num "0")]) "^" (num "2"))
        "+"
        («term_^_» (Term.app `p [(num "1")]) "^" (num "2")))
       "*"
       («term_+_» («term_*_» (Term.app `p [(num "0")]) "*" `z) "+" (Term.app `p [(num "1")])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_» («term_*_» (Term.app `p [(num "0")]) "*" `z) "+" (Term.app `p [(num "1")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `p [(num "1")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      («term_*_» (Term.app `p [(num "0")]) "*" `z)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `z
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (Term.app `p [(num "0")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1022, (some 1023, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 65 >? 70, (some 71, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_+_» («term_*_» (Term.app `p [(num "0")]) "*" `z) "+" (Term.app `p [(num "1")]))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      («term_+_»
       («term_^_» (Term.app `p [(num "0")]) "^" (num "2"))
       "+"
       («term_^_» (Term.app `p [(num "1")]) "^" (num "2")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_» (Term.app `p [(num "1")]) "^" (num "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Term.app `p [(num "1")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1022, (some 1023, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      («term_^_» (Term.app `p [(num "0")]) "^" (num "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Term.app `p [(num "0")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1022, (some 1023, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 65 >? 80, (some 80, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 65, (some 66, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_+_»
      («term_^_» (Term.app `p [(num "0")]) "^" (num "2"))
      "+"
      («term_^_» (Term.app `p [(num "1")]) "^" (num "2")))
     ")")
[PrettyPrinter.parenthesize] ...precedences are 71 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_*_»
      (Term.paren
       "("
       («term_+_»
        («term_^_» (Term.app `p [(num "0")]) "^" (num "2"))
        "+"
        («term_^_» (Term.app `p [(num "1")]) "^" (num "2")))
       ")")
      "*"
      (Term.paren
       "("
       («term_+_» («term_*_» (Term.app `p [(num "0")]) "*" `z) "+" (Term.app `p [(num "1")]))
       ")"))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      («term_-_»
       («term_*_»
        (Term.typeAscription "(" (Term.app `p [(num "1")]) ":" [(Data.Complex.Basic.termℂ "ℂ")] ")")
        "*"
        `z)
       "-"
       (Term.app `p [(num "0")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `p [(num "0")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      («term_*_»
       (Term.typeAscription "(" (Term.app `p [(num "1")]) ":" [(Data.Complex.Basic.termℂ "ℂ")] ")")
       "*"
       `z)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `z
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (Term.typeAscription "(" (Term.app `p [(num "1")]) ":" [(Data.Complex.Basic.termℂ "ℂ")] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Complex.Basic.termℂ "ℂ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `p [(num "1")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 65 >? 70, (some 71, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 65, (some 66, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_-_»
      («term_*_»
       (Term.typeAscription "(" (Term.app `p [(num "1")]) ":" [(Data.Complex.Basic.termℂ "ℂ")] ")")
       "*"
       `z)
      "-"
      (Term.app `p [(num "0")]))
     ")")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      («term_/_»
       (Term.typeAscription
        "("
        (Term.app
         `lcRow0
         [`p
          (coeNotation
           "↑"
           (Term.typeAscription
            "("
            `g
            ":"
            [(NumberTheory.Modular.«termSL(_,_)»
              "SL("
              (num "2")
              ", "
              (Data.Real.Basic.termℝ "ℝ")
              ")")]
            ")"))])
        ":"
        [(Data.Complex.Basic.termℂ "ℂ")]
        ")")
       "/"
       («term_+_»
        («term_^_» (Term.app `p [(num "0")]) "^" (num "2"))
        "+"
        («term_^_» (Term.app `p [(num "1")]) "^" (num "2"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_»
       («term_^_» (Term.app `p [(num "0")]) "^" (num "2"))
       "+"
       («term_^_» (Term.app `p [(num "1")]) "^" (num "2")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_» (Term.app `p [(num "1")]) "^" (num "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Term.app `p [(num "1")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1022, (some 1023, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      («term_^_» (Term.app `p [(num "0")]) "^" (num "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Term.app `p [(num "0")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1022, (some 1023, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 65 >? 80, (some 80, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_+_»
      («term_^_» (Term.app `p [(num "0")]) "^" (num "2"))
      "+"
      («term_^_» (Term.app `p [(num "1")]) "^" (num "2")))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (Term.typeAscription
       "("
       (Term.app
        `lcRow0
        [`p
         (coeNotation
          "↑"
          (Term.typeAscription
           "("
           `g
           ":"
           [(NumberTheory.Modular.«termSL(_,_)»
             "SL("
             (num "2")
             ", "
             (Data.Real.Basic.termℝ "ℝ")
             ")")]
           ")"))])
       ":"
       [(Data.Complex.Basic.termℂ "ℂ")]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Complex.Basic.termℂ "ℂ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `lcRow0
       [`p
        (coeNotation
         "↑"
         (Term.typeAscription
          "("
          `g
          ":"
          [(NumberTheory.Modular.«termSL(_,_)»
            "SL("
            (num "2")
            ", "
            (Data.Real.Basic.termℝ "ℝ")
            ")")]
          ")"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'coeNotation', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'coeNotation', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (coeNotation
       "↑"
       (Term.typeAscription
        "("
        `g
        ":"
        [(NumberTheory.Modular.«termSL(_,_)» "SL(" (num "2") ", " (Data.Real.Basic.termℝ "ℝ") ")")]
        ")"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription
       "("
       `g
       ":"
       [(NumberTheory.Modular.«termSL(_,_)» "SL(" (num "2") ", " (Data.Real.Basic.termℝ "ℝ") ")")]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (NumberTheory.Modular.«termSL(_,_)» "SL(" (num "2") ", " (Data.Real.Basic.termℝ "ℝ") ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.Modular.«termSL(_,_)»', expected 'NumberTheory.Modular.termSL(_,_)._@.NumberTheory.Modular._hyg.8'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    This replaces `(g•z).re = a/c + *` in the standard theory with the following novel identity:
      `g • z = (a c + b d) / (c^2 + d^2) + (d z - c) / ((c^2 + d^2) (c z + d))`
      which does not need to be decomposed depending on whether `c = 0`. -/
  theorem
    smul_eq_lc_row0_add
    { p : Fin 2 → ℤ } ( hp : IsCoprime p 0 p 1 ) ( hg : ↑ₘ g 1 = p )
      :
        ↑ g • z
          =
          ( lcRow0 p ↑ ( g : SL( 2 , ℝ ) ) : ℂ ) / p 0 ^ 2 + p 1 ^ 2
            +
            ( p 1 : ℂ ) * z - p 0 / p 0 ^ 2 + p 1 ^ 2 * p 0 * z + p 1
    :=
      by
        have nonZ1 : ( p 0 : ℂ ) ^ 2 + p 1 ^ 2 ≠ 0 := by exact_mod_cast hp.sq_add_sq_ne_zero
          have
            : ( coe : ℤ → ℝ ) ∘ p ≠ 0 := fun h => hp.ne_zero by ext i <;> simpa using congr_fun h i
          have nonZ2 : ( p 0 : ℂ ) * z + p 1 ≠ 0 := by simpa using linear_ne_zero _ z this
          field_simp [ nonZ1 , nonZ2 , denom_ne_zero , - UpperHalfPlane.denom , - denom_apply ]
          rw
            [
              (
                by simp
                :
                ( p 1 : ℂ ) * z - p 0 = p 1 * z - p 0 * ↑ det ( ↑ g : Matrix Fin 2 Fin 2 ℤ )
                )
              ]
          rw [ ← hg , det_fin_two ]
          simp
            only
            [
              Int.coe_castRingHom
                ,
                coe_matrix_coe
                ,
                Int.cast_mul
                ,
                of_real_int_cast
                ,
                map_apply
                ,
                denom
                ,
                Int.cast_sub
                ,
                _root_.coe_coe
                ,
                coe_GL_pos_coe_GL_coe_matrix
              ]
          ring
#align modular_group.smul_eq_lc_row0_add ModularGroup.smul_eq_lc_row0_add

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `tendsto_abs_re_smul [])
      (Command.declSig
       [(Term.implicitBinder
         "{"
         [`p]
         [":" (Term.arrow (Term.app `Fin [(num "2")]) "→" (termℤ "ℤ"))]
         "}")
        (Term.explicitBinder
         "("
         [`hp]
         [":" (Term.app `IsCoprime [(Term.app `p [(num "0")]) (Term.app `p [(num "1")])])]
         []
         ")")]
       (Term.typeSpec
        ":"
        (Term.app
         `Tendsto
         [(Term.fun
           "fun"
           (Term.basicFun
            [`g]
            [(Term.typeSpec
              ":"
              («term{_:_//_}»
               "{"
               `g
               [":" (NumberTheory.Modular.«termSL(_,_)» "SL(" (num "2") ", " (termℤ "ℤ") ")")]
               "//"
               («term_=_» (Term.app (NumberTheory.Modular.«term↑ₘ_» "↑ₘ" `g) [(num "1")]) "=" `p)
               "}"))]
            "=>"
            («term|___|»
             (group "|")
             (Term.proj
              (Algebra.Group.Defs.«term_•_»
               (Term.typeAscription
                "("
                `g
                ":"
                [(NumberTheory.Modular.«termSL(_,_)» "SL(" (num "2") ", " (termℤ "ℤ") ")")]
                ")")
               " • "
               `z)
              "."
              `re)
             (group)
             "|")))
          `cofinite
          `atTop])))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.tacticSuffices_
            "suffices"
            (Term.sufficesDecl
             []
             (Term.app
              `tendsto
              [(Term.fun
                "fun"
                (Term.basicFun
                 [`g]
                 [(Term.typeSpec
                   ":"
                   (Set.Data.Set.Image.«term_⁻¹'_»
                    (Term.fun
                     "fun"
                     (Term.basicFun
                      [`g]
                      [(Term.typeSpec
                        ":"
                        (NumberTheory.Modular.«termSL(_,_)» "SL(" (num "2") ", " (termℤ "ℤ") ")"))]
                      "=>"
                      (Term.app (NumberTheory.Modular.«term↑ₘ_» "↑ₘ" `g) [(num "1")])))
                    " ⁻¹' "
                    («term{_}» "{" [`p] "}")))]
                 "=>"
                 (Term.proj
                  (Algebra.Group.Defs.«term_•_»
                   (Term.typeAscription
                    "("
                    `g
                    ":"
                    [(NumberTheory.Modular.«termSL(_,_)» "SL(" (num "2") ", " (termℤ "ℤ") ")")]
                    ")")
                   " • "
                   `z)
                  "."
                  `re)))
               `cofinite
               (Term.app `cocompact [(Data.Real.Basic.termℝ "ℝ")])])
             (Term.byTactic'
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.exact "exact" (Term.app `tendsto_norm_cocompact_at_top.comp [`this]))])))))
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              []
              [(Term.typeSpec
                ":"
                («term_≠_»
                 («term_⁻¹»
                  («term_+_»
                   («term_^_»
                    (Term.typeAscription
                     "("
                     (Term.app `p [(num "0")])
                     ":"
                     [(Data.Real.Basic.termℝ "ℝ")]
                     ")")
                    "^"
                    (num "2"))
                   "+"
                   («term_^_» (Term.app `p [(num "1")]) "^" (num "2")))
                  "⁻¹")
                 "≠"
                 (num "0")))]
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Tactic.apply "apply" `inv_ne_zero)
                  []
                  (Tactic.NormCast.tacticExact_mod_cast_
                   "exact_mod_cast"
                   `hp.sq_add_sq_ne_zero)]))))))
           []
           (Tactic.tacticLet_
            "let"
            (Term.letDecl
             (Term.letIdDecl
              `f
              []
              []
              ":="
              (Term.app `Homeomorph.mulRight₀ [(Term.hole "_") `this]))))
           []
           (Tactic.tacticLet_
            "let"
            (Term.letDecl
             (Term.letIdDecl
              `ff
              []
              []
              ":="
              (Term.app
               `Homeomorph.addRight
               [(Term.proj
                 («term_/_»
                  («term_-_»
                   («term_*_»
                    (Term.typeAscription
                     "("
                     (Term.app `p [(num "1")])
                     ":"
                     [(Data.Complex.Basic.termℂ "ℂ")]
                     ")")
                    "*"
                    `z)
                   "-"
                   (Term.app `p [(num "0")]))
                  "/"
                  («term_*_»
                   («term_+_»
                    («term_^_» (Term.app `p [(num "0")]) "^" (num "2"))
                    "+"
                    («term_^_» (Term.app `p [(num "1")]) "^" (num "2")))
                   "*"
                   («term_+_»
                    («term_*_» (Term.app `p [(num "0")]) "*" `z)
                    "+"
                    (Term.app `p [(num "1")]))))
                 "."
                 `re)]))))
           []
           (convert
            "convert"
            []
            (Term.app
             (Term.proj
              (Term.proj
               (Term.proj (Term.app `f.trans [`ff]) "." `ClosedEmbedding)
               "."
               `tendsto_cocompact)
              "."
              `comp)
             [(Term.app `tendsto_lc_row0 [`hp])])
            [])
           []
           (Std.Tactic.Ext.«tacticExt___:_»
            "ext"
            [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `g))]
            [])
           []
           (Tactic.change
            "change"
            («term_=_»
             (Term.proj
              (Algebra.Group.Defs.«term_•_»
               (Term.typeAscription
                "("
                `g
                ":"
                [(NumberTheory.Modular.«termSL(_,_)» "SL(" (num "2") ", " (termℤ "ℤ") ")")]
                ")")
               " • "
               `z)
              "."
              `re)
             "="
             («term_+_»
              («term_/_»
               (Term.app
                `lc_row0
                [`p
                 (coeNotation
                  "↑"
                  (Term.typeAscription
                   "("
                   (coeNotation "↑" `g)
                   ":"
                   [(NumberTheory.Modular.«termSL(_,_)»
                     "SL("
                     (num "2")
                     ", "
                     (Data.Real.Basic.termℝ "ℝ")
                     ")")]
                   ")"))])
               "/"
               («term_+_»
                («term_^_» (Term.app `p [(num "0")]) "^" (num "2"))
                "+"
                («term_^_» (Term.app `p [(num "1")]) "^" (num "2"))))
              "+"
              (Term.proj
               («term_/_»
                («term_-_»
                 («term_*_»
                  (Term.typeAscription
                   "("
                   (Term.app `p [(num "1")])
                   ":"
                   [(Data.Complex.Basic.termℂ "ℂ")]
                   ")")
                  "*"
                  `z)
                 "-"
                 (Term.app `p [(num "0")]))
                "/"
                («term_*_»
                 («term_+_»
                  («term_^_» (Term.app `p [(num "0")]) "^" (num "2"))
                  "+"
                  («term_^_» (Term.app `p [(num "1")]) "^" (num "2")))
                 "*"
                 («term_+_»
                  («term_*_» (Term.app `p [(num "0")]) "*" `z)
                  "+"
                  (Term.app `p [(num "1")]))))
               "."
               `re)))
            [])
           []
           (Tactic.NormCast.tacticExact_mod_cast_
            "exact_mod_cast"
            (Term.app
             `congr_arg
             [`Complex.re
              (Term.app `smul_eq_lc_row0_add [`z `hp (Term.proj `g "." (fieldIdx "2"))])]))])))
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
         [(Tactic.tacticSuffices_
           "suffices"
           (Term.sufficesDecl
            []
            (Term.app
             `tendsto
             [(Term.fun
               "fun"
               (Term.basicFun
                [`g]
                [(Term.typeSpec
                  ":"
                  (Set.Data.Set.Image.«term_⁻¹'_»
                   (Term.fun
                    "fun"
                    (Term.basicFun
                     [`g]
                     [(Term.typeSpec
                       ":"
                       (NumberTheory.Modular.«termSL(_,_)» "SL(" (num "2") ", " (termℤ "ℤ") ")"))]
                     "=>"
                     (Term.app (NumberTheory.Modular.«term↑ₘ_» "↑ₘ" `g) [(num "1")])))
                   " ⁻¹' "
                   («term{_}» "{" [`p] "}")))]
                "=>"
                (Term.proj
                 (Algebra.Group.Defs.«term_•_»
                  (Term.typeAscription
                   "("
                   `g
                   ":"
                   [(NumberTheory.Modular.«termSL(_,_)» "SL(" (num "2") ", " (termℤ "ℤ") ")")]
                   ")")
                  " • "
                  `z)
                 "."
                 `re)))
              `cofinite
              (Term.app `cocompact [(Data.Real.Basic.termℝ "ℝ")])])
            (Term.byTactic'
             "by"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(Tactic.exact "exact" (Term.app `tendsto_norm_cocompact_at_top.comp [`this]))])))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             []
             [(Term.typeSpec
               ":"
               («term_≠_»
                («term_⁻¹»
                 («term_+_»
                  («term_^_»
                   (Term.typeAscription
                    "("
                    (Term.app `p [(num "0")])
                    ":"
                    [(Data.Real.Basic.termℝ "ℝ")]
                    ")")
                   "^"
                   (num "2"))
                  "+"
                  («term_^_» (Term.app `p [(num "1")]) "^" (num "2")))
                 "⁻¹")
                "≠"
                (num "0")))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.apply "apply" `inv_ne_zero)
                 []
                 (Tactic.NormCast.tacticExact_mod_cast_
                  "exact_mod_cast"
                  `hp.sq_add_sq_ne_zero)]))))))
          []
          (Tactic.tacticLet_
           "let"
           (Term.letDecl
            (Term.letIdDecl
             `f
             []
             []
             ":="
             (Term.app `Homeomorph.mulRight₀ [(Term.hole "_") `this]))))
          []
          (Tactic.tacticLet_
           "let"
           (Term.letDecl
            (Term.letIdDecl
             `ff
             []
             []
             ":="
             (Term.app
              `Homeomorph.addRight
              [(Term.proj
                («term_/_»
                 («term_-_»
                  («term_*_»
                   (Term.typeAscription
                    "("
                    (Term.app `p [(num "1")])
                    ":"
                    [(Data.Complex.Basic.termℂ "ℂ")]
                    ")")
                   "*"
                   `z)
                  "-"
                  (Term.app `p [(num "0")]))
                 "/"
                 («term_*_»
                  («term_+_»
                   («term_^_» (Term.app `p [(num "0")]) "^" (num "2"))
                   "+"
                   («term_^_» (Term.app `p [(num "1")]) "^" (num "2")))
                  "*"
                  («term_+_»
                   («term_*_» (Term.app `p [(num "0")]) "*" `z)
                   "+"
                   (Term.app `p [(num "1")]))))
                "."
                `re)]))))
          []
          (convert
           "convert"
           []
           (Term.app
            (Term.proj
             (Term.proj
              (Term.proj (Term.app `f.trans [`ff]) "." `ClosedEmbedding)
              "."
              `tendsto_cocompact)
             "."
             `comp)
            [(Term.app `tendsto_lc_row0 [`hp])])
           [])
          []
          (Std.Tactic.Ext.«tacticExt___:_»
           "ext"
           [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `g))]
           [])
          []
          (Tactic.change
           "change"
           («term_=_»
            (Term.proj
             (Algebra.Group.Defs.«term_•_»
              (Term.typeAscription
               "("
               `g
               ":"
               [(NumberTheory.Modular.«termSL(_,_)» "SL(" (num "2") ", " (termℤ "ℤ") ")")]
               ")")
              " • "
              `z)
             "."
             `re)
            "="
            («term_+_»
             («term_/_»
              (Term.app
               `lc_row0
               [`p
                (coeNotation
                 "↑"
                 (Term.typeAscription
                  "("
                  (coeNotation "↑" `g)
                  ":"
                  [(NumberTheory.Modular.«termSL(_,_)»
                    "SL("
                    (num "2")
                    ", "
                    (Data.Real.Basic.termℝ "ℝ")
                    ")")]
                  ")"))])
              "/"
              («term_+_»
               («term_^_» (Term.app `p [(num "0")]) "^" (num "2"))
               "+"
               («term_^_» (Term.app `p [(num "1")]) "^" (num "2"))))
             "+"
             (Term.proj
              («term_/_»
               («term_-_»
                («term_*_»
                 (Term.typeAscription
                  "("
                  (Term.app `p [(num "1")])
                  ":"
                  [(Data.Complex.Basic.termℂ "ℂ")]
                  ")")
                 "*"
                 `z)
                "-"
                (Term.app `p [(num "0")]))
               "/"
               («term_*_»
                («term_+_»
                 («term_^_» (Term.app `p [(num "0")]) "^" (num "2"))
                 "+"
                 («term_^_» (Term.app `p [(num "1")]) "^" (num "2")))
                "*"
                («term_+_»
                 («term_*_» (Term.app `p [(num "0")]) "*" `z)
                 "+"
                 (Term.app `p [(num "1")]))))
              "."
              `re)))
           [])
          []
          (Tactic.NormCast.tacticExact_mod_cast_
           "exact_mod_cast"
           (Term.app
            `congr_arg
            [`Complex.re
             (Term.app `smul_eq_lc_row0_add [`z `hp (Term.proj `g "." (fieldIdx "2"))])]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.NormCast.tacticExact_mod_cast_
       "exact_mod_cast"
       (Term.app
        `congr_arg
        [`Complex.re (Term.app `smul_eq_lc_row0_add [`z `hp (Term.proj `g "." (fieldIdx "2"))])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `congr_arg
       [`Complex.re (Term.app `smul_eq_lc_row0_add [`z `hp (Term.proj `g "." (fieldIdx "2"))])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `smul_eq_lc_row0_add [`z `hp (Term.proj `g "." (fieldIdx "2"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `g "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `g
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hp
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `z
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `smul_eq_lc_row0_add
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `smul_eq_lc_row0_add [`z `hp (Term.proj `g "." (fieldIdx "2"))])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `Complex.re
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `congr_arg
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.change
       "change"
       («term_=_»
        (Term.proj
         (Algebra.Group.Defs.«term_•_»
          (Term.typeAscription
           "("
           `g
           ":"
           [(NumberTheory.Modular.«termSL(_,_)» "SL(" (num "2") ", " (termℤ "ℤ") ")")]
           ")")
          " • "
          `z)
         "."
         `re)
        "="
        («term_+_»
         («term_/_»
          (Term.app
           `lc_row0
           [`p
            (coeNotation
             "↑"
             (Term.typeAscription
              "("
              (coeNotation "↑" `g)
              ":"
              [(NumberTheory.Modular.«termSL(_,_)»
                "SL("
                (num "2")
                ", "
                (Data.Real.Basic.termℝ "ℝ")
                ")")]
              ")"))])
          "/"
          («term_+_»
           («term_^_» (Term.app `p [(num "0")]) "^" (num "2"))
           "+"
           («term_^_» (Term.app `p [(num "1")]) "^" (num "2"))))
         "+"
         (Term.proj
          («term_/_»
           («term_-_»
            («term_*_»
             (Term.typeAscription
              "("
              (Term.app `p [(num "1")])
              ":"
              [(Data.Complex.Basic.termℂ "ℂ")]
              ")")
             "*"
             `z)
            "-"
            (Term.app `p [(num "0")]))
           "/"
           («term_*_»
            («term_+_»
             («term_^_» (Term.app `p [(num "0")]) "^" (num "2"))
             "+"
             («term_^_» (Term.app `p [(num "1")]) "^" (num "2")))
            "*"
            («term_+_» («term_*_» (Term.app `p [(num "0")]) "*" `z) "+" (Term.app `p [(num "1")]))))
          "."
          `re)))
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Term.proj
        (Algebra.Group.Defs.«term_•_»
         (Term.typeAscription
          "("
          `g
          ":"
          [(NumberTheory.Modular.«termSL(_,_)» "SL(" (num "2") ", " (termℤ "ℤ") ")")]
          ")")
         " • "
         `z)
        "."
        `re)
       "="
       («term_+_»
        («term_/_»
         (Term.app
          `lc_row0
          [`p
           (coeNotation
            "↑"
            (Term.typeAscription
             "("
             (coeNotation "↑" `g)
             ":"
             [(NumberTheory.Modular.«termSL(_,_)»
               "SL("
               (num "2")
               ", "
               (Data.Real.Basic.termℝ "ℝ")
               ")")]
             ")"))])
         "/"
         («term_+_»
          («term_^_» (Term.app `p [(num "0")]) "^" (num "2"))
          "+"
          («term_^_» (Term.app `p [(num "1")]) "^" (num "2"))))
        "+"
        (Term.proj
         («term_/_»
          («term_-_»
           («term_*_»
            (Term.typeAscription
             "("
             (Term.app `p [(num "1")])
             ":"
             [(Data.Complex.Basic.termℂ "ℂ")]
             ")")
            "*"
            `z)
           "-"
           (Term.app `p [(num "0")]))
          "/"
          («term_*_»
           («term_+_»
            («term_^_» (Term.app `p [(num "0")]) "^" (num "2"))
            "+"
            («term_^_» (Term.app `p [(num "1")]) "^" (num "2")))
           "*"
           («term_+_» («term_*_» (Term.app `p [(num "0")]) "*" `z) "+" (Term.app `p [(num "1")]))))
         "."
         `re)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_»
       («term_/_»
        (Term.app
         `lc_row0
         [`p
          (coeNotation
           "↑"
           (Term.typeAscription
            "("
            (coeNotation "↑" `g)
            ":"
            [(NumberTheory.Modular.«termSL(_,_)»
              "SL("
              (num "2")
              ", "
              (Data.Real.Basic.termℝ "ℝ")
              ")")]
            ")"))])
        "/"
        («term_+_»
         («term_^_» (Term.app `p [(num "0")]) "^" (num "2"))
         "+"
         («term_^_» (Term.app `p [(num "1")]) "^" (num "2"))))
       "+"
       (Term.proj
        («term_/_»
         («term_-_»
          («term_*_»
           (Term.typeAscription
            "("
            (Term.app `p [(num "1")])
            ":"
            [(Data.Complex.Basic.termℂ "ℂ")]
            ")")
           "*"
           `z)
          "-"
          (Term.app `p [(num "0")]))
         "/"
         («term_*_»
          («term_+_»
           («term_^_» (Term.app `p [(num "0")]) "^" (num "2"))
           "+"
           («term_^_» (Term.app `p [(num "1")]) "^" (num "2")))
          "*"
          («term_+_» («term_*_» (Term.app `p [(num "0")]) "*" `z) "+" (Term.app `p [(num "1")]))))
        "."
        `re))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj
       («term_/_»
        («term_-_»
         («term_*_»
          (Term.typeAscription
           "("
           (Term.app `p [(num "1")])
           ":"
           [(Data.Complex.Basic.termℂ "ℂ")]
           ")")
          "*"
          `z)
         "-"
         (Term.app `p [(num "0")]))
        "/"
        («term_*_»
         («term_+_»
          («term_^_» (Term.app `p [(num "0")]) "^" (num "2"))
          "+"
          («term_^_» (Term.app `p [(num "1")]) "^" (num "2")))
         "*"
         («term_+_» («term_*_» (Term.app `p [(num "0")]) "*" `z) "+" (Term.app `p [(num "1")]))))
       "."
       `re)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      («term_/_»
       («term_-_»
        («term_*_»
         (Term.typeAscription
          "("
          (Term.app `p [(num "1")])
          ":"
          [(Data.Complex.Basic.termℂ "ℂ")]
          ")")
         "*"
         `z)
        "-"
        (Term.app `p [(num "0")]))
       "/"
       («term_*_»
        («term_+_»
         («term_^_» (Term.app `p [(num "0")]) "^" (num "2"))
         "+"
         («term_^_» (Term.app `p [(num "1")]) "^" (num "2")))
        "*"
        («term_+_» («term_*_» (Term.app `p [(num "0")]) "*" `z) "+" (Term.app `p [(num "1")]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_»
       («term_+_»
        («term_^_» (Term.app `p [(num "0")]) "^" (num "2"))
        "+"
        («term_^_» (Term.app `p [(num "1")]) "^" (num "2")))
       "*"
       («term_+_» («term_*_» (Term.app `p [(num "0")]) "*" `z) "+" (Term.app `p [(num "1")])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_» («term_*_» (Term.app `p [(num "0")]) "*" `z) "+" (Term.app `p [(num "1")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `p [(num "1")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      («term_*_» (Term.app `p [(num "0")]) "*" `z)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `z
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (Term.app `p [(num "0")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1022, (some 1023, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 65 >? 70, (some 71, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_+_» («term_*_» (Term.app `p [(num "0")]) "*" `z) "+" (Term.app `p [(num "1")]))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      («term_+_»
       («term_^_» (Term.app `p [(num "0")]) "^" (num "2"))
       "+"
       («term_^_» (Term.app `p [(num "1")]) "^" (num "2")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_» (Term.app `p [(num "1")]) "^" (num "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Term.app `p [(num "1")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1022, (some 1023, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      («term_^_» (Term.app `p [(num "0")]) "^" (num "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Term.app `p [(num "0")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1022, (some 1023, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 65 >? 80, (some 80, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 65, (some 66, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_+_»
      («term_^_» (Term.app `p [(num "0")]) "^" (num "2"))
      "+"
      («term_^_» (Term.app `p [(num "1")]) "^" (num "2")))
     ")")
[PrettyPrinter.parenthesize] ...precedences are 71 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_*_»
      (Term.paren
       "("
       («term_+_»
        («term_^_» (Term.app `p [(num "0")]) "^" (num "2"))
        "+"
        («term_^_» (Term.app `p [(num "1")]) "^" (num "2")))
       ")")
      "*"
      (Term.paren
       "("
       («term_+_» («term_*_» (Term.app `p [(num "0")]) "*" `z) "+" (Term.app `p [(num "1")]))
       ")"))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      («term_-_»
       («term_*_»
        (Term.typeAscription "(" (Term.app `p [(num "1")]) ":" [(Data.Complex.Basic.termℂ "ℂ")] ")")
        "*"
        `z)
       "-"
       (Term.app `p [(num "0")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `p [(num "0")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      («term_*_»
       (Term.typeAscription "(" (Term.app `p [(num "1")]) ":" [(Data.Complex.Basic.termℂ "ℂ")] ")")
       "*"
       `z)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `z
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (Term.typeAscription "(" (Term.app `p [(num "1")]) ":" [(Data.Complex.Basic.termℂ "ℂ")] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Complex.Basic.termℂ "ℂ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `p [(num "1")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 65 >? 70, (some 71, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 65, (some 66, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_-_»
      («term_*_»
       (Term.typeAscription "(" (Term.app `p [(num "1")]) ":" [(Data.Complex.Basic.termℂ "ℂ")] ")")
       "*"
       `z)
      "-"
      (Term.app `p [(num "0")]))
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 70, (some 71, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_/_»
      (Term.paren
       "("
       («term_-_»
        («term_*_»
         (Term.typeAscription
          "("
          (Term.app `p [(num "1")])
          ":"
          [(Data.Complex.Basic.termℂ "ℂ")]
          ")")
         "*"
         `z)
        "-"
        (Term.app `p [(num "0")]))
       ")")
      "/"
      (Term.paren
       "("
       («term_*_»
        (Term.paren
         "("
         («term_+_»
          («term_^_» (Term.app `p [(num "0")]) "^" (num "2"))
          "+"
          («term_^_» (Term.app `p [(num "1")]) "^" (num "2")))
         ")")
        "*"
        (Term.paren
         "("
         («term_+_» («term_*_» (Term.app `p [(num "0")]) "*" `z) "+" (Term.app `p [(num "1")]))
         ")"))
       ")"))
     ")")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      («term_/_»
       (Term.app
        `lc_row0
        [`p
         (coeNotation
          "↑"
          (Term.typeAscription
           "("
           (coeNotation "↑" `g)
           ":"
           [(NumberTheory.Modular.«termSL(_,_)»
             "SL("
             (num "2")
             ", "
             (Data.Real.Basic.termℝ "ℝ")
             ")")]
           ")"))])
       "/"
       («term_+_»
        («term_^_» (Term.app `p [(num "0")]) "^" (num "2"))
        "+"
        («term_^_» (Term.app `p [(num "1")]) "^" (num "2"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_»
       («term_^_» (Term.app `p [(num "0")]) "^" (num "2"))
       "+"
       («term_^_» (Term.app `p [(num "1")]) "^" (num "2")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_» (Term.app `p [(num "1")]) "^" (num "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Term.app `p [(num "1")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1022, (some 1023, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      («term_^_» (Term.app `p [(num "0")]) "^" (num "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Term.app `p [(num "0")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1022, (some 1023, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 65 >? 80, (some 80, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_+_»
      («term_^_» (Term.app `p [(num "0")]) "^" (num "2"))
      "+"
      («term_^_» (Term.app `p [(num "1")]) "^" (num "2")))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (Term.app
       `lc_row0
       [`p
        (coeNotation
         "↑"
         (Term.typeAscription
          "("
          (coeNotation "↑" `g)
          ":"
          [(NumberTheory.Modular.«termSL(_,_)»
            "SL("
            (num "2")
            ", "
            (Data.Real.Basic.termℝ "ℝ")
            ")")]
          ")"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'coeNotation', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'coeNotation', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (coeNotation
       "↑"
       (Term.typeAscription
        "("
        (coeNotation "↑" `g)
        ":"
        [(NumberTheory.Modular.«termSL(_,_)» "SL(" (num "2") ", " (Data.Real.Basic.termℝ "ℝ") ")")]
        ")"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription
       "("
       (coeNotation "↑" `g)
       ":"
       [(NumberTheory.Modular.«termSL(_,_)» "SL(" (num "2") ", " (Data.Real.Basic.termℝ "ℝ") ")")]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (NumberTheory.Modular.«termSL(_,_)» "SL(" (num "2") ", " (Data.Real.Basic.termℝ "ℝ") ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.Modular.«termSL(_,_)»', expected 'NumberTheory.Modular.termSL(_,_)._@.NumberTheory.Modular._hyg.8'
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
  tendsto_abs_re_smul
  { p : Fin 2 → ℤ } ( hp : IsCoprime p 0 p 1 )
    :
      Tendsto
        fun g : { g : SL( 2 , ℤ ) // ↑ₘ g 1 = p } => | ( g : SL( 2 , ℤ ) ) • z . re | cofinite atTop
  :=
    by
      suffices
          tendsto
              fun g : fun g : SL( 2 , ℤ ) => ↑ₘ g 1 ⁻¹' { p } => ( g : SL( 2 , ℤ ) ) • z . re
                cofinite
                cocompact ℝ
            by exact tendsto_norm_cocompact_at_top.comp this
        have
          : ( p 0 : ℝ ) ^ 2 + p 1 ^ 2 ⁻¹ ≠ 0
            :=
            by apply inv_ne_zero exact_mod_cast hp.sq_add_sq_ne_zero
        let f := Homeomorph.mulRight₀ _ this
        let ff := Homeomorph.addRight ( p 1 : ℂ ) * z - p 0 / p 0 ^ 2 + p 1 ^ 2 * p 0 * z + p 1 . re
        convert f.trans ff . ClosedEmbedding . tendsto_cocompact . comp tendsto_lc_row0 hp
        ext g
        change
          ( g : SL( 2 , ℤ ) ) • z . re
            =
            lc_row0 p ↑ ( ↑ g : SL( 2 , ℝ ) ) / p 0 ^ 2 + p 1 ^ 2
              +
              ( p 1 : ℂ ) * z - p 0 / p 0 ^ 2 + p 1 ^ 2 * p 0 * z + p 1 . re
        exact_mod_cast congr_arg Complex.re smul_eq_lc_row0_add z hp g . 2
#align modular_group.tendsto_abs_re_smul ModularGroup.tendsto_abs_re_smul

end TendstoLemmas

section FundamentalDomain

attribute [local simp] coe_smul re_smul

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment "/--" "For `z : ℍ`, there is a `g : SL(2,ℤ)` maximizing `(g•z).im` -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `exists_max_im [])
      (Command.declSig
       []
       (Term.typeSpec
        ":"
        («term∃_,_»
         "∃"
         (Lean.explicitBinders
          (Lean.unbracketedExplicitBinders
           [(Lean.binderIdent `g)]
           [":" (NumberTheory.Modular.«termSL(_,_)» "SL(" (num "2") ", " (termℤ "ℤ") ")")]))
         ","
         (Term.forall
          "∀"
          [`g']
          [(Term.typeSpec
            ":"
            (NumberTheory.Modular.«termSL(_,_)» "SL(" (num "2") ", " (termℤ "ℤ") ")"))]
          ","
          («term_≤_»
           (Term.proj (Algebra.Group.Defs.«term_•_» `g' " • " `z) "." `im)
           "≤"
           (Term.proj (Algebra.Group.Defs.«term_•_» `g " • " `z) "." `im))))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Mathlib.Tactic.tacticClassical_
            "classical"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.tacticLet_
                "let"
                (Term.letDecl
                 (Term.letIdDecl
                  `s
                  []
                  [(Term.typeSpec
                    ":"
                    (Term.app `Set [(Term.arrow (Term.app `Fin [(num "2")]) "→" (termℤ "ℤ"))]))]
                  ":="
                  (Set.«term{_|_}»
                   "{"
                   (Std.ExtendedBinder.extBinder (Lean.binderIdent `cd) [])
                   "|"
                   (Term.app `IsCoprime [(Term.app `cd [(num "0")]) (Term.app `cd [(num "1")])])
                   "}"))))
               []
               (Tactic.tacticHave_
                "have"
                (Term.haveDecl
                 (Term.haveIdDecl
                  [`hs []]
                  [(Term.typeSpec ":" `s.nonempty)]
                  ":="
                  (Term.anonymousCtor
                   "⟨"
                   [(Matrix.Data.Fin.VecNotation.«term![_,» "![" [(num "1") "," (num "1")] "]")
                    ","
                    `isCoprime_one_left]
                   "⟩"))))
               []
               (Std.Tactic.obtain
                "obtain"
                [(Std.Tactic.RCases.rcasesPatMed
                  [(Std.Tactic.RCases.rcasesPat.tuple
                    "⟨"
                    [(Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `p)])
                      [])
                     ","
                     (Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed
                       [(Std.Tactic.RCases.rcasesPat.one `hp_coprime)])
                      [])
                     ","
                     (Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hp)])
                      [])]
                    "⟩")])]
                []
                [":="
                 [(Term.app
                   `Filter.Tendsto.exists_within_forall_le
                   [`hs (Term.app `tendsto_norm_sq_coprime_pair [`z])])]])
               []
               (Std.Tactic.obtain
                "obtain"
                [(Std.Tactic.RCases.rcasesPatMed
                  [(Std.Tactic.RCases.rcasesPat.tuple
                    "⟨"
                    [(Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `g)])
                      [])
                     ","
                     (Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.clear "-")])
                      [])
                     ","
                     (Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hg)])
                      [])]
                    "⟩")])]
                []
                [":=" [(Term.app `bottom_row_surj [`hp_coprime])]])
               []
               (Tactic.refine'
                "refine'"
                (Term.anonymousCtor
                 "⟨"
                 [`g "," (Term.fun "fun" (Term.basicFun [`g'] [] "=>" (Term.hole "_")))]
                 "⟩"))
               []
               (Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule [] `special_linear_group.im_smul_eq_div_norm_sq)
                  ","
                  (Tactic.rwRule [] `special_linear_group.im_smul_eq_div_norm_sq)
                  ","
                  (Tactic.rwRule [] `div_le_div_left)]
                 "]")
                [])
               []
               (tactic__
                (cdotTk (patternIgnore (token.«· » "·")))
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
                     [(Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `hg)]
                     "]")]
                   ["using"
                    (Term.app
                     `hp
                     [(Term.app (NumberTheory.Modular.«term↑ₘ_» "↑ₘ" `g') [(num "1")])
                      (Term.app `bottom_row_coprime [`g'])])]))])
               []
               (tactic__
                (cdotTk (patternIgnore (token.«· » "·")))
                [(Tactic.exact "exact" `z.im_pos)])
               []
               (tactic__
                (cdotTk (patternIgnore (token.«· » "·")))
                [(Tactic.exact "exact" (Term.app `norm_sq_denom_pos [`g' `z]))])
               []
               (tactic__
                (cdotTk (patternIgnore (token.«· » "·")))
                [(Tactic.exact "exact" (Term.app `norm_sq_denom_pos [`g `z]))])])))])))
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
         [(Mathlib.Tactic.tacticClassical_
           "classical"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(Tactic.tacticLet_
               "let"
               (Term.letDecl
                (Term.letIdDecl
                 `s
                 []
                 [(Term.typeSpec
                   ":"
                   (Term.app `Set [(Term.arrow (Term.app `Fin [(num "2")]) "→" (termℤ "ℤ"))]))]
                 ":="
                 (Set.«term{_|_}»
                  "{"
                  (Std.ExtendedBinder.extBinder (Lean.binderIdent `cd) [])
                  "|"
                  (Term.app `IsCoprime [(Term.app `cd [(num "0")]) (Term.app `cd [(num "1")])])
                  "}"))))
              []
              (Tactic.tacticHave_
               "have"
               (Term.haveDecl
                (Term.haveIdDecl
                 [`hs []]
                 [(Term.typeSpec ":" `s.nonempty)]
                 ":="
                 (Term.anonymousCtor
                  "⟨"
                  [(Matrix.Data.Fin.VecNotation.«term![_,» "![" [(num "1") "," (num "1")] "]")
                   ","
                   `isCoprime_one_left]
                  "⟩"))))
              []
              (Std.Tactic.obtain
               "obtain"
               [(Std.Tactic.RCases.rcasesPatMed
                 [(Std.Tactic.RCases.rcasesPat.tuple
                   "⟨"
                   [(Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `p)])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed
                      [(Std.Tactic.RCases.rcasesPat.one `hp_coprime)])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hp)])
                     [])]
                   "⟩")])]
               []
               [":="
                [(Term.app
                  `Filter.Tendsto.exists_within_forall_le
                  [`hs (Term.app `tendsto_norm_sq_coprime_pair [`z])])]])
              []
              (Std.Tactic.obtain
               "obtain"
               [(Std.Tactic.RCases.rcasesPatMed
                 [(Std.Tactic.RCases.rcasesPat.tuple
                   "⟨"
                   [(Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `g)])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.clear "-")])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hg)])
                     [])]
                   "⟩")])]
               []
               [":=" [(Term.app `bottom_row_surj [`hp_coprime])]])
              []
              (Tactic.refine'
               "refine'"
               (Term.anonymousCtor
                "⟨"
                [`g "," (Term.fun "fun" (Term.basicFun [`g'] [] "=>" (Term.hole "_")))]
                "⟩"))
              []
              (Tactic.rwSeq
               "rw"
               []
               (Tactic.rwRuleSeq
                "["
                [(Tactic.rwRule [] `special_linear_group.im_smul_eq_div_norm_sq)
                 ","
                 (Tactic.rwRule [] `special_linear_group.im_smul_eq_div_norm_sq)
                 ","
                 (Tactic.rwRule [] `div_le_div_left)]
                "]")
               [])
              []
              (tactic__
               (cdotTk (patternIgnore (token.«· » "·")))
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
                    [(Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `hg)]
                    "]")]
                  ["using"
                   (Term.app
                    `hp
                    [(Term.app (NumberTheory.Modular.«term↑ₘ_» "↑ₘ" `g') [(num "1")])
                     (Term.app `bottom_row_coprime [`g'])])]))])
              []
              (tactic__
               (cdotTk (patternIgnore (token.«· » "·")))
               [(Tactic.exact "exact" `z.im_pos)])
              []
              (tactic__
               (cdotTk (patternIgnore (token.«· » "·")))
               [(Tactic.exact "exact" (Term.app `norm_sq_denom_pos [`g' `z]))])
              []
              (tactic__
               (cdotTk (patternIgnore (token.«· » "·")))
               [(Tactic.exact "exact" (Term.app `norm_sq_denom_pos [`g `z]))])])))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.tacticClassical_
       "classical"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.tacticLet_
           "let"
           (Term.letDecl
            (Term.letIdDecl
             `s
             []
             [(Term.typeSpec
               ":"
               (Term.app `Set [(Term.arrow (Term.app `Fin [(num "2")]) "→" (termℤ "ℤ"))]))]
             ":="
             (Set.«term{_|_}»
              "{"
              (Std.ExtendedBinder.extBinder (Lean.binderIdent `cd) [])
              "|"
              (Term.app `IsCoprime [(Term.app `cd [(num "0")]) (Term.app `cd [(num "1")])])
              "}"))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`hs []]
             [(Term.typeSpec ":" `s.nonempty)]
             ":="
             (Term.anonymousCtor
              "⟨"
              [(Matrix.Data.Fin.VecNotation.«term![_,» "![" [(num "1") "," (num "1")] "]")
               ","
               `isCoprime_one_left]
              "⟩"))))
          []
          (Std.Tactic.obtain
           "obtain"
           [(Std.Tactic.RCases.rcasesPatMed
             [(Std.Tactic.RCases.rcasesPat.tuple
               "⟨"
               [(Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `p)])
                 [])
                ","
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hp_coprime)])
                 [])
                ","
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hp)])
                 [])]
               "⟩")])]
           []
           [":="
            [(Term.app
              `Filter.Tendsto.exists_within_forall_le
              [`hs (Term.app `tendsto_norm_sq_coprime_pair [`z])])]])
          []
          (Std.Tactic.obtain
           "obtain"
           [(Std.Tactic.RCases.rcasesPatMed
             [(Std.Tactic.RCases.rcasesPat.tuple
               "⟨"
               [(Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `g)])
                 [])
                ","
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.clear "-")])
                 [])
                ","
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hg)])
                 [])]
               "⟩")])]
           []
           [":=" [(Term.app `bottom_row_surj [`hp_coprime])]])
          []
          (Tactic.refine'
           "refine'"
           (Term.anonymousCtor
            "⟨"
            [`g "," (Term.fun "fun" (Term.basicFun [`g'] [] "=>" (Term.hole "_")))]
            "⟩"))
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `special_linear_group.im_smul_eq_div_norm_sq)
             ","
             (Tactic.rwRule [] `special_linear_group.im_smul_eq_div_norm_sq)
             ","
             (Tactic.rwRule [] `div_le_div_left)]
            "]")
           [])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
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
                [(Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `hg)]
                "]")]
              ["using"
               (Term.app
                `hp
                [(Term.app (NumberTheory.Modular.«term↑ₘ_» "↑ₘ" `g') [(num "1")])
                 (Term.app `bottom_row_coprime [`g'])])]))])
          []
          (tactic__ (cdotTk (patternIgnore (token.«· » "·"))) [(Tactic.exact "exact" `z.im_pos)])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.exact "exact" (Term.app `norm_sq_denom_pos [`g' `z]))])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.exact "exact" (Term.app `norm_sq_denom_pos [`g `z]))])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.exact "exact" (Term.app `norm_sq_denom_pos [`g `z]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" (Term.app `norm_sq_denom_pos [`g `z]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `norm_sq_denom_pos [`g `z])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `z
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `norm_sq_denom_pos
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.exact "exact" (Term.app `norm_sq_denom_pos [`g' `z]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" (Term.app `norm_sq_denom_pos [`g' `z]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `norm_sq_denom_pos [`g' `z])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `z
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `g'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `norm_sq_denom_pos
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__ (cdotTk (patternIgnore (token.«· » "·"))) [(Tactic.exact "exact" `z.im_pos)])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" `z.im_pos)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `z.im_pos
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Std.Tactic.Simpa.simpa
         "simpa"
         []
         []
         (Std.Tactic.Simpa.simpaArgsRest
          []
          []
          []
          [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `hg)] "]")]
          ["using"
           (Term.app
            `hp
            [(Term.app (NumberTheory.Modular.«term↑ₘ_» "↑ₘ" `g') [(num "1")])
             (Term.app `bottom_row_coprime [`g'])])]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Simpa.simpa
       "simpa"
       []
       []
       (Std.Tactic.Simpa.simpaArgsRest
        []
        []
        []
        [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `hg)] "]")]
        ["using"
         (Term.app
          `hp
          [(Term.app (NumberTheory.Modular.«term↑ₘ_» "↑ₘ" `g') [(num "1")])
           (Term.app `bottom_row_coprime [`g'])])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `hp
       [(Term.app (NumberTheory.Modular.«term↑ₘ_» "↑ₘ" `g') [(num "1")])
        (Term.app `bottom_row_coprime [`g'])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `bottom_row_coprime [`g'])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `bottom_row_coprime
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `bottom_row_coprime [`g'])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app (NumberTheory.Modular.«term↑ₘ_» "↑ₘ" `g') [(num "1")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (NumberTheory.Modular.«term↑ₘ_» "↑ₘ" `g')
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.Modular.«term↑ₘ_»', expected 'NumberTheory.Modular.term↑ₘ_._@.NumberTheory.Modular._hyg.827'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/-- For `z : ℍ`, there is a `g : SL(2,ℤ)` maximizing `(g•z).im` -/
  theorem
    exists_max_im
    : ∃ g : SL( 2 , ℤ ) , ∀ g' : SL( 2 , ℤ ) , g' • z . im ≤ g • z . im
    :=
      by
        classical
          let s : Set Fin 2 → ℤ := { cd | IsCoprime cd 0 cd 1 }
            have hs : s.nonempty := ⟨ ![ 1 , 1 ] , isCoprime_one_left ⟩
            obtain
              ⟨ p , hp_coprime , hp ⟩
              := Filter.Tendsto.exists_within_forall_le hs tendsto_norm_sq_coprime_pair z
            obtain ⟨ g , - , hg ⟩ := bottom_row_surj hp_coprime
            refine' ⟨ g , fun g' => _ ⟩
            rw
              [
                special_linear_group.im_smul_eq_div_norm_sq
                  ,
                  special_linear_group.im_smul_eq_div_norm_sq
                  ,
                  div_le_div_left
                ]
            · simpa [ ← hg ] using hp ↑ₘ g' 1 bottom_row_coprime g'
            · exact z.im_pos
            · exact norm_sq_denom_pos g' z
            · exact norm_sq_denom_pos g z
#align modular_group.exists_max_im ModularGroup.exists_max_im

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "Given `z : ℍ` and a bottom row `(c,d)`, among the `g : SL(2,ℤ)` with this bottom row, minimize\n  `|(g•z).re|`.  -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `exists_row_one_eq_and_min_re [])
      (Command.declSig
       [(Term.implicitBinder
         "{"
         [`cd]
         [":" (Term.arrow (Term.app `Fin [(num "2")]) "→" (termℤ "ℤ"))]
         "}")
        (Term.explicitBinder
         "("
         [`hcd]
         [":" (Term.app `IsCoprime [(Term.app `cd [(num "0")]) (Term.app `cd [(num "1")])])]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term∃_,_»
         "∃"
         (Lean.explicitBinders
          (Lean.unbracketedExplicitBinders
           [(Lean.binderIdent `g)]
           [":" (NumberTheory.Modular.«termSL(_,_)» "SL(" (num "2") ", " (termℤ "ℤ") ")")]))
         ","
         («term_∧_»
          («term_=_» (Term.app (NumberTheory.Modular.«term↑ₘ_» "↑ₘ" `g) [(num "1")]) "=" `cd)
          "∧"
          (Term.forall
           "∀"
           [`g']
           [(Term.typeSpec
             ":"
             (NumberTheory.Modular.«termSL(_,_)» "SL(" (num "2") ", " (termℤ "ℤ") ")"))]
           ","
           (Term.arrow
            («term_=_»
             (Term.app (NumberTheory.Modular.«term↑ₘ_» "↑ₘ" `g) [(num "1")])
             "="
             (Term.app (NumberTheory.Modular.«term↑ₘ_» "↑ₘ" `g') [(num "1")]))
            "→"
            («term_≤_»
             («term|___|»
              (group "|")
              (Term.proj (Algebra.Group.Defs.«term_•_» `g " • " `z) "." `re)
              (group)
              "|")
             "≤"
             («term|___|»
              (group "|")
              (Term.proj (Algebra.Group.Defs.«term_•_» `g' " • " `z) "." `re)
              (group)
              "|"))))))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Std.Tactic.tacticHaveI_
            "haveI"
            (Term.haveDecl
             (Term.haveIdDecl
              []
              [(Term.typeSpec
                ":"
                (Term.app
                 `Nonempty
                 [(«term{_:_//_}»
                   "{"
                   `g
                   [":" (NumberTheory.Modular.«termSL(_,_)» "SL(" (num "2") ", " (termℤ "ℤ") ")")]
                   "//"
                   («term_=_»
                    (Term.app (NumberTheory.Modular.«term↑ₘ_» "↑ₘ" `g) [(num "1")])
                    "="
                    `cd)
                   "}")]))]
              ":="
              (Term.let
               "let"
               (Term.letDecl
                (Term.letPatDecl
                 (Term.anonymousCtor "⟨" [`x "," `hx] "⟩")
                 []
                 []
                 ":="
                 (Term.app `bottom_row_surj [`hcd])))
               []
               (Term.anonymousCtor
                "⟨"
                [(Term.anonymousCtor "⟨" [`x "," (Term.proj `hx "." (fieldIdx "2"))] "⟩")]
                "⟩")))))
           []
           (Std.Tactic.obtain
            "obtain"
            [(Std.Tactic.RCases.rcasesPatMed
              [(Std.Tactic.RCases.rcasesPat.tuple
                "⟨"
                [(Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `g)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hg)])
                  [])]
                "⟩")])]
            []
            [":="
             [(Term.app
               `Filter.Tendsto.exists_forall_le
               [(Term.app `tendsto_abs_re_smul [`z `hcd])])]])
           []
           (Tactic.refine'
            "refine'"
            (Term.anonymousCtor
             "⟨"
             [`g "," (Term.proj `g "." (fieldIdx "2")) "," (Term.hole "_")]
             "⟩"))
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.intro "intro" [`g1 `hg1])
             []
             (Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                []
                [(Term.typeSpec
                  ":"
                  («term_∈_»
                   `g1
                   "∈"
                   (Set.Data.Set.Image.«term_⁻¹'_»
                    (Term.fun
                     "fun"
                     (Term.basicFun
                      [`g]
                      [(Term.typeSpec
                        ":"
                        (NumberTheory.Modular.«termSL(_,_)» "SL(" (num "2") ", " (termℤ "ℤ") ")"))]
                      "=>"
                      (Term.app (NumberTheory.Modular.«term↑ₘ_» "↑ₘ" `g) [(num "1")])))
                    " ⁻¹' "
                    («term{_}» "{" [`cd] "}"))))]
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
                      [(Tactic.rwRule [] `Set.mem_preimage)
                       ","
                       (Tactic.rwRule [] `Set.mem_singleton_iff)]
                      "]")
                     [])
                    []
                    (Tactic.exact
                     "exact"
                     (Term.app
                      `Eq.trans
                      [`hg1.symm
                       (Term.app
                        `set.mem_singleton_iff.mp
                        [(Term.app
                          `set.mem_preimage.mp
                          [(Term.proj `g "." (fieldIdx "2"))])])]))]))))))
             []
             (Tactic.exact
              "exact"
              (Term.app `hg [(Term.anonymousCtor "⟨" [`g1 "," `this] "⟩")]))])])))
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
         [(Std.Tactic.tacticHaveI_
           "haveI"
           (Term.haveDecl
            (Term.haveIdDecl
             []
             [(Term.typeSpec
               ":"
               (Term.app
                `Nonempty
                [(«term{_:_//_}»
                  "{"
                  `g
                  [":" (NumberTheory.Modular.«termSL(_,_)» "SL(" (num "2") ", " (termℤ "ℤ") ")")]
                  "//"
                  («term_=_»
                   (Term.app (NumberTheory.Modular.«term↑ₘ_» "↑ₘ" `g) [(num "1")])
                   "="
                   `cd)
                  "}")]))]
             ":="
             (Term.let
              "let"
              (Term.letDecl
               (Term.letPatDecl
                (Term.anonymousCtor "⟨" [`x "," `hx] "⟩")
                []
                []
                ":="
                (Term.app `bottom_row_surj [`hcd])))
              []
              (Term.anonymousCtor
               "⟨"
               [(Term.anonymousCtor "⟨" [`x "," (Term.proj `hx "." (fieldIdx "2"))] "⟩")]
               "⟩")))))
          []
          (Std.Tactic.obtain
           "obtain"
           [(Std.Tactic.RCases.rcasesPatMed
             [(Std.Tactic.RCases.rcasesPat.tuple
               "⟨"
               [(Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `g)])
                 [])
                ","
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hg)])
                 [])]
               "⟩")])]
           []
           [":="
            [(Term.app
              `Filter.Tendsto.exists_forall_le
              [(Term.app `tendsto_abs_re_smul [`z `hcd])])]])
          []
          (Tactic.refine'
           "refine'"
           (Term.anonymousCtor
            "⟨"
            [`g "," (Term.proj `g "." (fieldIdx "2")) "," (Term.hole "_")]
            "⟩"))
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.intro "intro" [`g1 `hg1])
            []
            (Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               []
               [(Term.typeSpec
                 ":"
                 («term_∈_»
                  `g1
                  "∈"
                  (Set.Data.Set.Image.«term_⁻¹'_»
                   (Term.fun
                    "fun"
                    (Term.basicFun
                     [`g]
                     [(Term.typeSpec
                       ":"
                       (NumberTheory.Modular.«termSL(_,_)» "SL(" (num "2") ", " (termℤ "ℤ") ")"))]
                     "=>"
                     (Term.app (NumberTheory.Modular.«term↑ₘ_» "↑ₘ" `g) [(num "1")])))
                   " ⁻¹' "
                   («term{_}» "{" [`cd] "}"))))]
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
                     [(Tactic.rwRule [] `Set.mem_preimage)
                      ","
                      (Tactic.rwRule [] `Set.mem_singleton_iff)]
                     "]")
                    [])
                   []
                   (Tactic.exact
                    "exact"
                    (Term.app
                     `Eq.trans
                     [`hg1.symm
                      (Term.app
                       `set.mem_singleton_iff.mp
                       [(Term.app
                         `set.mem_preimage.mp
                         [(Term.proj `g "." (fieldIdx "2"))])])]))]))))))
            []
            (Tactic.exact
             "exact"
             (Term.app `hg [(Term.anonymousCtor "⟨" [`g1 "," `this] "⟩")]))])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.intro "intro" [`g1 `hg1])
        []
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           []
           [(Term.typeSpec
             ":"
             («term_∈_»
              `g1
              "∈"
              (Set.Data.Set.Image.«term_⁻¹'_»
               (Term.fun
                "fun"
                (Term.basicFun
                 [`g]
                 [(Term.typeSpec
                   ":"
                   (NumberTheory.Modular.«termSL(_,_)» "SL(" (num "2") ", " (termℤ "ℤ") ")"))]
                 "=>"
                 (Term.app (NumberTheory.Modular.«term↑ₘ_» "↑ₘ" `g) [(num "1")])))
               " ⁻¹' "
               («term{_}» "{" [`cd] "}"))))]
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
                 [(Tactic.rwRule [] `Set.mem_preimage)
                  ","
                  (Tactic.rwRule [] `Set.mem_singleton_iff)]
                 "]")
                [])
               []
               (Tactic.exact
                "exact"
                (Term.app
                 `Eq.trans
                 [`hg1.symm
                  (Term.app
                   `set.mem_singleton_iff.mp
                   [(Term.app `set.mem_preimage.mp [(Term.proj `g "." (fieldIdx "2"))])])]))]))))))
        []
        (Tactic.exact "exact" (Term.app `hg [(Term.anonymousCtor "⟨" [`g1 "," `this] "⟩")]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" (Term.app `hg [(Term.anonymousCtor "⟨" [`g1 "," `this] "⟩")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `hg [(Term.anonymousCtor "⟨" [`g1 "," `this] "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [`g1 "," `this] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `this
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g1
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `hg
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
           («term_∈_»
            `g1
            "∈"
            (Set.Data.Set.Image.«term_⁻¹'_»
             (Term.fun
              "fun"
              (Term.basicFun
               [`g]
               [(Term.typeSpec
                 ":"
                 (NumberTheory.Modular.«termSL(_,_)» "SL(" (num "2") ", " (termℤ "ℤ") ")"))]
               "=>"
               (Term.app (NumberTheory.Modular.«term↑ₘ_» "↑ₘ" `g) [(num "1")])))
             " ⁻¹' "
             («term{_}» "{" [`cd] "}"))))]
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
               [(Tactic.rwRule [] `Set.mem_preimage) "," (Tactic.rwRule [] `Set.mem_singleton_iff)]
               "]")
              [])
             []
             (Tactic.exact
              "exact"
              (Term.app
               `Eq.trans
               [`hg1.symm
                (Term.app
                 `set.mem_singleton_iff.mp
                 [(Term.app `set.mem_preimage.mp [(Term.proj `g "." (fieldIdx "2"))])])]))]))))))
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
            [(Tactic.rwRule [] `Set.mem_preimage) "," (Tactic.rwRule [] `Set.mem_singleton_iff)]
            "]")
           [])
          []
          (Tactic.exact
           "exact"
           (Term.app
            `Eq.trans
            [`hg1.symm
             (Term.app
              `set.mem_singleton_iff.mp
              [(Term.app `set.mem_preimage.mp [(Term.proj `g "." (fieldIdx "2"))])])]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.app
        `Eq.trans
        [`hg1.symm
         (Term.app
          `set.mem_singleton_iff.mp
          [(Term.app `set.mem_preimage.mp [(Term.proj `g "." (fieldIdx "2"))])])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Eq.trans
       [`hg1.symm
        (Term.app
         `set.mem_singleton_iff.mp
         [(Term.app `set.mem_preimage.mp [(Term.proj `g "." (fieldIdx "2"))])])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `set.mem_singleton_iff.mp
       [(Term.app `set.mem_preimage.mp [(Term.proj `g "." (fieldIdx "2"))])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `set.mem_preimage.mp [(Term.proj `g "." (fieldIdx "2"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `g "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `g
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `set.mem_preimage.mp
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `set.mem_preimage.mp [(Term.proj `g "." (fieldIdx "2"))])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `set.mem_singleton_iff.mp
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `set.mem_singleton_iff.mp
      [(Term.paren "(" (Term.app `set.mem_preimage.mp [(Term.proj `g "." (fieldIdx "2"))]) ")")])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hg1.symm
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Eq.trans
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
        [(Tactic.rwRule [] `Set.mem_preimage) "," (Tactic.rwRule [] `Set.mem_singleton_iff)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Set.mem_singleton_iff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Set.mem_preimage
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∈_»
       `g1
       "∈"
       (Set.Data.Set.Image.«term_⁻¹'_»
        (Term.fun
         "fun"
         (Term.basicFun
          [`g]
          [(Term.typeSpec
            ":"
            (NumberTheory.Modular.«termSL(_,_)» "SL(" (num "2") ", " (termℤ "ℤ") ")"))]
          "=>"
          (Term.app (NumberTheory.Modular.«term↑ₘ_» "↑ₘ" `g) [(num "1")])))
        " ⁻¹' "
        («term{_}» "{" [`cd] "}")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Set.Data.Set.Image.«term_⁻¹'_»
       (Term.fun
        "fun"
        (Term.basicFun
         [`g]
         [(Term.typeSpec
           ":"
           (NumberTheory.Modular.«termSL(_,_)» "SL(" (num "2") ", " (termℤ "ℤ") ")"))]
         "=>"
         (Term.app (NumberTheory.Modular.«term↑ₘ_» "↑ₘ" `g) [(num "1")])))
       " ⁻¹' "
       («term{_}» "{" [`cd] "}"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term{_}» "{" [`cd] "}")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `cd
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Term.fun
       "fun"
       (Term.basicFun
        [`g]
        [(Term.typeSpec
          ":"
          (NumberTheory.Modular.«termSL(_,_)» "SL(" (num "2") ", " (termℤ "ℤ") ")"))]
        "=>"
        (Term.app (NumberTheory.Modular.«term↑ₘ_» "↑ₘ" `g) [(num "1")])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (NumberTheory.Modular.«term↑ₘ_» "↑ₘ" `g) [(num "1")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (NumberTheory.Modular.«term↑ₘ_» "↑ₘ" `g)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.Modular.«term↑ₘ_»', expected 'NumberTheory.Modular.term↑ₘ_._@.NumberTheory.Modular._hyg.827'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts'
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
/--
    Given `z : ℍ` and a bottom row `(c,d)`, among the `g : SL(2,ℤ)` with this bottom row, minimize
      `|(g•z).re|`.  -/
  theorem
    exists_row_one_eq_and_min_re
    { cd : Fin 2 → ℤ } ( hcd : IsCoprime cd 0 cd 1 )
      :
        ∃
          g : SL( 2 , ℤ )
          ,
          ↑ₘ g 1 = cd ∧ ∀ g' : SL( 2 , ℤ ) , ↑ₘ g 1 = ↑ₘ g' 1 → | g • z . re | ≤ | g' • z . re |
    :=
      by
        haveI
            : Nonempty { g : SL( 2 , ℤ ) // ↑ₘ g 1 = cd }
              :=
              let ⟨ x , hx ⟩ := bottom_row_surj hcd ⟨ ⟨ x , hx . 2 ⟩ ⟩
          obtain ⟨ g , hg ⟩ := Filter.Tendsto.exists_forall_le tendsto_abs_re_smul z hcd
          refine' ⟨ g , g . 2 , _ ⟩
          ·
            intro g1 hg1
              have
                : g1 ∈ fun g : SL( 2 , ℤ ) => ↑ₘ g 1 ⁻¹' { cd }
                  :=
                  by
                    rw [ Set.mem_preimage , Set.mem_singleton_iff ]
                      exact Eq.trans hg1.symm set.mem_singleton_iff.mp set.mem_preimage.mp g . 2
              exact hg ⟨ g1 , this ⟩
#align modular_group.exists_row_one_eq_and_min_re ModularGroup.exists_row_one_eq_and_min_re

/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr!![ » -/
/- ./././Mathport/Syntax/Translate/Expr.lean:390:14: unsupported user notation matrix.notation -/
/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment "/--" "The matrix `T = [[1,1],[0,1]]` as an element of `SL(2,ℤ)` -/")]
      []
      []
      []
      []
      [])
     (Command.def
      "def"
      (Command.declId `t [])
      (Command.optDeclSig
       []
       [(Term.typeSpec
         ":"
         (NumberTheory.Modular.«termSL(_,_)» "SL(" (num "2") ", " (termℤ "ℤ") ")"))])
      (Command.declValSimple
       ":="
       (Term.anonymousCtor
        "⟨"
        [(Term.app
          `«expr!![ »
          [(str
            "\"./././Mathport/Syntax/Translate/Expr.lean:390:14: unsupported user notation matrix.notation\"")])
         ","
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Mathlib.Tactic.normNum
              "norm_num"
              []
              [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `Matrix.det_fin_two_of)] "]")]
              [])])))]
        "⟩")
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.app
         `«expr!![ »
         [(str
           "\"./././Mathport/Syntax/Translate/Expr.lean:390:14: unsupported user notation matrix.notation\"")])
        ","
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Mathlib.Tactic.normNum
             "norm_num"
             []
             [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `Matrix.det_fin_two_of)] "]")]
             [])])))]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Mathlib.Tactic.normNum
           "norm_num"
           []
           [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `Matrix.det_fin_two_of)] "]")]
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.normNum
       "norm_num"
       []
       [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `Matrix.det_fin_two_of)] "]")]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Matrix.det_fin_two_of
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `«expr!![ »
       [(str
         "\"./././Mathport/Syntax/Translate/Expr.lean:390:14: unsupported user notation matrix.notation\"")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'str', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'str', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (str
       "\"./././Mathport/Syntax/Translate/Expr.lean:390:14: unsupported user notation matrix.notation\"")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `«expr!![ »
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (NumberTheory.Modular.«termSL(_,_)» "SL(" (num "2") ", " (termℤ "ℤ") ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.Modular.«termSL(_,_)»', expected 'NumberTheory.Modular.termSL(_,_)._@.NumberTheory.Modular._hyg.8'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/-- The matrix `T = [[1,1],[0,1]]` as an element of `SL(2,ℤ)` -/
  def
    t
    : SL( 2 , ℤ )
    :=
      ⟨
        «expr!![ »
            "./././Mathport/Syntax/Translate/Expr.lean:390:14: unsupported user notation matrix.notation"
          ,
          by norm_num [ Matrix.det_fin_two_of ]
        ⟩
#align modular_group.T ModularGroup.t

/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr!![ » -/
/- ./././Mathport/Syntax/Translate/Expr.lean:390:14: unsupported user notation matrix.notation -/
/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment "/--" "The matrix `S = [[0,-1],[1,0]]` as an element of `SL(2,ℤ)` -/")]
      []
      []
      []
      []
      [])
     (Command.def
      "def"
      (Command.declId `s [])
      (Command.optDeclSig
       []
       [(Term.typeSpec
         ":"
         (NumberTheory.Modular.«termSL(_,_)» "SL(" (num "2") ", " (termℤ "ℤ") ")"))])
      (Command.declValSimple
       ":="
       (Term.anonymousCtor
        "⟨"
        [(Term.app
          `«expr!![ »
          [(str
            "\"./././Mathport/Syntax/Translate/Expr.lean:390:14: unsupported user notation matrix.notation\"")])
         ","
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Mathlib.Tactic.normNum
              "norm_num"
              []
              [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `Matrix.det_fin_two_of)] "]")]
              [])])))]
        "⟩")
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.app
         `«expr!![ »
         [(str
           "\"./././Mathport/Syntax/Translate/Expr.lean:390:14: unsupported user notation matrix.notation\"")])
        ","
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Mathlib.Tactic.normNum
             "norm_num"
             []
             [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `Matrix.det_fin_two_of)] "]")]
             [])])))]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Mathlib.Tactic.normNum
           "norm_num"
           []
           [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `Matrix.det_fin_two_of)] "]")]
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.normNum
       "norm_num"
       []
       [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `Matrix.det_fin_two_of)] "]")]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Matrix.det_fin_two_of
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `«expr!![ »
       [(str
         "\"./././Mathport/Syntax/Translate/Expr.lean:390:14: unsupported user notation matrix.notation\"")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'str', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'str', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (str
       "\"./././Mathport/Syntax/Translate/Expr.lean:390:14: unsupported user notation matrix.notation\"")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `«expr!![ »
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (NumberTheory.Modular.«termSL(_,_)» "SL(" (num "2") ", " (termℤ "ℤ") ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.Modular.«termSL(_,_)»', expected 'NumberTheory.Modular.termSL(_,_)._@.NumberTheory.Modular._hyg.8'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/-- The matrix `S = [[0,-1],[1,0]]` as an element of `SL(2,ℤ)` -/
  def
    s
    : SL( 2 , ℤ )
    :=
      ⟨
        «expr!![ »
            "./././Mathport/Syntax/Translate/Expr.lean:390:14: unsupported user notation matrix.notation"
          ,
          by norm_num [ Matrix.det_fin_two_of ]
        ⟩
#align modular_group.S ModularGroup.s

/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr!![ » -/
/- ./././Mathport/Syntax/Translate/Expr.lean:390:14: unsupported user notation matrix.notation -/
/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `coe_S [])
      (Command.declSig
       []
       (Term.typeSpec
        ":"
        («term_=_»
         (NumberTheory.Modular.«term↑ₘ_» "↑ₘ" `S)
         "="
         (Term.app
          `«expr!![ »
          [(str
            "\"./././Mathport/Syntax/Translate/Expr.lean:390:14: unsupported user notation matrix.notation\"")]))))
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
       (NumberTheory.Modular.«term↑ₘ_» "↑ₘ" `S)
       "="
       (Term.app
        `«expr!![ »
        [(str
          "\"./././Mathport/Syntax/Translate/Expr.lean:390:14: unsupported user notation matrix.notation\"")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `«expr!![ »
       [(str
         "\"./././Mathport/Syntax/Translate/Expr.lean:390:14: unsupported user notation matrix.notation\"")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'str', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'str', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (str
       "\"./././Mathport/Syntax/Translate/Expr.lean:390:14: unsupported user notation matrix.notation\"")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `«expr!![ »
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (NumberTheory.Modular.«term↑ₘ_» "↑ₘ" `S)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.Modular.«term↑ₘ_»', expected 'NumberTheory.Modular.term↑ₘ_._@.NumberTheory.Modular._hyg.827'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  coe_S
  :
    ↑ₘ S
      =
      «expr!![ »
        "./././Mathport/Syntax/Translate/Expr.lean:390:14: unsupported user notation matrix.notation"
  := rfl
#align modular_group.coe_S ModularGroup.coe_S

/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr!![ » -/
/- ./././Mathport/Syntax/Translate/Expr.lean:390:14: unsupported user notation matrix.notation -/
/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `coe_T [])
      (Command.declSig
       []
       (Term.typeSpec
        ":"
        («term_=_»
         (NumberTheory.Modular.«term↑ₘ_» "↑ₘ" `T)
         "="
         (Term.app
          `«expr!![ »
          [(str
            "\"./././Mathport/Syntax/Translate/Expr.lean:390:14: unsupported user notation matrix.notation\"")]))))
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
       (NumberTheory.Modular.«term↑ₘ_» "↑ₘ" `T)
       "="
       (Term.app
        `«expr!![ »
        [(str
          "\"./././Mathport/Syntax/Translate/Expr.lean:390:14: unsupported user notation matrix.notation\"")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `«expr!![ »
       [(str
         "\"./././Mathport/Syntax/Translate/Expr.lean:390:14: unsupported user notation matrix.notation\"")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'str', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'str', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (str
       "\"./././Mathport/Syntax/Translate/Expr.lean:390:14: unsupported user notation matrix.notation\"")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `«expr!![ »
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (NumberTheory.Modular.«term↑ₘ_» "↑ₘ" `T)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.Modular.«term↑ₘ_»', expected 'NumberTheory.Modular.term↑ₘ_._@.NumberTheory.Modular._hyg.827'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  coe_T
  :
    ↑ₘ T
      =
      «expr!![ »
        "./././Mathport/Syntax/Translate/Expr.lean:390:14: unsupported user notation matrix.notation"
  := rfl
#align modular_group.coe_T ModularGroup.coe_T

/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr!![ » -/
/- ./././Mathport/Syntax/Translate/Expr.lean:390:14: unsupported user notation matrix.notation -/
/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `coe_T_inv [])
      (Command.declSig
       []
       (Term.typeSpec
        ":"
        («term_=_»
         (NumberTheory.Modular.«term↑ₘ_» "↑ₘ" («term_⁻¹» `T "⁻¹"))
         "="
         (Term.app
          `«expr!![ »
          [(str
            "\"./././Mathport/Syntax/Translate/Expr.lean:390:14: unsupported user notation matrix.notation\"")]))))
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
             [(Tactic.simpLemma [] [] `coe_inv)
              ","
              (Tactic.simpLemma [] [] `coe_T)
              ","
              (Tactic.simpLemma [] [] `adjugate_fin_two)]
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
            [(Tactic.simpLemma [] [] `coe_inv)
             ","
             (Tactic.simpLemma [] [] `coe_T)
             ","
             (Tactic.simpLemma [] [] `adjugate_fin_two)]
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
        [(Tactic.simpLemma [] [] `coe_inv)
         ","
         (Tactic.simpLemma [] [] `coe_T)
         ","
         (Tactic.simpLemma [] [] `adjugate_fin_two)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `adjugate_fin_two
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `coe_T
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `coe_inv
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (NumberTheory.Modular.«term↑ₘ_» "↑ₘ" («term_⁻¹» `T "⁻¹"))
       "="
       (Term.app
        `«expr!![ »
        [(str
          "\"./././Mathport/Syntax/Translate/Expr.lean:390:14: unsupported user notation matrix.notation\"")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `«expr!![ »
       [(str
         "\"./././Mathport/Syntax/Translate/Expr.lean:390:14: unsupported user notation matrix.notation\"")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'str', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'str', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (str
       "\"./././Mathport/Syntax/Translate/Expr.lean:390:14: unsupported user notation matrix.notation\"")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `«expr!![ »
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (NumberTheory.Modular.«term↑ₘ_» "↑ₘ" («term_⁻¹» `T "⁻¹"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.Modular.«term↑ₘ_»', expected 'NumberTheory.Modular.term↑ₘ_._@.NumberTheory.Modular._hyg.827'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  coe_T_inv
  :
    ↑ₘ T ⁻¹
      =
      «expr!![ »
        "./././Mathport/Syntax/Translate/Expr.lean:390:14: unsupported user notation matrix.notation"
  := by simp [ coe_inv , coe_T , adjugate_fin_two ]
#align modular_group.coe_T_inv ModularGroup.coe_T_inv

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:76:14: unsupported tactic `congrm #[[expr «expr!![ »(matrix.notation [expr _, ",", expr _, ";", expr _, ",", expr _, "]"] [])]] -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:76:14: unsupported tactic `congrm #[[expr «expr!![ »(matrix.notation [expr _, ",", expr _, ";", expr _, ",", expr _, "]"] [])]] -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr!![ » -/
/- ./././Mathport/Syntax/Translate/Expr.lean:390:14: unsupported user notation matrix.notation -/
/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `coe_T_zpow [])
      (Command.declSig
       [(Term.explicitBinder "(" [`n] [":" (termℤ "ℤ")] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (NumberTheory.Modular.«term↑ₘ_» "↑ₘ" («term_^_» `T "^" `n))
         "="
         (Term.app
          `«expr!![ »
          [(str
            "\"./././Mathport/Syntax/Translate/Expr.lean:390:14: unsupported user notation matrix.notation\"")]))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.induction'
            "induction'"
            [(Tactic.casesTarget [] `n)]
            ["using" `Int.induction_on]
            ["with"
             [(Lean.binderIdent `n)
              (Lean.binderIdent `h)
              (Lean.binderIdent `n)
              (Lean.binderIdent `h)]]
            [])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [] `zpow_zero)
                ","
                (Tactic.rwRule [] `coe_one)
                ","
                (Tactic.rwRule [] `Matrix.one_fin_two)]
               "]")
              [])])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Mathlib.Tactic.tacticSimp_rw__
              "simp_rw"
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [] `zpow_add)
                ","
                (Tactic.rwRule [] `zpow_one)
                ","
                (Tactic.rwRule [] `coe_mul)
                ","
                (Tactic.rwRule [] `h)
                ","
                (Tactic.rwRule [] `coe_T)
                ","
                (Tactic.rwRule [] `Matrix.mul_fin_two)]
               "]")
              [])
             []
             (choice
              (Tactic.trace
               "trace"
               (str
                "\"./././Mathport/Syntax/Translate/Tactic/Builtin.lean:76:14: unsupported tactic `congrm #[[expr «expr!![ »(matrix.notation [expr _, \\\",\\\", expr _, \\\";\\\", expr _, \\\",\\\", expr _, \\\"]\\\"] [])]]\""))
              (Tactic.traceMessage
               "trace"
               (str
                "\"./././Mathport/Syntax/Translate/Tactic/Builtin.lean:76:14: unsupported tactic `congrm #[[expr «expr!![ »(matrix.notation [expr _, \\\",\\\", expr _, \\\";\\\", expr _, \\\",\\\", expr _, \\\"]\\\"] [])]]\"")))
             []
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [] `mul_one)
                ","
                (Tactic.rwRule [] `mul_one)
                ","
                (Tactic.rwRule [] `add_comm)]
               "]")
              [])])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Mathlib.Tactic.tacticSimp_rw__
              "simp_rw"
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [] `zpow_sub)
                ","
                (Tactic.rwRule [] `zpow_one)
                ","
                (Tactic.rwRule [] `coe_mul)
                ","
                (Tactic.rwRule [] `h)
                ","
                (Tactic.rwRule [] `coe_T_inv)
                ","
                (Tactic.rwRule [] `Matrix.mul_fin_two)]
               "]")
              [])
             []
             (Tactic.«tactic_<;>_»
              (choice
               (Tactic.trace
                "trace"
                (str
                 "\"./././Mathport/Syntax/Translate/Tactic/Builtin.lean:76:14: unsupported tactic `congrm #[[expr «expr!![ »(matrix.notation [expr _, \\\",\\\", expr _, \\\";\\\", expr _, \\\",\\\", expr _, \\\"]\\\"] [])]]\""))
               (Tactic.traceMessage
                "trace"
                (str
                 "\"./././Mathport/Syntax/Translate/Tactic/Builtin.lean:76:14: unsupported tactic `congrm #[[expr «expr!![ »(matrix.notation [expr _, \\\",\\\", expr _, \\\";\\\", expr _, \\\",\\\", expr _, \\\"]\\\"] [])]]\"")))
              "<;>"
              (Mathlib.Tactic.RingNF.ring "ring"))])])))
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
           [(Tactic.casesTarget [] `n)]
           ["using" `Int.induction_on]
           ["with"
            [(Lean.binderIdent `n)
             (Lean.binderIdent `h)
             (Lean.binderIdent `n)
             (Lean.binderIdent `h)]]
           [])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] `zpow_zero)
               ","
               (Tactic.rwRule [] `coe_one)
               ","
               (Tactic.rwRule [] `Matrix.one_fin_two)]
              "]")
             [])])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Mathlib.Tactic.tacticSimp_rw__
             "simp_rw"
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] `zpow_add)
               ","
               (Tactic.rwRule [] `zpow_one)
               ","
               (Tactic.rwRule [] `coe_mul)
               ","
               (Tactic.rwRule [] `h)
               ","
               (Tactic.rwRule [] `coe_T)
               ","
               (Tactic.rwRule [] `Matrix.mul_fin_two)]
              "]")
             [])
            []
            (choice
             (Tactic.trace
              "trace"
              (str
               "\"./././Mathport/Syntax/Translate/Tactic/Builtin.lean:76:14: unsupported tactic `congrm #[[expr «expr!![ »(matrix.notation [expr _, \\\",\\\", expr _, \\\";\\\", expr _, \\\",\\\", expr _, \\\"]\\\"] [])]]\""))
             (Tactic.traceMessage
              "trace"
              (str
               "\"./././Mathport/Syntax/Translate/Tactic/Builtin.lean:76:14: unsupported tactic `congrm #[[expr «expr!![ »(matrix.notation [expr _, \\\",\\\", expr _, \\\";\\\", expr _, \\\",\\\", expr _, \\\"]\\\"] [])]]\"")))
            []
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] `mul_one)
               ","
               (Tactic.rwRule [] `mul_one)
               ","
               (Tactic.rwRule [] `add_comm)]
              "]")
             [])])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Mathlib.Tactic.tacticSimp_rw__
             "simp_rw"
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] `zpow_sub)
               ","
               (Tactic.rwRule [] `zpow_one)
               ","
               (Tactic.rwRule [] `coe_mul)
               ","
               (Tactic.rwRule [] `h)
               ","
               (Tactic.rwRule [] `coe_T_inv)
               ","
               (Tactic.rwRule [] `Matrix.mul_fin_two)]
              "]")
             [])
            []
            (Tactic.«tactic_<;>_»
             (choice
              (Tactic.trace
               "trace"
               (str
                "\"./././Mathport/Syntax/Translate/Tactic/Builtin.lean:76:14: unsupported tactic `congrm #[[expr «expr!![ »(matrix.notation [expr _, \\\",\\\", expr _, \\\";\\\", expr _, \\\",\\\", expr _, \\\"]\\\"] [])]]\""))
              (Tactic.traceMessage
               "trace"
               (str
                "\"./././Mathport/Syntax/Translate/Tactic/Builtin.lean:76:14: unsupported tactic `congrm #[[expr «expr!![ »(matrix.notation [expr _, \\\",\\\", expr _, \\\";\\\", expr _, \\\",\\\", expr _, \\\"]\\\"] [])]]\"")))
             "<;>"
             (Mathlib.Tactic.RingNF.ring "ring"))])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Mathlib.Tactic.tacticSimp_rw__
         "simp_rw"
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule [] `zpow_sub)
           ","
           (Tactic.rwRule [] `zpow_one)
           ","
           (Tactic.rwRule [] `coe_mul)
           ","
           (Tactic.rwRule [] `h)
           ","
           (Tactic.rwRule [] `coe_T_inv)
           ","
           (Tactic.rwRule [] `Matrix.mul_fin_two)]
          "]")
         [])
        []
        (Tactic.«tactic_<;>_»
         (choice
          (Tactic.trace
           "trace"
           (str
            "\"./././Mathport/Syntax/Translate/Tactic/Builtin.lean:76:14: unsupported tactic `congrm #[[expr «expr!![ »(matrix.notation [expr _, \\\",\\\", expr _, \\\";\\\", expr _, \\\",\\\", expr _, \\\"]\\\"] [])]]\""))
          (Tactic.traceMessage
           "trace"
           (str
            "\"./././Mathport/Syntax/Translate/Tactic/Builtin.lean:76:14: unsupported tactic `congrm #[[expr «expr!![ »(matrix.notation [expr _, \\\",\\\", expr _, \\\";\\\", expr _, \\\",\\\", expr _, \\\"]\\\"] [])]]\"")))
         "<;>"
         (Mathlib.Tactic.RingNF.ring "ring"))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.«tactic_<;>_»
       (choice
        (Tactic.trace
         "trace"
         (str
          "\"./././Mathport/Syntax/Translate/Tactic/Builtin.lean:76:14: unsupported tactic `congrm #[[expr «expr!![ »(matrix.notation [expr _, \\\",\\\", expr _, \\\";\\\", expr _, \\\",\\\", expr _, \\\"]\\\"] [])]]\""))
        (Tactic.traceMessage
         "trace"
         (str
          "\"./././Mathport/Syntax/Translate/Tactic/Builtin.lean:76:14: unsupported tactic `congrm #[[expr «expr!![ »(matrix.notation [expr _, \\\",\\\", expr _, \\\";\\\", expr _, \\\",\\\", expr _, \\\"]\\\"] [])]]\"")))
       "<;>"
       (Mathlib.Tactic.RingNF.ring "ring"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.RingNF.ring "ring")
[PrettyPrinter.parenthesize] ...precedences are 2 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
      (choice
       (Tactic.trace
        "trace"
        (str
         "\"./././Mathport/Syntax/Translate/Tactic/Builtin.lean:76:14: unsupported tactic `congrm #[[expr «expr!![ »(matrix.notation [expr _, \\\",\\\", expr _, \\\";\\\", expr _, \\\",\\\", expr _, \\\"]\\\"] [])]]\""))
       (Tactic.traceMessage
        "trace"
        (str
         "\"./././Mathport/Syntax/Translate/Tactic/Builtin.lean:76:14: unsupported tactic `congrm #[[expr «expr!![ »(matrix.notation [expr _, \\\",\\\", expr _, \\\";\\\", expr _, \\\",\\\", expr _, \\\"]\\\"] [])]]\"")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
      (str
       "\"./././Mathport/Syntax/Translate/Tactic/Builtin.lean:76:14: unsupported tactic `congrm #[[expr «expr!![ »(matrix.notation [expr _, \\\",\\\", expr _, \\\";\\\", expr _, \\\",\\\", expr _, \\\"]\\\"] [])]]\"")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (some 1022, tactic)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.tacticSimp_rw__
       "simp_rw"
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `zpow_sub)
         ","
         (Tactic.rwRule [] `zpow_one)
         ","
         (Tactic.rwRule [] `coe_mul)
         ","
         (Tactic.rwRule [] `h)
         ","
         (Tactic.rwRule [] `coe_T_inv)
         ","
         (Tactic.rwRule [] `Matrix.mul_fin_two)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Matrix.mul_fin_two
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `coe_T_inv
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `coe_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `zpow_one
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `zpow_sub
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Mathlib.Tactic.tacticSimp_rw__
         "simp_rw"
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule [] `zpow_add)
           ","
           (Tactic.rwRule [] `zpow_one)
           ","
           (Tactic.rwRule [] `coe_mul)
           ","
           (Tactic.rwRule [] `h)
           ","
           (Tactic.rwRule [] `coe_T)
           ","
           (Tactic.rwRule [] `Matrix.mul_fin_two)]
          "]")
         [])
        []
        (choice
         (Tactic.trace
          "trace"
          (str
           "\"./././Mathport/Syntax/Translate/Tactic/Builtin.lean:76:14: unsupported tactic `congrm #[[expr «expr!![ »(matrix.notation [expr _, \\\",\\\", expr _, \\\";\\\", expr _, \\\",\\\", expr _, \\\"]\\\"] [])]]\""))
         (Tactic.traceMessage
          "trace"
          (str
           "\"./././Mathport/Syntax/Translate/Tactic/Builtin.lean:76:14: unsupported tactic `congrm #[[expr «expr!![ »(matrix.notation [expr _, \\\",\\\", expr _, \\\";\\\", expr _, \\\",\\\", expr _, \\\"]\\\"] [])]]\"")))
        []
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule [] `mul_one)
           ","
           (Tactic.rwRule [] `mul_one)
           ","
           (Tactic.rwRule [] `add_comm)]
          "]")
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `mul_one)
         ","
         (Tactic.rwRule [] `mul_one)
         ","
         (Tactic.rwRule [] `add_comm)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `add_comm
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_one
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_one
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (choice
       (Tactic.trace
        "trace"
        (str
         "\"./././Mathport/Syntax/Translate/Tactic/Builtin.lean:76:14: unsupported tactic `congrm #[[expr «expr!![ »(matrix.notation [expr _, \\\",\\\", expr _, \\\";\\\", expr _, \\\",\\\", expr _, \\\"]\\\"] [])]]\""))
       (Tactic.traceMessage
        "trace"
        (str
         "\"./././Mathport/Syntax/Translate/Tactic/Builtin.lean:76:14: unsupported tactic `congrm #[[expr «expr!![ »(matrix.notation [expr _, \\\",\\\", expr _, \\\";\\\", expr _, \\\",\\\", expr _, \\\"]\\\"] [])]]\"")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
      (str
       "\"./././Mathport/Syntax/Translate/Tactic/Builtin.lean:76:14: unsupported tactic `congrm #[[expr «expr!![ »(matrix.notation [expr _, \\\",\\\", expr _, \\\";\\\", expr _, \\\",\\\", expr _, \\\"]\\\"] [])]]\"")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (some 1022, tactic)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.tacticSimp_rw__
       "simp_rw"
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `zpow_add)
         ","
         (Tactic.rwRule [] `zpow_one)
         ","
         (Tactic.rwRule [] `coe_mul)
         ","
         (Tactic.rwRule [] `h)
         ","
         (Tactic.rwRule [] `coe_T)
         ","
         (Tactic.rwRule [] `Matrix.mul_fin_two)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Matrix.mul_fin_two
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `coe_T
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `coe_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `zpow_one
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `zpow_add
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule [] `zpow_zero)
           ","
           (Tactic.rwRule [] `coe_one)
           ","
           (Tactic.rwRule [] `Matrix.one_fin_two)]
          "]")
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `zpow_zero)
         ","
         (Tactic.rwRule [] `coe_one)
         ","
         (Tactic.rwRule [] `Matrix.one_fin_two)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Matrix.one_fin_two
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `coe_one
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `zpow_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.induction'
       "induction'"
       [(Tactic.casesTarget [] `n)]
       ["using" `Int.induction_on]
       ["with"
        [(Lean.binderIdent `n) (Lean.binderIdent `h) (Lean.binderIdent `n) (Lean.binderIdent `h)]]
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (NumberTheory.Modular.«term↑ₘ_» "↑ₘ" («term_^_» `T "^" `n))
       "="
       (Term.app
        `«expr!![ »
        [(str
          "\"./././Mathport/Syntax/Translate/Expr.lean:390:14: unsupported user notation matrix.notation\"")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `«expr!![ »
       [(str
         "\"./././Mathport/Syntax/Translate/Expr.lean:390:14: unsupported user notation matrix.notation\"")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'str', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'str', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (str
       "\"./././Mathport/Syntax/Translate/Expr.lean:390:14: unsupported user notation matrix.notation\"")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `«expr!![ »
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (NumberTheory.Modular.«term↑ₘ_» "↑ₘ" («term_^_» `T "^" `n))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.Modular.«term↑ₘ_»', expected 'NumberTheory.Modular.term↑ₘ_._@.NumberTheory.Modular._hyg.827'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  coe_T_zpow
  ( n : ℤ )
    :
      ↑ₘ T ^ n
        =
        «expr!![ »
          "./././Mathport/Syntax/Translate/Expr.lean:390:14: unsupported user notation matrix.notation"
  :=
    by
      induction' n using Int.induction_on with n h n h
        · rw [ zpow_zero , coe_one , Matrix.one_fin_two ]
        ·
          simp_rw [ zpow_add , zpow_one , coe_mul , h , coe_T , Matrix.mul_fin_two ]
            trace
                "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:76:14: unsupported tactic `congrm #[[expr «expr!![ »(matrix.notation [expr _, \",\", expr _, \";\", expr _, \",\", expr _, \"]\"] [])]]"
              trace
                "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:76:14: unsupported tactic `congrm #[[expr «expr!![ »(matrix.notation [expr _, \",\", expr _, \";\", expr _, \",\", expr _, \"]\"] [])]]"
            rw [ mul_one , mul_one , add_comm ]
        ·
          simp_rw [ zpow_sub , zpow_one , coe_mul , h , coe_T_inv , Matrix.mul_fin_two ]
            trace
                  "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:76:14: unsupported tactic `congrm #[[expr «expr!![ »(matrix.notation [expr _, \",\", expr _, \";\", expr _, \",\", expr _, \"]\"] [])]]"
                trace
                  "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:76:14: unsupported tactic `congrm #[[expr «expr!![ »(matrix.notation [expr _, \",\", expr _, \";\", expr _, \",\", expr _, \"]\"] [])]]"
              <;>
              ring
#align modular_group.coe_T_zpow ModularGroup.coe_T_zpow

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
      (Command.declId `T_pow_mul_apply_one [])
      (Command.declSig
       [(Term.explicitBinder "(" [`n] [":" (termℤ "ℤ")] [] ")")
        (Term.explicitBinder
         "("
         [`g]
         [":" (NumberTheory.Modular.«termSL(_,_)» "SL(" (num "2") ", " (termℤ "ℤ") ")")]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app
          (NumberTheory.Modular.«term↑ₘ_» "↑ₘ" («term_*_» («term_^_» `T "^" `n) "*" `g))
          [(num "1")])
         "="
         (Term.app (NumberTheory.Modular.«term↑ₘ_» "↑ₘ" `g) [(num "1")]))))
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
             [(Tactic.simpLemma [] [] `coe_T_zpow)
              ","
              (Tactic.simpLemma [] [] `Matrix.mul)
              ","
              (Tactic.simpLemma [] [] `Matrix.dotProduct)
              ","
              (Tactic.simpLemma [] [] `Fin.sum_univ_succ)]
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
            [(Tactic.simpLemma [] [] `coe_T_zpow)
             ","
             (Tactic.simpLemma [] [] `Matrix.mul)
             ","
             (Tactic.simpLemma [] [] `Matrix.dotProduct)
             ","
             (Tactic.simpLemma [] [] `Fin.sum_univ_succ)]
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
        [(Tactic.simpLemma [] [] `coe_T_zpow)
         ","
         (Tactic.simpLemma [] [] `Matrix.mul)
         ","
         (Tactic.simpLemma [] [] `Matrix.dotProduct)
         ","
         (Tactic.simpLemma [] [] `Fin.sum_univ_succ)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Fin.sum_univ_succ
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Matrix.dotProduct
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Matrix.mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `coe_T_zpow
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app
        (NumberTheory.Modular.«term↑ₘ_» "↑ₘ" («term_*_» («term_^_» `T "^" `n) "*" `g))
        [(num "1")])
       "="
       (Term.app (NumberTheory.Modular.«term↑ₘ_» "↑ₘ" `g) [(num "1")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (NumberTheory.Modular.«term↑ₘ_» "↑ₘ" `g) [(num "1")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (NumberTheory.Modular.«term↑ₘ_» "↑ₘ" `g)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.Modular.«term↑ₘ_»', expected 'NumberTheory.Modular.term↑ₘ_._@.NumberTheory.Modular._hyg.827'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ simp ]
  theorem
    T_pow_mul_apply_one
    ( n : ℤ ) ( g : SL( 2 , ℤ ) ) : ↑ₘ T ^ n * g 1 = ↑ₘ g 1
    := by simp [ coe_T_zpow , Matrix.mul , Matrix.dotProduct , Fin.sum_univ_succ ]
#align modular_group.T_pow_mul_apply_one ModularGroup.T_pow_mul_apply_one

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
      (Command.declId `T_mul_apply_one [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`g]
         [":" (NumberTheory.Modular.«termSL(_,_)» "SL(" (num "2") ", " (termℤ "ℤ") ")")]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app (NumberTheory.Modular.«term↑ₘ_» "↑ₘ" («term_*_» `T "*" `g)) [(num "1")])
         "="
         (Term.app (NumberTheory.Modular.«term↑ₘ_» "↑ₘ" `g) [(num "1")]))))
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
             []
             ["using" (Term.app `T_pow_mul_apply_one [(num "1") `g])]))])))
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
            []
            ["using" (Term.app `T_pow_mul_apply_one [(num "1") `g])]))])))
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
        []
        ["using" (Term.app `T_pow_mul_apply_one [(num "1") `g])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `T_pow_mul_apply_one [(num "1") `g])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `T_pow_mul_apply_one
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app (NumberTheory.Modular.«term↑ₘ_» "↑ₘ" («term_*_» `T "*" `g)) [(num "1")])
       "="
       (Term.app (NumberTheory.Modular.«term↑ₘ_» "↑ₘ" `g) [(num "1")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (NumberTheory.Modular.«term↑ₘ_» "↑ₘ" `g) [(num "1")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (NumberTheory.Modular.«term↑ₘ_» "↑ₘ" `g)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.Modular.«term↑ₘ_»', expected 'NumberTheory.Modular.term↑ₘ_._@.NumberTheory.Modular._hyg.827'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ simp ]
  theorem
    T_mul_apply_one
    ( g : SL( 2 , ℤ ) ) : ↑ₘ T * g 1 = ↑ₘ g 1
    := by simpa using T_pow_mul_apply_one 1 g
#align modular_group.T_mul_apply_one ModularGroup.T_mul_apply_one

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
      (Command.declId `T_inv_mul_apply_one [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`g]
         [":" (NumberTheory.Modular.«termSL(_,_)» "SL(" (num "2") ", " (termℤ "ℤ") ")")]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app
          (NumberTheory.Modular.«term↑ₘ_» "↑ₘ" («term_*_» («term_⁻¹» `T "⁻¹") "*" `g))
          [(num "1")])
         "="
         (Term.app (NumberTheory.Modular.«term↑ₘ_» "↑ₘ" `g) [(num "1")]))))
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
             []
             ["using" (Term.app `T_pow_mul_apply_one [(«term-_» "-" (num "1")) `g])]))])))
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
            []
            ["using" (Term.app `T_pow_mul_apply_one [(«term-_» "-" (num "1")) `g])]))])))
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
        []
        ["using" (Term.app `T_pow_mul_apply_one [(«term-_» "-" (num "1")) `g])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `T_pow_mul_apply_one [(«term-_» "-" (num "1")) `g])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term-_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term-_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      («term-_» "-" (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 75 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 75, (some 75, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term-_» "-" (num "1")) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `T_pow_mul_apply_one
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app
        (NumberTheory.Modular.«term↑ₘ_» "↑ₘ" («term_*_» («term_⁻¹» `T "⁻¹") "*" `g))
        [(num "1")])
       "="
       (Term.app (NumberTheory.Modular.«term↑ₘ_» "↑ₘ" `g) [(num "1")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (NumberTheory.Modular.«term↑ₘ_» "↑ₘ" `g) [(num "1")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (NumberTheory.Modular.«term↑ₘ_» "↑ₘ" `g)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.Modular.«term↑ₘ_»', expected 'NumberTheory.Modular.term↑ₘ_._@.NumberTheory.Modular._hyg.827'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ simp ]
  theorem
    T_inv_mul_apply_one
    ( g : SL( 2 , ℤ ) ) : ↑ₘ T ⁻¹ * g 1 = ↑ₘ g 1
    := by simpa using T_pow_mul_apply_one - 1 g
#align modular_group.T_inv_mul_apply_one ModularGroup.T_inv_mul_apply_one

theorem coe_T_zpow_smul_eq {n : ℤ} : (↑(T ^ n • z) : ℂ) = z + n := by simp [coe_T_zpow]
#align modular_group.coe_T_zpow_smul_eq ModularGroup.coe_T_zpow_smul_eq

theorem re_T_zpow_smul (n : ℤ) : (T ^ n • z).re = z.re + n := by
  rw [← coe_re, coe_T_zpow_smul_eq, add_re, int_cast_re, coe_re]
#align modular_group.re_T_zpow_smul ModularGroup.re_T_zpow_smul

theorem im_T_zpow_smul (n : ℤ) : (T ^ n • z).im = z.im := by
  rw [← coe_im, coe_T_zpow_smul_eq, add_im, int_cast_im, add_zero, coe_im]
#align modular_group.im_T_zpow_smul ModularGroup.im_T_zpow_smul

theorem re_T_smul : (T • z).re = z.re + 1 := by simpa using re_T_zpow_smul z 1
#align modular_group.re_T_smul ModularGroup.re_T_smul

theorem im_T_smul : (T • z).im = z.im := by simpa using im_T_zpow_smul z 1
#align modular_group.im_T_smul ModularGroup.im_T_smul

theorem re_T_inv_smul : (T⁻¹ • z).re = z.re - 1 := by simpa using re_T_zpow_smul z (-1)
#align modular_group.re_T_inv_smul ModularGroup.re_T_inv_smul

theorem im_T_inv_smul : (T⁻¹ • z).im = z.im := by simpa using im_T_zpow_smul z (-1)
#align modular_group.im_T_inv_smul ModularGroup.im_T_inv_smul

variable {z}

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `exists_eq_T_zpow_of_c_eq_zero [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`hc]
         [":"
          («term_=_»
           (Term.app (NumberTheory.Modular.«term↑ₘ_» "↑ₘ" `g) [(num "1") (num "0")])
           "="
           (num "0"))]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term∃_,_»
         "∃"
         (Lean.explicitBinders
          (Lean.unbracketedExplicitBinders [(Lean.binderIdent `n)] [":" (termℤ "ℤ")]))
         ","
         (Term.forall
          "∀"
          [`z]
          [(Term.typeSpec
            ":"
            (UpperHalfPlane.Analysis.Complex.UpperHalfPlane.Basic.upper_half_plane "ℍ"))]
          ","
          («term_=_»
           (Algebra.Group.Defs.«term_•_» `g " • " `z)
           "="
           (Algebra.Group.Defs.«term_•_» («term_^_» `T "^" `n) " • " `z))))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.tacticHave_
            "have"
            (Term.haveDecl (Term.haveIdDecl [`had []] [] ":=" `g.det_coe)))
           []
           (Mathlib.Tactic.replace'
            "replace"
            [`had []]
            [(Term.typeSpec
              ":"
              («term_=_»
               («term_*_»
                (Term.app (NumberTheory.Modular.«term↑ₘ_» "↑ₘ" `g) [(num "0") (num "0")])
                "*"
                (Term.app (NumberTheory.Modular.«term↑ₘ_» "↑ₘ" `g) [(num "1") (num "1")]))
               "="
               (num "1")))])
           ";"
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [] `det_fin_two) "," (Tactic.rwRule [] `hc)]
               "]")
              [(Tactic.location "at" (Tactic.locationHyp [`had] []))])
             []
             (linarith "linarith" [] (linarithArgsRest [] [] []))])
           []
           (Std.Tactic.rcases
            "rcases"
            [(Tactic.casesTarget [] (Term.app `Int.eq_one_or_neg_one_of_mul_eq_one' [`had]))]
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
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `ha)])
                       [])
                      ","
                      (Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hd)])
                       [])]
                     "⟩")
                    "|"
                    (Std.Tactic.RCases.rcasesPat.tuple
                     "⟨"
                     [(Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `ha)])
                       [])
                      ","
                      (Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hd)])
                       [])]
                     "⟩")])
                  [])
                 ")")])
              [])])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Mathlib.Tactic.«tacticUse_,,»
              "use"
              [(Term.app (NumberTheory.Modular.«term↑ₘ_» "↑ₘ" `g) [(num "0") (num "1")])])
             []
             (Tactic.tacticSuffices_
              "suffices"
              (Term.sufficesDecl
               []
               («term_=_»
                `g
                "="
                («term_^_»
                 `T
                 "^"
                 (Term.app (NumberTheory.Modular.«term↑ₘ_» "↑ₘ" `g) [(num "0") (num "1")])))
               (Term.byTactic'
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(Tactic.intro "intro" [`z])
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
                        (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `this)] "]"))])))])))))
             []
             (Std.Tactic.Ext.«tacticExt___:_»
              "ext"
              [(Std.Tactic.RCases.rintroPat.binder
                "("
                [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `i))
                 (Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `j))]
                []
                ")")]
              [])
             []
             (Tactic.«tactic_<;>_»
              (Tactic.«tactic_<;>_»
               (Lean.Elab.Tactic.finCases "fin_cases" [`i] [])
               "<;>"
               (Lean.Elab.Tactic.finCases "fin_cases" [`j] []))
              "<;>"
              (Tactic.simp
               "simp"
               []
               []
               []
               ["["
                [(Tactic.simpLemma [] [] `ha)
                 ","
                 (Tactic.simpLemma [] [] `hc)
                 ","
                 (Tactic.simpLemma [] [] `hd)
                 ","
                 (Tactic.simpLemma [] [] `coe_T_zpow)]
                "]"]
               []))])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Mathlib.Tactic.«tacticUse_,,»
              "use"
              [(«term-_»
                "-"
                (Term.app (NumberTheory.Modular.«term↑ₘ_» "↑ₘ" `g) [(num "0") (num "1")]))])
             []
             (Tactic.tacticSuffices_
              "suffices"
              (Term.sufficesDecl
               []
               («term_=_»
                `g
                "="
                («term-_»
                 "-"
                 («term_^_»
                  `T
                  "^"
                  («term-_»
                   "-"
                   (Term.app (NumberTheory.Modular.«term↑ₘ_» "↑ₘ" `g) [(num "0") (num "1")])))))
               (Term.byTactic'
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(Tactic.intro "intro" [`z])
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
                         [(Tactic.rwRule [] `this) "," (Tactic.rwRule [] `SL_neg_smul)]
                         "]"))])))])))))
             []
             (Std.Tactic.Ext.«tacticExt___:_»
              "ext"
              [(Std.Tactic.RCases.rintroPat.binder
                "("
                [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `i))
                 (Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `j))]
                []
                ")")]
              [])
             []
             (Tactic.«tactic_<;>_»
              (Tactic.«tactic_<;>_»
               (Lean.Elab.Tactic.finCases "fin_cases" [`i] [])
               "<;>"
               (Lean.Elab.Tactic.finCases "fin_cases" [`j] []))
              "<;>"
              (Tactic.simp
               "simp"
               []
               []
               []
               ["["
                [(Tactic.simpLemma [] [] `ha)
                 ","
                 (Tactic.simpLemma [] [] `hc)
                 ","
                 (Tactic.simpLemma [] [] `hd)
                 ","
                 (Tactic.simpLemma [] [] `coe_T_zpow)]
                "]"]
               []))])])))
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
         [(Tactic.tacticHave_ "have" (Term.haveDecl (Term.haveIdDecl [`had []] [] ":=" `g.det_coe)))
          []
          (Mathlib.Tactic.replace'
           "replace"
           [`had []]
           [(Term.typeSpec
             ":"
             («term_=_»
              («term_*_»
               (Term.app (NumberTheory.Modular.«term↑ₘ_» "↑ₘ" `g) [(num "0") (num "0")])
               "*"
               (Term.app (NumberTheory.Modular.«term↑ₘ_» "↑ₘ" `g) [(num "1") (num "1")]))
              "="
              (num "1")))])
          ";"
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `det_fin_two) "," (Tactic.rwRule [] `hc)] "]")
             [(Tactic.location "at" (Tactic.locationHyp [`had] []))])
            []
            (linarith "linarith" [] (linarithArgsRest [] [] []))])
          []
          (Std.Tactic.rcases
           "rcases"
           [(Tactic.casesTarget [] (Term.app `Int.eq_one_or_neg_one_of_mul_eq_one' [`had]))]
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
                      (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `ha)])
                      [])
                     ","
                     (Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hd)])
                      [])]
                    "⟩")
                   "|"
                   (Std.Tactic.RCases.rcasesPat.tuple
                    "⟨"
                    [(Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `ha)])
                      [])
                     ","
                     (Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hd)])
                      [])]
                    "⟩")])
                 [])
                ")")])
             [])])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Mathlib.Tactic.«tacticUse_,,»
             "use"
             [(Term.app (NumberTheory.Modular.«term↑ₘ_» "↑ₘ" `g) [(num "0") (num "1")])])
            []
            (Tactic.tacticSuffices_
             "suffices"
             (Term.sufficesDecl
              []
              («term_=_»
               `g
               "="
               («term_^_»
                `T
                "^"
                (Term.app (NumberTheory.Modular.«term↑ₘ_» "↑ₘ" `g) [(num "0") (num "1")])))
              (Term.byTactic'
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Tactic.intro "intro" [`z])
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
                       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `this)] "]"))])))])))))
            []
            (Std.Tactic.Ext.«tacticExt___:_»
             "ext"
             [(Std.Tactic.RCases.rintroPat.binder
               "("
               [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `i))
                (Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `j))]
               []
               ")")]
             [])
            []
            (Tactic.«tactic_<;>_»
             (Tactic.«tactic_<;>_»
              (Lean.Elab.Tactic.finCases "fin_cases" [`i] [])
              "<;>"
              (Lean.Elab.Tactic.finCases "fin_cases" [`j] []))
             "<;>"
             (Tactic.simp
              "simp"
              []
              []
              []
              ["["
               [(Tactic.simpLemma [] [] `ha)
                ","
                (Tactic.simpLemma [] [] `hc)
                ","
                (Tactic.simpLemma [] [] `hd)
                ","
                (Tactic.simpLemma [] [] `coe_T_zpow)]
               "]"]
              []))])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Mathlib.Tactic.«tacticUse_,,»
             "use"
             [(«term-_»
               "-"
               (Term.app (NumberTheory.Modular.«term↑ₘ_» "↑ₘ" `g) [(num "0") (num "1")]))])
            []
            (Tactic.tacticSuffices_
             "suffices"
             (Term.sufficesDecl
              []
              («term_=_»
               `g
               "="
               («term-_»
                "-"
                («term_^_»
                 `T
                 "^"
                 («term-_»
                  "-"
                  (Term.app (NumberTheory.Modular.«term↑ₘ_» "↑ₘ" `g) [(num "0") (num "1")])))))
              (Term.byTactic'
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Tactic.intro "intro" [`z])
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
                        [(Tactic.rwRule [] `this) "," (Tactic.rwRule [] `SL_neg_smul)]
                        "]"))])))])))))
            []
            (Std.Tactic.Ext.«tacticExt___:_»
             "ext"
             [(Std.Tactic.RCases.rintroPat.binder
               "("
               [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `i))
                (Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `j))]
               []
               ")")]
             [])
            []
            (Tactic.«tactic_<;>_»
             (Tactic.«tactic_<;>_»
              (Lean.Elab.Tactic.finCases "fin_cases" [`i] [])
              "<;>"
              (Lean.Elab.Tactic.finCases "fin_cases" [`j] []))
             "<;>"
             (Tactic.simp
              "simp"
              []
              []
              []
              ["["
               [(Tactic.simpLemma [] [] `ha)
                ","
                (Tactic.simpLemma [] [] `hc)
                ","
                (Tactic.simpLemma [] [] `hd)
                ","
                (Tactic.simpLemma [] [] `coe_T_zpow)]
               "]"]
              []))])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Mathlib.Tactic.«tacticUse_,,»
         "use"
         [(«term-_» "-" (Term.app (NumberTheory.Modular.«term↑ₘ_» "↑ₘ" `g) [(num "0") (num "1")]))])
        []
        (Tactic.tacticSuffices_
         "suffices"
         (Term.sufficesDecl
          []
          («term_=_»
           `g
           "="
           («term-_»
            "-"
            («term_^_»
             `T
             "^"
             («term-_»
              "-"
              (Term.app (NumberTheory.Modular.«term↑ₘ_» "↑ₘ" `g) [(num "0") (num "1")])))))
          (Term.byTactic'
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(Tactic.intro "intro" [`z])
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
                    [(Tactic.rwRule [] `this) "," (Tactic.rwRule [] `SL_neg_smul)]
                    "]"))])))])))))
        []
        (Std.Tactic.Ext.«tacticExt___:_»
         "ext"
         [(Std.Tactic.RCases.rintroPat.binder
           "("
           [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `i))
            (Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `j))]
           []
           ")")]
         [])
        []
        (Tactic.«tactic_<;>_»
         (Tactic.«tactic_<;>_»
          (Lean.Elab.Tactic.finCases "fin_cases" [`i] [])
          "<;>"
          (Lean.Elab.Tactic.finCases "fin_cases" [`j] []))
         "<;>"
         (Tactic.simp
          "simp"
          []
          []
          []
          ["["
           [(Tactic.simpLemma [] [] `ha)
            ","
            (Tactic.simpLemma [] [] `hc)
            ","
            (Tactic.simpLemma [] [] `hd)
            ","
            (Tactic.simpLemma [] [] `coe_T_zpow)]
           "]"]
          []))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.«tactic_<;>_»
       (Tactic.«tactic_<;>_»
        (Lean.Elab.Tactic.finCases "fin_cases" [`i] [])
        "<;>"
        (Lean.Elab.Tactic.finCases "fin_cases" [`j] []))
       "<;>"
       (Tactic.simp
        "simp"
        []
        []
        []
        ["["
         [(Tactic.simpLemma [] [] `ha)
          ","
          (Tactic.simpLemma [] [] `hc)
          ","
          (Tactic.simpLemma [] [] `hd)
          ","
          (Tactic.simpLemma [] [] `coe_T_zpow)]
         "]"]
        []))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       []
       ["["
        [(Tactic.simpLemma [] [] `ha)
         ","
         (Tactic.simpLemma [] [] `hc)
         ","
         (Tactic.simpLemma [] [] `hd)
         ","
         (Tactic.simpLemma [] [] `coe_T_zpow)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `coe_T_zpow
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hd
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hc
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ha
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 2 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
      (Tactic.«tactic_<;>_»
       (Lean.Elab.Tactic.finCases "fin_cases" [`i] [])
       "<;>"
       (Lean.Elab.Tactic.finCases "fin_cases" [`j] []))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Lean.Elab.Tactic.finCases "fin_cases" [`j] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'token.«*»'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `j
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 2 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
      (Lean.Elab.Tactic.finCases "fin_cases" [`i] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'token.«*»'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Ext.«tacticExt___:_»
       "ext"
       [(Std.Tactic.RCases.rintroPat.binder
         "("
         [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `i))
          (Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `j))]
         []
         ")")]
       [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticSuffices_
       "suffices"
       (Term.sufficesDecl
        []
        («term_=_»
         `g
         "="
         («term-_»
          "-"
          («term_^_»
           `T
           "^"
           («term-_»
            "-"
            (Term.app (NumberTheory.Modular.«term↑ₘ_» "↑ₘ" `g) [(num "0") (num "1")])))))
        (Term.byTactic'
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Tactic.intro "intro" [`z])
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
                  [(Tactic.rwRule [] `this) "," (Tactic.rwRule [] `SL_neg_smul)]
                  "]"))])))])))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic'', expected 'Lean.Parser.Term.fromTerm'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
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
            [(Tactic.rwRule [] `this) "," (Tactic.rwRule [] `SL_neg_smul)]
            "]"))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.Conv.convSeq1Indented', expected 'Lean.Parser.Tactic.Conv.convSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `SL_neg_smul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `this
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.intro "intro" [`z])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `z
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       `g
       "="
       («term-_»
        "-"
        («term_^_»
         `T
         "^"
         («term-_» "-" (Term.app (NumberTheory.Modular.«term↑ₘ_» "↑ₘ" `g) [(num "0") (num "1")])))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term-_»
       "-"
       («term_^_»
        `T
        "^"
        («term-_» "-" (Term.app (NumberTheory.Modular.«term↑ₘ_» "↑ₘ" `g) [(num "0") (num "1")]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_»
       `T
       "^"
       («term-_» "-" (Term.app (NumberTheory.Modular.«term↑ₘ_» "↑ₘ" `g) [(num "0") (num "1")])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term-_» "-" (Term.app (NumberTheory.Modular.«term↑ₘ_» "↑ₘ" `g) [(num "0") (num "1")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (NumberTheory.Modular.«term↑ₘ_» "↑ₘ" `g) [(num "0") (num "1")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (NumberTheory.Modular.«term↑ₘ_» "↑ₘ" `g)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.Modular.«term↑ₘ_»', expected 'NumberTheory.Modular.term↑ₘ_._@.NumberTheory.Modular._hyg.827'
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
  exists_eq_T_zpow_of_c_eq_zero
  ( hc : ↑ₘ g 1 0 = 0 ) : ∃ n : ℤ , ∀ z : ℍ , g • z = T ^ n • z
  :=
    by
      have had := g.det_coe
        replace had : ↑ₘ g 0 0 * ↑ₘ g 1 1 = 1
        ;
        · rw [ det_fin_two , hc ] at had linarith
        rcases Int.eq_one_or_neg_one_of_mul_eq_one' had with ( ⟨ ha , hd ⟩ | ⟨ ha , hd ⟩ )
        ·
          use ↑ₘ g 0 1
            suffices g = T ^ ↑ₘ g 0 1 by intro z conv_lhs => rw [ this ]
            ext ( i j )
            fin_cases i <;> fin_cases j <;> simp [ ha , hc , hd , coe_T_zpow ]
        ·
          use - ↑ₘ g 0 1
            suffices g = - T ^ - ↑ₘ g 0 1 by intro z conv_lhs => rw [ this , SL_neg_smul ]
            ext ( i j )
            fin_cases i <;> fin_cases j <;> simp [ ha , hc , hd , coe_T_zpow ]
#align modular_group.exists_eq_T_zpow_of_c_eq_zero ModularGroup.exists_eq_T_zpow_of_c_eq_zero

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:76:14: unsupported tactic `congrm #[[expr «expr!![ »(matrix.notation [expr _, ",", expr _, ";", expr _, ",", expr _, "]"] [])]] -/
/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `g_eq_of_c_eq_one [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`hc]
         [":"
          («term_=_»
           (Term.app (NumberTheory.Modular.«term↑ₘ_» "↑ₘ" `g) [(num "1") (num "0")])
           "="
           (num "1"))]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         `g
         "="
         («term_*_»
          («term_*_»
           («term_^_»
            `T
            "^"
            (Term.app (NumberTheory.Modular.«term↑ₘ_» "↑ₘ" `g) [(num "0") (num "0")]))
           "*"
           `S)
          "*"
          («term_^_»
           `T
           "^"
           (Term.app (NumberTheory.Modular.«term↑ₘ_» "↑ₘ" `g) [(num "1") (num "1")]))))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.tacticHave_
            "have"
            (Term.haveDecl (Term.haveIdDecl [`hg []] [] ":=" `g.det_coe.symm)))
           []
           (Mathlib.Tactic.replace'
            "replace"
            [`hg []]
            [(Term.typeSpec
              ":"
              («term_=_»
               (Term.app (NumberTheory.Modular.«term↑ₘ_» "↑ₘ" `g) [(num "0") (num "1")])
               "="
               («term_-_»
                («term_*_»
                 (Term.app (NumberTheory.Modular.«term↑ₘ_» "↑ₘ" `g) [(num "0") (num "0")])
                 "*"
                 (Term.app (NumberTheory.Modular.«term↑ₘ_» "↑ₘ" `g) [(num "1") (num "1")]))
                "-"
                (num "1"))))])
           ";"
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [] `det_fin_two) "," (Tactic.rwRule [] `hc)]
               "]")
              [(Tactic.location "at" (Tactic.locationHyp [`hg] []))])
             []
             (linarith "linarith" [] (linarithArgsRest [] [] []))])
           []
           (Tactic.refine' "refine'" (Term.app `Subtype.ext [(Term.hole "_")]))
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
                   []
                   (Term.app `Matrix.eta_fin_two [(NumberTheory.Modular.«term↑ₘ_» "↑ₘ" `g)]))]
                 "]"))])))
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `hc) "," (Tactic.rwRule [] `hg)] "]")
            [])
           []
           (Tactic.simp
            "simp"
            []
            []
            ["only"]
            ["["
             [(Tactic.simpLemma [] [] `coe_mul)
              ","
              (Tactic.simpLemma [] [] `coe_T_zpow)
              ","
              (Tactic.simpLemma [] [] `coe_S)
              ","
              (Tactic.simpLemma [] [] `mul_fin_two)]
             "]"]
            [])
           []
           (Tactic.«tactic_<;>_»
            (choice
             (Tactic.trace
              "trace"
              (str
               "\"./././Mathport/Syntax/Translate/Tactic/Builtin.lean:76:14: unsupported tactic `congrm #[[expr «expr!![ »(matrix.notation [expr _, \\\",\\\", expr _, \\\";\\\", expr _, \\\",\\\", expr _, \\\"]\\\"] [])]]\""))
             (Tactic.traceMessage
              "trace"
              (str
               "\"./././Mathport/Syntax/Translate/Tactic/Builtin.lean:76:14: unsupported tactic `congrm #[[expr «expr!![ »(matrix.notation [expr _, \\\",\\\", expr _, \\\";\\\", expr _, \\\",\\\", expr _, \\\"]\\\"] [])]]\"")))
            "<;>"
            (Mathlib.Tactic.RingNF.ring "ring"))])))
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
         [(Tactic.tacticHave_
           "have"
           (Term.haveDecl (Term.haveIdDecl [`hg []] [] ":=" `g.det_coe.symm)))
          []
          (Mathlib.Tactic.replace'
           "replace"
           [`hg []]
           [(Term.typeSpec
             ":"
             («term_=_»
              (Term.app (NumberTheory.Modular.«term↑ₘ_» "↑ₘ" `g) [(num "0") (num "1")])
              "="
              («term_-_»
               («term_*_»
                (Term.app (NumberTheory.Modular.«term↑ₘ_» "↑ₘ" `g) [(num "0") (num "0")])
                "*"
                (Term.app (NumberTheory.Modular.«term↑ₘ_» "↑ₘ" `g) [(num "1") (num "1")]))
               "-"
               (num "1"))))])
          ";"
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `det_fin_two) "," (Tactic.rwRule [] `hc)] "]")
             [(Tactic.location "at" (Tactic.locationHyp [`hg] []))])
            []
            (linarith "linarith" [] (linarithArgsRest [] [] []))])
          []
          (Tactic.refine' "refine'" (Term.app `Subtype.ext [(Term.hole "_")]))
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
                  []
                  (Term.app `Matrix.eta_fin_two [(NumberTheory.Modular.«term↑ₘ_» "↑ₘ" `g)]))]
                "]"))])))
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `hc) "," (Tactic.rwRule [] `hg)] "]")
           [])
          []
          (Tactic.simp
           "simp"
           []
           []
           ["only"]
           ["["
            [(Tactic.simpLemma [] [] `coe_mul)
             ","
             (Tactic.simpLemma [] [] `coe_T_zpow)
             ","
             (Tactic.simpLemma [] [] `coe_S)
             ","
             (Tactic.simpLemma [] [] `mul_fin_two)]
            "]"]
           [])
          []
          (Tactic.«tactic_<;>_»
           (choice
            (Tactic.trace
             "trace"
             (str
              "\"./././Mathport/Syntax/Translate/Tactic/Builtin.lean:76:14: unsupported tactic `congrm #[[expr «expr!![ »(matrix.notation [expr _, \\\",\\\", expr _, \\\";\\\", expr _, \\\",\\\", expr _, \\\"]\\\"] [])]]\""))
            (Tactic.traceMessage
             "trace"
             (str
              "\"./././Mathport/Syntax/Translate/Tactic/Builtin.lean:76:14: unsupported tactic `congrm #[[expr «expr!![ »(matrix.notation [expr _, \\\",\\\", expr _, \\\";\\\", expr _, \\\",\\\", expr _, \\\"]\\\"] [])]]\"")))
           "<;>"
           (Mathlib.Tactic.RingNF.ring "ring"))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.«tactic_<;>_»
       (choice
        (Tactic.trace
         "trace"
         (str
          "\"./././Mathport/Syntax/Translate/Tactic/Builtin.lean:76:14: unsupported tactic `congrm #[[expr «expr!![ »(matrix.notation [expr _, \\\",\\\", expr _, \\\";\\\", expr _, \\\",\\\", expr _, \\\"]\\\"] [])]]\""))
        (Tactic.traceMessage
         "trace"
         (str
          "\"./././Mathport/Syntax/Translate/Tactic/Builtin.lean:76:14: unsupported tactic `congrm #[[expr «expr!![ »(matrix.notation [expr _, \\\",\\\", expr _, \\\";\\\", expr _, \\\",\\\", expr _, \\\"]\\\"] [])]]\"")))
       "<;>"
       (Mathlib.Tactic.RingNF.ring "ring"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.RingNF.ring "ring")
[PrettyPrinter.parenthesize] ...precedences are 2 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
      (choice
       (Tactic.trace
        "trace"
        (str
         "\"./././Mathport/Syntax/Translate/Tactic/Builtin.lean:76:14: unsupported tactic `congrm #[[expr «expr!![ »(matrix.notation [expr _, \\\",\\\", expr _, \\\";\\\", expr _, \\\",\\\", expr _, \\\"]\\\"] [])]]\""))
       (Tactic.traceMessage
        "trace"
        (str
         "\"./././Mathport/Syntax/Translate/Tactic/Builtin.lean:76:14: unsupported tactic `congrm #[[expr «expr!![ »(matrix.notation [expr _, \\\",\\\", expr _, \\\";\\\", expr _, \\\",\\\", expr _, \\\"]\\\"] [])]]\"")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
      (str
       "\"./././Mathport/Syntax/Translate/Tactic/Builtin.lean:76:14: unsupported tactic `congrm #[[expr «expr!![ »(matrix.notation [expr _, \\\",\\\", expr _, \\\";\\\", expr _, \\\",\\\", expr _, \\\"]\\\"] [])]]\"")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (some 1022, tactic)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["["
        [(Tactic.simpLemma [] [] `coe_mul)
         ","
         (Tactic.simpLemma [] [] `coe_T_zpow)
         ","
         (Tactic.simpLemma [] [] `coe_S)
         ","
         (Tactic.simpLemma [] [] `mul_fin_two)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_fin_two
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `coe_S
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `coe_T_zpow
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `coe_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `hc) "," (Tactic.rwRule [] `hg)] "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hg
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hc
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
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
              []
              (Term.app `Matrix.eta_fin_two [(NumberTheory.Modular.«term↑ₘ_» "↑ₘ" `g)]))]
            "]"))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.Conv.convSeq1Indented', expected 'Lean.Parser.Tactic.Conv.convSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Matrix.eta_fin_two [(NumberTheory.Modular.«term↑ₘ_» "↑ₘ" `g)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.Modular.«term↑ₘ_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.Modular.«term↑ₘ_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (NumberTheory.Modular.«term↑ₘ_» "↑ₘ" `g)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.Modular.«term↑ₘ_»', expected 'NumberTheory.Modular.term↑ₘ_._@.NumberTheory.Modular._hyg.827'
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
  g_eq_of_c_eq_one
  ( hc : ↑ₘ g 1 0 = 1 ) : g = T ^ ↑ₘ g 0 0 * S * T ^ ↑ₘ g 1 1
  :=
    by
      have hg := g.det_coe.symm
        replace hg : ↑ₘ g 0 1 = ↑ₘ g 0 0 * ↑ₘ g 1 1 - 1
        ;
        · rw [ det_fin_two , hc ] at hg linarith
        refine' Subtype.ext _
        conv_lhs => rw [ Matrix.eta_fin_two ↑ₘ g ]
        rw [ hc , hg ]
        simp only [ coe_mul , coe_T_zpow , coe_S , mul_fin_two ]
        trace
              "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:76:14: unsupported tactic `congrm #[[expr «expr!![ »(matrix.notation [expr _, \",\", expr _, \";\", expr _, \",\", expr _, \"]\"] [])]]"
            trace
              "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:76:14: unsupported tactic `congrm #[[expr «expr!![ »(matrix.notation [expr _, \",\", expr _, \";\", expr _, \",\", expr _, \"]\"] [])]]"
          <;>
          ring
#align modular_group.g_eq_of_c_eq_one ModularGroup.g_eq_of_c_eq_one

/-- If `1 < |z|`, then `|S • z| < 1`. -/
theorem norm_sq_S_smul_lt_one (h : 1 < normSq z) : normSq ↑(S • z) < 1 := by
  simpa [coe_S] using (inv_lt_inv z.norm_sq_pos zero_lt_one).mpr h
#align modular_group.norm_sq_S_smul_lt_one ModularGroup.norm_sq_S_smul_lt_one

/-- If `|z| < 1`, then applying `S` strictly decreases `im`. -/
theorem im_lt_im_S_smul (h : normSq z < 1) : z.im < (S • z).im :=
  by
  have : z.im < z.im / norm_sq (z : ℂ) :=
    by
    have imz : 0 < z.im := im_pos z
    apply (lt_div_iff z.norm_sq_pos).mpr
    nlinarith
  convert this
  simp only [special_linear_group.im_smul_eq_div_norm_sq]
  field_simp [norm_sq_denom_ne_zero, norm_sq_ne_zero, S]
#align modular_group.im_lt_im_S_smul ModularGroup.im_lt_im_S_smul

/-- The standard (closed) fundamental domain of the action of `SL(2,ℤ)` on `ℍ`. -/
def fd : Set ℍ :=
  { z | 1 ≤ (z : ℂ).normSq ∧ |z.re| ≤ (1 : ℝ) / 2 }
#align modular_group.fd ModularGroup.fd

/-- The standard open fundamental domain of the action of `SL(2,ℤ)` on `ℍ`. -/
def fdo : Set ℍ :=
  { z | 1 < (z : ℂ).normSq ∧ |z.re| < (1 : ℝ) / 2 }
#align modular_group.fdo ModularGroup.fdo

-- mathport name: modular_group.fd
scoped[Modular] notation "𝒟" => ModularGroup.fd

-- mathport name: modular_group.fdo
scoped[Modular] notation "𝒟ᵒ" => ModularGroup.fdo

theorem abs_two_mul_re_lt_one_of_mem_fdo (h : z ∈ 𝒟ᵒ) : |2 * z.re| < 1 :=
  by
  rw [abs_mul, abs_two, ← lt_div_iff' (zero_lt_two' ℝ)]
  exact h.2
#align modular_group.abs_two_mul_re_lt_one_of_mem_fdo ModularGroup.abs_two_mul_re_lt_one_of_mem_fdo

theorem three_lt_four_mul_im_sq_of_mem_fdo (h : z ∈ 𝒟ᵒ) : 3 < 4 * z.im ^ 2 :=
  by
  have : 1 < z.re * z.re + z.im * z.im := by simpa [Complex.norm_sq_apply] using h.1
  have := h.2
  cases abs_cases z.re <;> nlinarith
#align
  modular_group.three_lt_four_mul_im_sq_of_mem_fdo ModularGroup.three_lt_four_mul_im_sq_of_mem_fdo

/-- If `z ∈ 𝒟ᵒ`, and `n : ℤ`, then `|z + n| > 1`. -/
theorem one_lt_norm_sq_T_zpow_smul (hz : z ∈ 𝒟ᵒ) (n : ℤ) : 1 < normSq (T ^ n • z : ℍ) :=
  by
  have hz₁ : 1 < z.re * z.re + z.im * z.im := hz.1
  have hzn := Int.nneg_mul_add_sq_of_abs_le_one n (abs_two_mul_re_lt_one_of_mem_fdo hz).le
  have : 1 < (z.re + ↑n) * (z.re + ↑n) + z.im * z.im := by linarith
  simpa [coe_T_zpow, norm_sq]
#align modular_group.one_lt_norm_sq_T_zpow_smul ModularGroup.one_lt_norm_sq_T_zpow_smul

theorem eq_zero_of_mem_fdo_of_T_zpow_mem_fdo {n : ℤ} (hz : z ∈ 𝒟ᵒ) (hg : T ^ n • z ∈ 𝒟ᵒ) : n = 0 :=
  by
  suffices |(n : ℝ)| < 1 by
    rwa [← Int.cast_abs, ← Int.cast_one, Int.cast_lt, Int.abs_lt_one_iff] at this
  have h₁ := hz.2
  have h₂ := hg.2
  rw [re_T_zpow_smul] at h₂
  calc
    |(n : ℝ)| ≤ |z.re| + |z.re + (n : ℝ)| := abs_add' (n : ℝ) z.re
    _ < 1 / 2 + 1 / 2 := add_lt_add h₁ h₂
    _ = 1 := add_halves 1
    
#align
  modular_group.eq_zero_of_mem_fdo_of_T_zpow_mem_fdo ModularGroup.eq_zero_of_mem_fdo_of_T_zpow_mem_fdo

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment "/--" "Any `z : ℍ` can be moved to `𝒟` by an element of `SL(2,ℤ)`  -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `exists_smul_mem_fd [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`z]
         [":" (UpperHalfPlane.Analysis.Complex.UpperHalfPlane.Basic.upper_half_plane "ℍ")]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term∃_,_»
         "∃"
         (Lean.explicitBinders
          (Lean.unbracketedExplicitBinders
           [(Lean.binderIdent `g)]
           [":" (NumberTheory.Modular.«termSL(_,_)» "SL(" (num "2") ", " (termℤ "ℤ") ")")]))
         ","
         («term_∈_»
          (Algebra.Group.Defs.«term_•_» `g " • " `z)
          "∈"
          (Modular.NumberTheory.Modular.modular_group.fd "𝒟")))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Std.Tactic.obtain
            "obtain"
            [(Std.Tactic.RCases.rcasesPatMed
              [(Std.Tactic.RCases.rcasesPat.tuple
                "⟨"
                [(Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `g₀)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hg₀)])
                  [])]
                "⟩")])]
            []
            [":=" [(Term.app `exists_max_im [`z])]])
           []
           (Std.Tactic.obtain
            "obtain"
            [(Std.Tactic.RCases.rcasesPatMed
              [(Std.Tactic.RCases.rcasesPat.tuple
                "⟨"
                [(Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `g)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hg)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hg')])
                  [])]
                "⟩")])]
            []
            [":="
             [(Term.app `exists_row_one_eq_and_min_re [`z (Term.app `bottom_row_coprime [`g₀])])]])
           []
           (Tactic.refine' "refine'" (Term.anonymousCtor "⟨" [`g "," (Term.hole "_")] "⟩"))
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`hg₀' []]
              [(Term.typeSpec
                ":"
                (Term.forall
                 "∀"
                 [`g']
                 [(Term.typeSpec
                   ":"
                   (NumberTheory.Modular.«termSL(_,_)» "SL(" (num "2") ", " (termℤ "ℤ") ")"))]
                 ","
                 («term_≤_»
                  (Term.proj (Algebra.Group.Defs.«term_•_» `g' " • " `z) "." `im)
                  "≤"
                  (Term.proj (Algebra.Group.Defs.«term_•_» `g " • " `z) "." `im))))]
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Tactic.tacticHave_
                   "have"
                   (Term.haveDecl
                    (Term.haveIdDecl
                     [`hg'' []]
                     [(Term.typeSpec
                       ":"
                       («term_=_»
                        (Term.proj (Algebra.Group.Defs.«term_•_» `g " • " `z) "." `im)
                        "="
                        (Term.proj (Algebra.Group.Defs.«term_•_» `g₀ " • " `z) "." `im)))]
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
                           [(Tactic.rwRule [] `special_linear_group.im_smul_eq_div_norm_sq)
                            ","
                            (Tactic.rwRule [] `special_linear_group.im_smul_eq_div_norm_sq)
                            ","
                            (Tactic.rwRule [] `denom_apply)
                            ","
                            (Tactic.rwRule [] `denom_apply)
                            ","
                            (Tactic.rwRule [] `hg)]
                           "]")
                          [])]))))))
                  []
                  (Std.Tactic.Simpa.simpa
                   "simpa"
                   []
                   []
                   (Std.Tactic.Simpa.simpaArgsRest
                    []
                    []
                    ["only"]
                    [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `hg'')] "]")]
                    ["using" `hg₀]))]))))))
           []
           (Tactic.constructor "constructor")
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Mathlib.Tactic.Contrapose.contrapose! "contrapose!" [`hg₀' []])
             []
             (Tactic.refine'
              "refine'"
              (Term.anonymousCtor "⟨" [(«term_*_» `S "*" `g) "," (Term.hole "_")] "⟩"))
             []
             (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_smul)] "]") [])
             []
             (Tactic.exact "exact" (Term.app `im_lt_im_S_smul [`hg₀']))])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.tacticShow_
              "show"
              («term_≤_»
               («term|___|»
                (group "|")
                (Term.proj (Algebra.Group.Defs.«term_•_» `g " • " `z) "." `re)
                (group)
                "|")
               "≤"
               («term_/_» (num "1") "/" (num "2"))))
             []
             (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `abs_le)] "]") [])
             []
             (Tactic.constructor "constructor")
             []
             (tactic__
              (cdotTk (patternIgnore (token.«· » "·")))
              [(Mathlib.Tactic.Contrapose.contrapose! "contrapose!" [`hg' []])
               []
               (Tactic.refine'
                "refine'"
                (Term.anonymousCtor
                 "⟨"
                 [(«term_*_» `T "*" `g)
                  ","
                  (Term.proj (Term.app `T_mul_apply_one [(Term.hole "_")]) "." `symm)
                  ","
                  (Term.hole "_")]
                 "⟩"))
               []
               (Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule [] `mul_smul) "," (Tactic.rwRule [] `re_T_smul)]
                 "]")
                [])
               []
               (Tactic.«tactic_<;>_»
                (Tactic.«tactic_<;>_»
                 (Tactic.cases
                  "cases"
                  [(Tactic.casesTarget
                    []
                    (Term.app
                     `abs_cases
                     [(«term_+_»
                       (Term.proj (Algebra.Group.Defs.«term_•_» `g " • " `z) "." `re)
                       "+"
                       (num "1"))]))]
                  []
                  [])
                 "<;>"
                 (Tactic.cases
                  "cases"
                  [(Tactic.casesTarget
                    []
                    (Term.app
                     `abs_cases
                     [(Term.proj (Algebra.Group.Defs.«term_•_» `g " • " `z) "." `re)]))]
                  []
                  []))
                "<;>"
                (linarith "linarith" [] (linarithArgsRest [] [] [])))])
             []
             (tactic__
              (cdotTk (patternIgnore (token.«· » "·")))
              [(Mathlib.Tactic.Contrapose.contrapose! "contrapose!" [`hg' []])
               []
               (Tactic.refine'
                "refine'"
                (Term.anonymousCtor
                 "⟨"
                 [(«term_*_» («term_⁻¹» `T "⁻¹") "*" `g)
                  ","
                  (Term.proj (Term.app `T_inv_mul_apply_one [(Term.hole "_")]) "." `symm)
                  ","
                  (Term.hole "_")]
                 "⟩"))
               []
               (Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule [] `mul_smul) "," (Tactic.rwRule [] `re_T_inv_smul)]
                 "]")
                [])
               []
               (Tactic.«tactic_<;>_»
                (Tactic.«tactic_<;>_»
                 (Tactic.cases
                  "cases"
                  [(Tactic.casesTarget
                    []
                    (Term.app
                     `abs_cases
                     [(«term_-_»
                       (Term.proj (Algebra.Group.Defs.«term_•_» `g " • " `z) "." `re)
                       "-"
                       (num "1"))]))]
                  []
                  [])
                 "<;>"
                 (Tactic.cases
                  "cases"
                  [(Tactic.casesTarget
                    []
                    (Term.app
                     `abs_cases
                     [(Term.proj (Algebra.Group.Defs.«term_•_» `g " • " `z) "." `re)]))]
                  []
                  []))
                "<;>"
                (linarith "linarith" [] (linarithArgsRest [] [] [])))])])])))
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
         [(Std.Tactic.obtain
           "obtain"
           [(Std.Tactic.RCases.rcasesPatMed
             [(Std.Tactic.RCases.rcasesPat.tuple
               "⟨"
               [(Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `g₀)])
                 [])
                ","
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hg₀)])
                 [])]
               "⟩")])]
           []
           [":=" [(Term.app `exists_max_im [`z])]])
          []
          (Std.Tactic.obtain
           "obtain"
           [(Std.Tactic.RCases.rcasesPatMed
             [(Std.Tactic.RCases.rcasesPat.tuple
               "⟨"
               [(Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `g)])
                 [])
                ","
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hg)])
                 [])
                ","
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hg')])
                 [])]
               "⟩")])]
           []
           [":="
            [(Term.app `exists_row_one_eq_and_min_re [`z (Term.app `bottom_row_coprime [`g₀])])]])
          []
          (Tactic.refine' "refine'" (Term.anonymousCtor "⟨" [`g "," (Term.hole "_")] "⟩"))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`hg₀' []]
             [(Term.typeSpec
               ":"
               (Term.forall
                "∀"
                [`g']
                [(Term.typeSpec
                  ":"
                  (NumberTheory.Modular.«termSL(_,_)» "SL(" (num "2") ", " (termℤ "ℤ") ")"))]
                ","
                («term_≤_»
                 (Term.proj (Algebra.Group.Defs.«term_•_» `g' " • " `z) "." `im)
                 "≤"
                 (Term.proj (Algebra.Group.Defs.«term_•_» `g " • " `z) "." `im))))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.tacticHave_
                  "have"
                  (Term.haveDecl
                   (Term.haveIdDecl
                    [`hg'' []]
                    [(Term.typeSpec
                      ":"
                      («term_=_»
                       (Term.proj (Algebra.Group.Defs.«term_•_» `g " • " `z) "." `im)
                       "="
                       (Term.proj (Algebra.Group.Defs.«term_•_» `g₀ " • " `z) "." `im)))]
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
                          [(Tactic.rwRule [] `special_linear_group.im_smul_eq_div_norm_sq)
                           ","
                           (Tactic.rwRule [] `special_linear_group.im_smul_eq_div_norm_sq)
                           ","
                           (Tactic.rwRule [] `denom_apply)
                           ","
                           (Tactic.rwRule [] `denom_apply)
                           ","
                           (Tactic.rwRule [] `hg)]
                          "]")
                         [])]))))))
                 []
                 (Std.Tactic.Simpa.simpa
                  "simpa"
                  []
                  []
                  (Std.Tactic.Simpa.simpaArgsRest
                   []
                   []
                   ["only"]
                   [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `hg'')] "]")]
                   ["using" `hg₀]))]))))))
          []
          (Tactic.constructor "constructor")
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Mathlib.Tactic.Contrapose.contrapose! "contrapose!" [`hg₀' []])
            []
            (Tactic.refine'
             "refine'"
             (Term.anonymousCtor "⟨" [(«term_*_» `S "*" `g) "," (Term.hole "_")] "⟩"))
            []
            (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_smul)] "]") [])
            []
            (Tactic.exact "exact" (Term.app `im_lt_im_S_smul [`hg₀']))])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.tacticShow_
             "show"
             («term_≤_»
              («term|___|»
               (group "|")
               (Term.proj (Algebra.Group.Defs.«term_•_» `g " • " `z) "." `re)
               (group)
               "|")
              "≤"
              («term_/_» (num "1") "/" (num "2"))))
            []
            (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `abs_le)] "]") [])
            []
            (Tactic.constructor "constructor")
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(Mathlib.Tactic.Contrapose.contrapose! "contrapose!" [`hg' []])
              []
              (Tactic.refine'
               "refine'"
               (Term.anonymousCtor
                "⟨"
                [(«term_*_» `T "*" `g)
                 ","
                 (Term.proj (Term.app `T_mul_apply_one [(Term.hole "_")]) "." `symm)
                 ","
                 (Term.hole "_")]
                "⟩"))
              []
              (Tactic.rwSeq
               "rw"
               []
               (Tactic.rwRuleSeq
                "["
                [(Tactic.rwRule [] `mul_smul) "," (Tactic.rwRule [] `re_T_smul)]
                "]")
               [])
              []
              (Tactic.«tactic_<;>_»
               (Tactic.«tactic_<;>_»
                (Tactic.cases
                 "cases"
                 [(Tactic.casesTarget
                   []
                   (Term.app
                    `abs_cases
                    [(«term_+_»
                      (Term.proj (Algebra.Group.Defs.«term_•_» `g " • " `z) "." `re)
                      "+"
                      (num "1"))]))]
                 []
                 [])
                "<;>"
                (Tactic.cases
                 "cases"
                 [(Tactic.casesTarget
                   []
                   (Term.app
                    `abs_cases
                    [(Term.proj (Algebra.Group.Defs.«term_•_» `g " • " `z) "." `re)]))]
                 []
                 []))
               "<;>"
               (linarith "linarith" [] (linarithArgsRest [] [] [])))])
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(Mathlib.Tactic.Contrapose.contrapose! "contrapose!" [`hg' []])
              []
              (Tactic.refine'
               "refine'"
               (Term.anonymousCtor
                "⟨"
                [(«term_*_» («term_⁻¹» `T "⁻¹") "*" `g)
                 ","
                 (Term.proj (Term.app `T_inv_mul_apply_one [(Term.hole "_")]) "." `symm)
                 ","
                 (Term.hole "_")]
                "⟩"))
              []
              (Tactic.rwSeq
               "rw"
               []
               (Tactic.rwRuleSeq
                "["
                [(Tactic.rwRule [] `mul_smul) "," (Tactic.rwRule [] `re_T_inv_smul)]
                "]")
               [])
              []
              (Tactic.«tactic_<;>_»
               (Tactic.«tactic_<;>_»
                (Tactic.cases
                 "cases"
                 [(Tactic.casesTarget
                   []
                   (Term.app
                    `abs_cases
                    [(«term_-_»
                      (Term.proj (Algebra.Group.Defs.«term_•_» `g " • " `z) "." `re)
                      "-"
                      (num "1"))]))]
                 []
                 [])
                "<;>"
                (Tactic.cases
                 "cases"
                 [(Tactic.casesTarget
                   []
                   (Term.app
                    `abs_cases
                    [(Term.proj (Algebra.Group.Defs.«term_•_» `g " • " `z) "." `re)]))]
                 []
                 []))
               "<;>"
               (linarith "linarith" [] (linarithArgsRest [] [] [])))])])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.tacticShow_
         "show"
         («term_≤_»
          («term|___|»
           (group "|")
           (Term.proj (Algebra.Group.Defs.«term_•_» `g " • " `z) "." `re)
           (group)
           "|")
          "≤"
          («term_/_» (num "1") "/" (num "2"))))
        []
        (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `abs_le)] "]") [])
        []
        (Tactic.constructor "constructor")
        []
        (tactic__
         (cdotTk (patternIgnore (token.«· » "·")))
         [(Mathlib.Tactic.Contrapose.contrapose! "contrapose!" [`hg' []])
          []
          (Tactic.refine'
           "refine'"
           (Term.anonymousCtor
            "⟨"
            [(«term_*_» `T "*" `g)
             ","
             (Term.proj (Term.app `T_mul_apply_one [(Term.hole "_")]) "." `symm)
             ","
             (Term.hole "_")]
            "⟩"))
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `mul_smul) "," (Tactic.rwRule [] `re_T_smul)]
            "]")
           [])
          []
          (Tactic.«tactic_<;>_»
           (Tactic.«tactic_<;>_»
            (Tactic.cases
             "cases"
             [(Tactic.casesTarget
               []
               (Term.app
                `abs_cases
                [(«term_+_»
                  (Term.proj (Algebra.Group.Defs.«term_•_» `g " • " `z) "." `re)
                  "+"
                  (num "1"))]))]
             []
             [])
            "<;>"
            (Tactic.cases
             "cases"
             [(Tactic.casesTarget
               []
               (Term.app
                `abs_cases
                [(Term.proj (Algebra.Group.Defs.«term_•_» `g " • " `z) "." `re)]))]
             []
             []))
           "<;>"
           (linarith "linarith" [] (linarithArgsRest [] [] [])))])
        []
        (tactic__
         (cdotTk (patternIgnore (token.«· » "·")))
         [(Mathlib.Tactic.Contrapose.contrapose! "contrapose!" [`hg' []])
          []
          (Tactic.refine'
           "refine'"
           (Term.anonymousCtor
            "⟨"
            [(«term_*_» («term_⁻¹» `T "⁻¹") "*" `g)
             ","
             (Term.proj (Term.app `T_inv_mul_apply_one [(Term.hole "_")]) "." `symm)
             ","
             (Term.hole "_")]
            "⟩"))
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `mul_smul) "," (Tactic.rwRule [] `re_T_inv_smul)]
            "]")
           [])
          []
          (Tactic.«tactic_<;>_»
           (Tactic.«tactic_<;>_»
            (Tactic.cases
             "cases"
             [(Tactic.casesTarget
               []
               (Term.app
                `abs_cases
                [(«term_-_»
                  (Term.proj (Algebra.Group.Defs.«term_•_» `g " • " `z) "." `re)
                  "-"
                  (num "1"))]))]
             []
             [])
            "<;>"
            (Tactic.cases
             "cases"
             [(Tactic.casesTarget
               []
               (Term.app
                `abs_cases
                [(Term.proj (Algebra.Group.Defs.«term_•_» `g " • " `z) "." `re)]))]
             []
             []))
           "<;>"
           (linarith "linarith" [] (linarithArgsRest [] [] [])))])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Mathlib.Tactic.Contrapose.contrapose! "contrapose!" [`hg' []])
        []
        (Tactic.refine'
         "refine'"
         (Term.anonymousCtor
          "⟨"
          [(«term_*_» («term_⁻¹» `T "⁻¹") "*" `g)
           ","
           (Term.proj (Term.app `T_inv_mul_apply_one [(Term.hole "_")]) "." `symm)
           ","
           (Term.hole "_")]
          "⟩"))
        []
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule [] `mul_smul) "," (Tactic.rwRule [] `re_T_inv_smul)]
          "]")
         [])
        []
        (Tactic.«tactic_<;>_»
         (Tactic.«tactic_<;>_»
          (Tactic.cases
           "cases"
           [(Tactic.casesTarget
             []
             (Term.app
              `abs_cases
              [(«term_-_»
                (Term.proj (Algebra.Group.Defs.«term_•_» `g " • " `z) "." `re)
                "-"
                (num "1"))]))]
           []
           [])
          "<;>"
          (Tactic.cases
           "cases"
           [(Tactic.casesTarget
             []
             (Term.app
              `abs_cases
              [(Term.proj (Algebra.Group.Defs.«term_•_» `g " • " `z) "." `re)]))]
           []
           []))
         "<;>"
         (linarith "linarith" [] (linarithArgsRest [] [] [])))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.«tactic_<;>_»
       (Tactic.«tactic_<;>_»
        (Tactic.cases
         "cases"
         [(Tactic.casesTarget
           []
           (Term.app
            `abs_cases
            [(«term_-_»
              (Term.proj (Algebra.Group.Defs.«term_•_» `g " • " `z) "." `re)
              "-"
              (num "1"))]))]
         []
         [])
        "<;>"
        (Tactic.cases
         "cases"
         [(Tactic.casesTarget
           []
           (Term.app `abs_cases [(Term.proj (Algebra.Group.Defs.«term_•_» `g " • " `z) "." `re)]))]
         []
         []))
       "<;>"
       (linarith "linarith" [] (linarithArgsRest [] [] [])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (linarith "linarith" [] (linarithArgsRest [] [] []))
[PrettyPrinter.parenthesize] ...precedences are 2 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
      (Tactic.«tactic_<;>_»
       (Tactic.cases
        "cases"
        [(Tactic.casesTarget
          []
          (Term.app
           `abs_cases
           [(«term_-_»
             (Term.proj (Algebra.Group.Defs.«term_•_» `g " • " `z) "." `re)
             "-"
             (num "1"))]))]
        []
        [])
       "<;>"
       (Tactic.cases
        "cases"
        [(Tactic.casesTarget
          []
          (Term.app `abs_cases [(Term.proj (Algebra.Group.Defs.«term_•_» `g " • " `z) "." `re)]))]
        []
        []))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.cases
       "cases"
       [(Tactic.casesTarget
         []
         (Term.app `abs_cases [(Term.proj (Algebra.Group.Defs.«term_•_» `g " • " `z) "." `re)]))]
       []
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `abs_cases [(Term.proj (Algebra.Group.Defs.«term_•_» `g " • " `z) "." `re)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Algebra.Group.Defs.«term_•_» `g " • " `z) "." `re)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Algebra.Group.Defs.«term_•_» `g " • " `z)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `z
[PrettyPrinter.parenthesize] ...precedences are 73 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 73, term))
      `g
[PrettyPrinter.parenthesize] ...precedences are 74 >? 1024, (none, [anonymous]) <=? (some 73, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 73, (some 73, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Algebra.Group.Defs.«term_•_» `g " • " `z)
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `abs_cases
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 2 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
      (Tactic.cases
       "cases"
       [(Tactic.casesTarget
         []
         (Term.app
          `abs_cases
          [(«term_-_»
            (Term.proj (Algebra.Group.Defs.«term_•_» `g " • " `z) "." `re)
            "-"
            (num "1"))]))]
       []
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `abs_cases
       [(«term_-_» (Term.proj (Algebra.Group.Defs.«term_•_» `g " • " `z) "." `re) "-" (num "1"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_-_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_-_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_-_» (Term.proj (Algebra.Group.Defs.«term_•_» `g " • " `z) "." `re) "-" (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      (Term.proj (Algebra.Group.Defs.«term_•_» `g " • " `z) "." `re)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Algebra.Group.Defs.«term_•_» `g " • " `z)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `z
[PrettyPrinter.parenthesize] ...precedences are 73 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 73, term))
      `g
[PrettyPrinter.parenthesize] ...precedences are 74 >? 1024, (none, [anonymous]) <=? (some 73, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 73, (some 73, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Algebra.Group.Defs.«term_•_» `g " • " `z)
     ")")
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_-_»
      (Term.proj (Term.paren "(" (Algebra.Group.Defs.«term_•_» `g " • " `z) ")") "." `re)
      "-"
      (num "1"))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `abs_cases
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `mul_smul) "," (Tactic.rwRule [] `re_T_inv_smul)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `re_T_inv_smul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_smul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine'
       "refine'"
       (Term.anonymousCtor
        "⟨"
        [(«term_*_» («term_⁻¹» `T "⁻¹") "*" `g)
         ","
         (Term.proj (Term.app `T_inv_mul_apply_one [(Term.hole "_")]) "." `symm)
         ","
         (Term.hole "_")]
        "⟩"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(«term_*_» («term_⁻¹» `T "⁻¹") "*" `g)
        ","
        (Term.proj (Term.app `T_inv_mul_apply_one [(Term.hole "_")]) "." `symm)
        ","
        (Term.hole "_")]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.app `T_inv_mul_apply_one [(Term.hole "_")]) "." `symm)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `T_inv_mul_apply_one [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `T_inv_mul_apply_one
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `T_inv_mul_apply_one [(Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_» («term_⁻¹» `T "⁻¹") "*" `g)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      («term_⁻¹» `T "⁻¹")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `T
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.Contrapose.contrapose! "contrapose!" [`hg' []])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Mathlib.Tactic.Contrapose.contrapose! "contrapose!" [`hg' []])
        []
        (Tactic.refine'
         "refine'"
         (Term.anonymousCtor
          "⟨"
          [(«term_*_» `T "*" `g)
           ","
           (Term.proj (Term.app `T_mul_apply_one [(Term.hole "_")]) "." `symm)
           ","
           (Term.hole "_")]
          "⟩"))
        []
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_smul) "," (Tactic.rwRule [] `re_T_smul)] "]")
         [])
        []
        (Tactic.«tactic_<;>_»
         (Tactic.«tactic_<;>_»
          (Tactic.cases
           "cases"
           [(Tactic.casesTarget
             []
             (Term.app
              `abs_cases
              [(«term_+_»
                (Term.proj (Algebra.Group.Defs.«term_•_» `g " • " `z) "." `re)
                "+"
                (num "1"))]))]
           []
           [])
          "<;>"
          (Tactic.cases
           "cases"
           [(Tactic.casesTarget
             []
             (Term.app
              `abs_cases
              [(Term.proj (Algebra.Group.Defs.«term_•_» `g " • " `z) "." `re)]))]
           []
           []))
         "<;>"
         (linarith "linarith" [] (linarithArgsRest [] [] [])))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.«tactic_<;>_»
       (Tactic.«tactic_<;>_»
        (Tactic.cases
         "cases"
         [(Tactic.casesTarget
           []
           (Term.app
            `abs_cases
            [(«term_+_»
              (Term.proj (Algebra.Group.Defs.«term_•_» `g " • " `z) "." `re)
              "+"
              (num "1"))]))]
         []
         [])
        "<;>"
        (Tactic.cases
         "cases"
         [(Tactic.casesTarget
           []
           (Term.app `abs_cases [(Term.proj (Algebra.Group.Defs.«term_•_» `g " • " `z) "." `re)]))]
         []
         []))
       "<;>"
       (linarith "linarith" [] (linarithArgsRest [] [] [])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (linarith "linarith" [] (linarithArgsRest [] [] []))
[PrettyPrinter.parenthesize] ...precedences are 2 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
      (Tactic.«tactic_<;>_»
       (Tactic.cases
        "cases"
        [(Tactic.casesTarget
          []
          (Term.app
           `abs_cases
           [(«term_+_»
             (Term.proj (Algebra.Group.Defs.«term_•_» `g " • " `z) "." `re)
             "+"
             (num "1"))]))]
        []
        [])
       "<;>"
       (Tactic.cases
        "cases"
        [(Tactic.casesTarget
          []
          (Term.app `abs_cases [(Term.proj (Algebra.Group.Defs.«term_•_» `g " • " `z) "." `re)]))]
        []
        []))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.cases
       "cases"
       [(Tactic.casesTarget
         []
         (Term.app `abs_cases [(Term.proj (Algebra.Group.Defs.«term_•_» `g " • " `z) "." `re)]))]
       []
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `abs_cases [(Term.proj (Algebra.Group.Defs.«term_•_» `g " • " `z) "." `re)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Algebra.Group.Defs.«term_•_» `g " • " `z) "." `re)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Algebra.Group.Defs.«term_•_» `g " • " `z)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `z
[PrettyPrinter.parenthesize] ...precedences are 73 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 73, term))
      `g
[PrettyPrinter.parenthesize] ...precedences are 74 >? 1024, (none, [anonymous]) <=? (some 73, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 73, (some 73, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Algebra.Group.Defs.«term_•_» `g " • " `z)
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `abs_cases
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 2 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
      (Tactic.cases
       "cases"
       [(Tactic.casesTarget
         []
         (Term.app
          `abs_cases
          [(«term_+_»
            (Term.proj (Algebra.Group.Defs.«term_•_» `g " • " `z) "." `re)
            "+"
            (num "1"))]))]
       []
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `abs_cases
       [(«term_+_» (Term.proj (Algebra.Group.Defs.«term_•_» `g " • " `z) "." `re) "+" (num "1"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_+_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_+_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_» (Term.proj (Algebra.Group.Defs.«term_•_» `g " • " `z) "." `re) "+" (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      (Term.proj (Algebra.Group.Defs.«term_•_» `g " • " `z) "." `re)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Algebra.Group.Defs.«term_•_» `g " • " `z)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `z
[PrettyPrinter.parenthesize] ...precedences are 73 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 73, term))
      `g
[PrettyPrinter.parenthesize] ...precedences are 74 >? 1024, (none, [anonymous]) <=? (some 73, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 73, (some 73, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Algebra.Group.Defs.«term_•_» `g " • " `z)
     ")")
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_+_»
      (Term.proj (Term.paren "(" (Algebra.Group.Defs.«term_•_» `g " • " `z) ")") "." `re)
      "+"
      (num "1"))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `abs_cases
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_smul) "," (Tactic.rwRule [] `re_T_smul)] "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `re_T_smul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_smul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine'
       "refine'"
       (Term.anonymousCtor
        "⟨"
        [(«term_*_» `T "*" `g)
         ","
         (Term.proj (Term.app `T_mul_apply_one [(Term.hole "_")]) "." `symm)
         ","
         (Term.hole "_")]
        "⟩"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(«term_*_» `T "*" `g)
        ","
        (Term.proj (Term.app `T_mul_apply_one [(Term.hole "_")]) "." `symm)
        ","
        (Term.hole "_")]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.app `T_mul_apply_one [(Term.hole "_")]) "." `symm)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `T_mul_apply_one [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `T_mul_apply_one
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `T_mul_apply_one [(Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_» `T "*" `g)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `T
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.Contrapose.contrapose! "contrapose!" [`hg' []])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.constructor "constructor")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `abs_le)] "]") [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `abs_le
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticShow_
       "show"
       («term_≤_»
        («term|___|»
         (group "|")
         (Term.proj (Algebra.Group.Defs.«term_•_» `g " • " `z) "." `re)
         (group)
         "|")
        "≤"
        («term_/_» (num "1") "/" (num "2"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≤_»
       («term|___|»
        (group "|")
        (Term.proj (Algebra.Group.Defs.«term_•_» `g " • " `z) "." `re)
        (group)
        "|")
       "≤"
       («term_/_» (num "1") "/" (num "2")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_/_» (num "1") "/" (num "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      («term|___|»
       (group "|")
       (Term.proj (Algebra.Group.Defs.«term_•_» `g " • " `z) "." `re)
       (group)
       "|")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Algebra.Group.Defs.«term_•_» `g " • " `z) "." `re)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Algebra.Group.Defs.«term_•_» `g " • " `z)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `z
[PrettyPrinter.parenthesize] ...precedences are 73 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 73, term))
      `g
[PrettyPrinter.parenthesize] ...precedences are 74 >? 1024, (none, [anonymous]) <=? (some 73, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 73, (some 73, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Algebra.Group.Defs.«term_•_» `g " • " `z)
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Mathlib.Tactic.Contrapose.contrapose! "contrapose!" [`hg₀' []])
        []
        (Tactic.refine'
         "refine'"
         (Term.anonymousCtor "⟨" [(«term_*_» `S "*" `g) "," (Term.hole "_")] "⟩"))
        []
        (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_smul)] "]") [])
        []
        (Tactic.exact "exact" (Term.app `im_lt_im_S_smul [`hg₀']))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" (Term.app `im_lt_im_S_smul [`hg₀']))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `im_lt_im_S_smul [`hg₀'])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hg₀'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `im_lt_im_S_smul
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_smul)] "]") [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_smul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine'
       "refine'"
       (Term.anonymousCtor "⟨" [(«term_*_» `S "*" `g) "," (Term.hole "_")] "⟩"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [(«term_*_» `S "*" `g) "," (Term.hole "_")] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_» `S "*" `g)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `S
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.Contrapose.contrapose! "contrapose!" [`hg₀' []])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.constructor "constructor")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`hg₀' []]
         [(Term.typeSpec
           ":"
           (Term.forall
            "∀"
            [`g']
            [(Term.typeSpec
              ":"
              (NumberTheory.Modular.«termSL(_,_)» "SL(" (num "2") ", " (termℤ "ℤ") ")"))]
            ","
            («term_≤_»
             (Term.proj (Algebra.Group.Defs.«term_•_» `g' " • " `z) "." `im)
             "≤"
             (Term.proj (Algebra.Group.Defs.«term_•_» `g " • " `z) "." `im))))]
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                [`hg'' []]
                [(Term.typeSpec
                  ":"
                  («term_=_»
                   (Term.proj (Algebra.Group.Defs.«term_•_» `g " • " `z) "." `im)
                   "="
                   (Term.proj (Algebra.Group.Defs.«term_•_» `g₀ " • " `z) "." `im)))]
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
                      [(Tactic.rwRule [] `special_linear_group.im_smul_eq_div_norm_sq)
                       ","
                       (Tactic.rwRule [] `special_linear_group.im_smul_eq_div_norm_sq)
                       ","
                       (Tactic.rwRule [] `denom_apply)
                       ","
                       (Tactic.rwRule [] `denom_apply)
                       ","
                       (Tactic.rwRule [] `hg)]
                      "]")
                     [])]))))))
             []
             (Std.Tactic.Simpa.simpa
              "simpa"
              []
              []
              (Std.Tactic.Simpa.simpaArgsRest
               []
               []
               ["only"]
               [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `hg'')] "]")]
               ["using" `hg₀]))]))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`hg'' []]
             [(Term.typeSpec
               ":"
               («term_=_»
                (Term.proj (Algebra.Group.Defs.«term_•_» `g " • " `z) "." `im)
                "="
                (Term.proj (Algebra.Group.Defs.«term_•_» `g₀ " • " `z) "." `im)))]
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
                   [(Tactic.rwRule [] `special_linear_group.im_smul_eq_div_norm_sq)
                    ","
                    (Tactic.rwRule [] `special_linear_group.im_smul_eq_div_norm_sq)
                    ","
                    (Tactic.rwRule [] `denom_apply)
                    ","
                    (Tactic.rwRule [] `denom_apply)
                    ","
                    (Tactic.rwRule [] `hg)]
                   "]")
                  [])]))))))
          []
          (Std.Tactic.Simpa.simpa
           "simpa"
           []
           []
           (Std.Tactic.Simpa.simpaArgsRest
            []
            []
            ["only"]
            [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `hg'')] "]")]
            ["using" `hg₀]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Simpa.simpa
       "simpa"
       []
       []
       (Std.Tactic.Simpa.simpaArgsRest
        []
        []
        ["only"]
        [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `hg'')] "]")]
        ["using" `hg₀]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hg₀
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hg''
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`hg'' []]
         [(Term.typeSpec
           ":"
           («term_=_»
            (Term.proj (Algebra.Group.Defs.«term_•_» `g " • " `z) "." `im)
            "="
            (Term.proj (Algebra.Group.Defs.«term_•_» `g₀ " • " `z) "." `im)))]
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
               [(Tactic.rwRule [] `special_linear_group.im_smul_eq_div_norm_sq)
                ","
                (Tactic.rwRule [] `special_linear_group.im_smul_eq_div_norm_sq)
                ","
                (Tactic.rwRule [] `denom_apply)
                ","
                (Tactic.rwRule [] `denom_apply)
                ","
                (Tactic.rwRule [] `hg)]
               "]")
              [])]))))))
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
            [(Tactic.rwRule [] `special_linear_group.im_smul_eq_div_norm_sq)
             ","
             (Tactic.rwRule [] `special_linear_group.im_smul_eq_div_norm_sq)
             ","
             (Tactic.rwRule [] `denom_apply)
             ","
             (Tactic.rwRule [] `denom_apply)
             ","
             (Tactic.rwRule [] `hg)]
            "]")
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `special_linear_group.im_smul_eq_div_norm_sq)
         ","
         (Tactic.rwRule [] `special_linear_group.im_smul_eq_div_norm_sq)
         ","
         (Tactic.rwRule [] `denom_apply)
         ","
         (Tactic.rwRule [] `denom_apply)
         ","
         (Tactic.rwRule [] `hg)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hg
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `denom_apply
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `denom_apply
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `special_linear_group.im_smul_eq_div_norm_sq
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `special_linear_group.im_smul_eq_div_norm_sq
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Term.proj (Algebra.Group.Defs.«term_•_» `g " • " `z) "." `im)
       "="
       (Term.proj (Algebra.Group.Defs.«term_•_» `g₀ " • " `z) "." `im))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Algebra.Group.Defs.«term_•_» `g₀ " • " `z) "." `im)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Algebra.Group.Defs.«term_•_» `g₀ " • " `z)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `z
[PrettyPrinter.parenthesize] ...precedences are 73 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 73, term))
      `g₀
[PrettyPrinter.parenthesize] ...precedences are 74 >? 1024, (none, [anonymous]) <=? (some 73, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 73, (some 73, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Algebra.Group.Defs.«term_•_» `g₀ " • " `z)
     ")")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.proj (Algebra.Group.Defs.«term_•_» `g " • " `z) "." `im)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Algebra.Group.Defs.«term_•_» `g " • " `z)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `z
[PrettyPrinter.parenthesize] ...precedences are 73 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 73, term))
      `g
[PrettyPrinter.parenthesize] ...precedences are 74 >? 1024, (none, [anonymous]) <=? (some 73, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 73, (some 73, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Algebra.Group.Defs.«term_•_» `g " • " `z)
     ")")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.forall
       "∀"
       [`g']
       [(Term.typeSpec
         ":"
         (NumberTheory.Modular.«termSL(_,_)» "SL(" (num "2") ", " (termℤ "ℤ") ")"))]
       ","
       («term_≤_»
        (Term.proj (Algebra.Group.Defs.«term_•_» `g' " • " `z) "." `im)
        "≤"
        (Term.proj (Algebra.Group.Defs.«term_•_» `g " • " `z) "." `im)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≤_»
       (Term.proj (Algebra.Group.Defs.«term_•_» `g' " • " `z) "." `im)
       "≤"
       (Term.proj (Algebra.Group.Defs.«term_•_» `g " • " `z) "." `im))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Algebra.Group.Defs.«term_•_» `g " • " `z) "." `im)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Algebra.Group.Defs.«term_•_» `g " • " `z)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `z
[PrettyPrinter.parenthesize] ...precedences are 73 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 73, term))
      `g
[PrettyPrinter.parenthesize] ...precedences are 74 >? 1024, (none, [anonymous]) <=? (some 73, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 73, (some 73, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Algebra.Group.Defs.«term_•_» `g " • " `z)
     ")")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.proj (Algebra.Group.Defs.«term_•_» `g' " • " `z) "." `im)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Algebra.Group.Defs.«term_•_» `g' " • " `z)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `z
[PrettyPrinter.parenthesize] ...precedences are 73 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 73, term))
      `g'
[PrettyPrinter.parenthesize] ...precedences are 74 >? 1024, (none, [anonymous]) <=? (some 73, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 73, (some 73, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Algebra.Group.Defs.«term_•_» `g' " • " `z)
     ")")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (NumberTheory.Modular.«termSL(_,_)» "SL(" (num "2") ", " (termℤ "ℤ") ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.Modular.«termSL(_,_)»', expected 'NumberTheory.Modular.termSL(_,_)._@.NumberTheory.Modular._hyg.8'
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
/-- Any `z : ℍ` can be moved to `𝒟` by an element of `SL(2,ℤ)`  -/
  theorem
    exists_smul_mem_fd
    ( z : ℍ ) : ∃ g : SL( 2 , ℤ ) , g • z ∈ 𝒟
    :=
      by
        obtain ⟨ g₀ , hg₀ ⟩ := exists_max_im z
          obtain ⟨ g , hg , hg' ⟩ := exists_row_one_eq_and_min_re z bottom_row_coprime g₀
          refine' ⟨ g , _ ⟩
          have
            hg₀'
              : ∀ g' : SL( 2 , ℤ ) , g' • z . im ≤ g • z . im
              :=
              by
                have
                    hg''
                      : g • z . im = g₀ • z . im
                      :=
                      by
                        rw
                          [
                            special_linear_group.im_smul_eq_div_norm_sq
                              ,
                              special_linear_group.im_smul_eq_div_norm_sq
                              ,
                              denom_apply
                              ,
                              denom_apply
                              ,
                              hg
                            ]
                  simpa only [ hg'' ] using hg₀
          constructor
          · contrapose! hg₀' refine' ⟨ S * g , _ ⟩ rw [ mul_smul ] exact im_lt_im_S_smul hg₀'
          ·
            show | g • z . re | ≤ 1 / 2
              rw [ abs_le ]
              constructor
              ·
                contrapose! hg'
                  refine' ⟨ T * g , T_mul_apply_one _ . symm , _ ⟩
                  rw [ mul_smul , re_T_smul ]
                  cases abs_cases g • z . re + 1 <;> cases abs_cases g • z . re <;> linarith
              ·
                contrapose! hg'
                  refine' ⟨ T ⁻¹ * g , T_inv_mul_apply_one _ . symm , _ ⟩
                  rw [ mul_smul , re_T_inv_smul ]
                  cases abs_cases g • z . re - 1 <;> cases abs_cases g • z . re <;> linarith
#align modular_group.exists_smul_mem_fd ModularGroup.exists_smul_mem_fd

section UniqueRepresentative

variable {z}

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment "/--" "An auxiliary result en route to `modular_group.c_eq_zero`. -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `abs_c_le_one [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`hz]
         [":" («term_∈_» `z "∈" (Modular.NumberTheory.Modular.modular_group.fdo "𝒟ᵒ"))]
         []
         ")")
        (Term.explicitBinder
         "("
         [`hg]
         [":"
          («term_∈_»
           (Algebra.Group.Defs.«term_•_» `g " • " `z)
           "∈"
           (Modular.NumberTheory.Modular.modular_group.fdo "𝒟ᵒ"))]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_≤_»
         («term|___|»
          (group "|")
          (Term.app (NumberTheory.Modular.«term↑ₘ_» "↑ₘ" `g) [(num "1") (num "0")])
          (group)
          "|")
         "≤"
         (num "1"))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.tacticLet_
            "let"
            (Term.letDecl
             (Term.letIdDecl
              `c'
              []
              [(Term.typeSpec ":" (termℤ "ℤ"))]
              ":="
              (Term.app (NumberTheory.Modular.«term↑ₘ_» "↑ₘ" `g) [(num "1") (num "0")]))))
           []
           (Tactic.tacticLet_
            "let"
            (Term.letDecl
             (Term.letIdDecl
              `c
              []
              [(Term.typeSpec ":" (Data.Real.Basic.termℝ "ℝ"))]
              ":="
              (Term.typeAscription "(" `c' ":" [(Data.Real.Basic.termℝ "ℝ")] ")"))))
           []
           (Tactic.tacticSuffices_
            "suffices"
            (Term.sufficesDecl
             []
             («term_<_» («term_*_» (num "3") "*" («term_^_» `c "^" (num "2"))) "<" (num "4"))
             (Term.byTactic'
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Int.cast_pow)
                    ","
                    (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Int.cast_three)
                    ","
                    (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Int.cast_four)
                    ","
                    (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Int.cast_mul)
                    ","
                    (Tactic.rwRule [] `Int.cast_lt)]
                   "]")
                  [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
                 []
                 (Mathlib.Tactic.replace'
                  "replace"
                  [`this []]
                  [(Term.typeSpec
                    ":"
                    («term_≤_»
                     («term_^_» `c' "^" (num "2"))
                     "≤"
                     («term_^_» (num "1") "^" (num "2"))))])
                 []
                 (tactic__
                  (cdotTk (patternIgnore (token.«· » "·")))
                  [(linarith "linarith" [] (linarithArgsRest [] [] []))])
                 []
                 (Std.Tactic.tacticRwa__
                  "rwa"
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule [] `sq_le_sq) "," (Tactic.rwRule [] `abs_one)]
                   "]")
                  [(Tactic.location "at" (Tactic.locationHyp [`this] []))])])))))
           []
           (Tactic.tacticSuffices_
            "suffices"
            (Term.sufficesDecl
             []
             (Term.arrow
              («term_≠_» `c "≠" (num "0"))
              "→"
              («term_<_» («term_*_» (num "9") "*" («term_^_» `c "^" (num "4"))) "<" (num "16")))
             (Term.byTactic'
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Std.Tactic.rcases
                  "rcases"
                  [(Tactic.casesTarget [] (Term.app `eq_or_ne [`c (num "0")]))]
                  ["with"
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed
                     [(Std.Tactic.RCases.rcasesPat.paren
                       "("
                       (Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed
                         [(Std.Tactic.RCases.rcasesPat.one `hc)
                          "|"
                          (Std.Tactic.RCases.rcasesPat.one `hc)])
                        [])
                       ")")])
                    [])])
                 []
                 (tactic__
                  (cdotTk (patternIgnore (token.«· » "·")))
                  [(Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `hc)] "]") [])
                   []
                   (Mathlib.Tactic.normNum "norm_num" [] [] [])])
                 []
                 (tactic__
                  (cdotTk (patternIgnore (token.«· » "·")))
                  [(Tactic.refine'
                    "refine'"
                    (Term.proj
                     (Term.app
                      `abs_lt_of_sq_lt_sq'
                      [(Term.hole "_")
                       (Term.byTactic
                        "by"
                        (Tactic.tacticSeq
                         (Tactic.tacticSeq1Indented
                          [(Mathlib.Tactic.normNum "norm_num" [] [] [])])))])
                     "."
                     (fieldIdx "2")))
                   []
                   (Tactic.specialize "specialize" (Term.app `this [`hc]))
                   []
                   (linarith "linarith" [] (linarithArgsRest [] [] []))])])))))
           []
           (Tactic.intro "intro" [`hc])
           []
           (Mathlib.Tactic.replace'
            "replace"
            [`hc []]
            [(Term.typeSpec ":" («term_<_» (num "0") "<" («term_^_» `c "^" (num "4"))))])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.«tactic_<;>_»
              (Tactic.rwSeq
               "rw"
               []
               (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `pow_bit0_pos_iff)] "]")
               [])
              "<;>"
              (Tactic.tacticTrivial "trivial"))])
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`h₁ []]
              []
              ":="
              (Term.app
               `mul_lt_mul_of_pos_right
               [(Term.app
                 `mul_lt_mul''
                 [(Term.app `three_lt_four_mul_im_sq_of_mem_fdo [`hg])
                  (Term.app `three_lt_four_mul_im_sq_of_mem_fdo [`hz])
                  (Term.byTactic
                   "by"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented
                     [(linarith "linarith" [] (linarithArgsRest [] [] []))])))
                  (Term.byTactic
                   "by"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented
                     [(linarith "linarith" [] (linarithArgsRest [] [] []))])))])
                `hc]))))
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`h₂ []]
              [(Term.typeSpec
                ":"
                («term_≤_»
                 («term_/_»
                  («term_^_» («term_*_» `c "*" `z.im) "^" (num "4"))
                  "/"
                  («term_^_»
                   (Term.app `norm_sq [(Term.app `denom [(coeNotation "↑" `g) `z])])
                   "^"
                   (num "2")))
                 "≤"
                 (num "1")))]
              ":="
              (Term.app
               `div_le_one_of_le
               [(Term.app
                 `pow_four_le_pow_two_of_pow_two_le
                 [(Term.app `UpperHalfPlane.c_mul_im_sq_le_norm_sq_denom [`z `g])])
                (Term.app `sq_nonneg [(Term.hole "_")])]))))
           []
           (Tactic.tacticLet_
            "let"
            (Term.letDecl
             (Term.letIdDecl `nsq [] [] ":=" (Term.app `norm_sq [(Term.app `denom [`g `z])]))))
           []
           (calcTactic
            "calc"
            (calcStep
             («term_<_»
              («term_*_» (num "9") "*" («term_^_» `c "^" (num "4")))
              "<"
              («term_*_»
               («term_*_»
                («term_*_» («term_^_» `c "^" (num "4")) "*" («term_^_» `z.im "^" (num "2")))
                "*"
                («term_^_»
                 (Term.proj (Algebra.Group.Defs.«term_•_» `g " • " `z) "." `im)
                 "^"
                 (num "2")))
               "*"
               (num "16")))
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented [(linarith "linarith" [] (linarithArgsRest [] [] []))]))))
            [(calcStep
              («term_=_»
               (Term.hole "_")
               "="
               («term_*_»
                («term_/_»
                 («term_*_» («term_^_» `c "^" (num "4")) "*" («term_^_» `z.im "^" (num "4")))
                 "/"
                 («term_^_» `nsq "^" (num "2")))
                "*"
                (num "16")))
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
                    [(Tactic.rwRule [] `special_linear_group.im_smul_eq_div_norm_sq)
                     ","
                     (Tactic.rwRule [] `div_pow)]
                    "]")
                   [])
                  []
                  (Mathlib.Tactic.RingNF.ring "ring")]))))
             (calcStep
              («term_≤_» (Term.hole "_") "≤" (num "16"))
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
                    [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `mul_pow)]
                    "]")
                   [])
                  []
                  (linarith "linarith" [] (linarithArgsRest [] [] []))]))))])])))
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
         [(Tactic.tacticLet_
           "let"
           (Term.letDecl
            (Term.letIdDecl
             `c'
             []
             [(Term.typeSpec ":" (termℤ "ℤ"))]
             ":="
             (Term.app (NumberTheory.Modular.«term↑ₘ_» "↑ₘ" `g) [(num "1") (num "0")]))))
          []
          (Tactic.tacticLet_
           "let"
           (Term.letDecl
            (Term.letIdDecl
             `c
             []
             [(Term.typeSpec ":" (Data.Real.Basic.termℝ "ℝ"))]
             ":="
             (Term.typeAscription "(" `c' ":" [(Data.Real.Basic.termℝ "ℝ")] ")"))))
          []
          (Tactic.tacticSuffices_
           "suffices"
           (Term.sufficesDecl
            []
            («term_<_» («term_*_» (num "3") "*" («term_^_» `c "^" (num "2"))) "<" (num "4"))
            (Term.byTactic'
             "by"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(Tactic.rwSeq
                 "rw"
                 []
                 (Tactic.rwRuleSeq
                  "["
                  [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Int.cast_pow)
                   ","
                   (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Int.cast_three)
                   ","
                   (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Int.cast_four)
                   ","
                   (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Int.cast_mul)
                   ","
                   (Tactic.rwRule [] `Int.cast_lt)]
                  "]")
                 [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
                []
                (Mathlib.Tactic.replace'
                 "replace"
                 [`this []]
                 [(Term.typeSpec
                   ":"
                   («term_≤_»
                    («term_^_» `c' "^" (num "2"))
                    "≤"
                    («term_^_» (num "1") "^" (num "2"))))])
                []
                (tactic__
                 (cdotTk (patternIgnore (token.«· » "·")))
                 [(linarith "linarith" [] (linarithArgsRest [] [] []))])
                []
                (Std.Tactic.tacticRwa__
                 "rwa"
                 (Tactic.rwRuleSeq
                  "["
                  [(Tactic.rwRule [] `sq_le_sq) "," (Tactic.rwRule [] `abs_one)]
                  "]")
                 [(Tactic.location "at" (Tactic.locationHyp [`this] []))])])))))
          []
          (Tactic.tacticSuffices_
           "suffices"
           (Term.sufficesDecl
            []
            (Term.arrow
             («term_≠_» `c "≠" (num "0"))
             "→"
             («term_<_» («term_*_» (num "9") "*" («term_^_» `c "^" (num "4"))) "<" (num "16")))
            (Term.byTactic'
             "by"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(Std.Tactic.rcases
                 "rcases"
                 [(Tactic.casesTarget [] (Term.app `eq_or_ne [`c (num "0")]))]
                 ["with"
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed
                    [(Std.Tactic.RCases.rcasesPat.paren
                      "("
                      (Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed
                        [(Std.Tactic.RCases.rcasesPat.one `hc)
                         "|"
                         (Std.Tactic.RCases.rcasesPat.one `hc)])
                       [])
                      ")")])
                   [])])
                []
                (tactic__
                 (cdotTk (patternIgnore (token.«· » "·")))
                 [(Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `hc)] "]") [])
                  []
                  (Mathlib.Tactic.normNum "norm_num" [] [] [])])
                []
                (tactic__
                 (cdotTk (patternIgnore (token.«· » "·")))
                 [(Tactic.refine'
                   "refine'"
                   (Term.proj
                    (Term.app
                     `abs_lt_of_sq_lt_sq'
                     [(Term.hole "_")
                      (Term.byTactic
                       "by"
                       (Tactic.tacticSeq
                        (Tactic.tacticSeq1Indented
                         [(Mathlib.Tactic.normNum "norm_num" [] [] [])])))])
                    "."
                    (fieldIdx "2")))
                  []
                  (Tactic.specialize "specialize" (Term.app `this [`hc]))
                  []
                  (linarith "linarith" [] (linarithArgsRest [] [] []))])])))))
          []
          (Tactic.intro "intro" [`hc])
          []
          (Mathlib.Tactic.replace'
           "replace"
           [`hc []]
           [(Term.typeSpec ":" («term_<_» (num "0") "<" («term_^_» `c "^" (num "4"))))])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.«tactic_<;>_»
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `pow_bit0_pos_iff)] "]")
              [])
             "<;>"
             (Tactic.tacticTrivial "trivial"))])
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`h₁ []]
             []
             ":="
             (Term.app
              `mul_lt_mul_of_pos_right
              [(Term.app
                `mul_lt_mul''
                [(Term.app `three_lt_four_mul_im_sq_of_mem_fdo [`hg])
                 (Term.app `three_lt_four_mul_im_sq_of_mem_fdo [`hz])
                 (Term.byTactic
                  "by"
                  (Tactic.tacticSeq
                   (Tactic.tacticSeq1Indented
                    [(linarith "linarith" [] (linarithArgsRest [] [] []))])))
                 (Term.byTactic
                  "by"
                  (Tactic.tacticSeq
                   (Tactic.tacticSeq1Indented
                    [(linarith "linarith" [] (linarithArgsRest [] [] []))])))])
               `hc]))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`h₂ []]
             [(Term.typeSpec
               ":"
               («term_≤_»
                («term_/_»
                 («term_^_» («term_*_» `c "*" `z.im) "^" (num "4"))
                 "/"
                 («term_^_»
                  (Term.app `norm_sq [(Term.app `denom [(coeNotation "↑" `g) `z])])
                  "^"
                  (num "2")))
                "≤"
                (num "1")))]
             ":="
             (Term.app
              `div_le_one_of_le
              [(Term.app
                `pow_four_le_pow_two_of_pow_two_le
                [(Term.app `UpperHalfPlane.c_mul_im_sq_le_norm_sq_denom [`z `g])])
               (Term.app `sq_nonneg [(Term.hole "_")])]))))
          []
          (Tactic.tacticLet_
           "let"
           (Term.letDecl
            (Term.letIdDecl `nsq [] [] ":=" (Term.app `norm_sq [(Term.app `denom [`g `z])]))))
          []
          (calcTactic
           "calc"
           (calcStep
            («term_<_»
             («term_*_» (num "9") "*" («term_^_» `c "^" (num "4")))
             "<"
             («term_*_»
              («term_*_»
               («term_*_» («term_^_» `c "^" (num "4")) "*" («term_^_» `z.im "^" (num "2")))
               "*"
               («term_^_»
                (Term.proj (Algebra.Group.Defs.«term_•_» `g " • " `z) "." `im)
                "^"
                (num "2")))
              "*"
              (num "16")))
            ":="
            (Term.byTactic
             "by"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented [(linarith "linarith" [] (linarithArgsRest [] [] []))]))))
           [(calcStep
             («term_=_»
              (Term.hole "_")
              "="
              («term_*_»
               («term_/_»
                («term_*_» («term_^_» `c "^" (num "4")) "*" («term_^_» `z.im "^" (num "4")))
                "/"
                («term_^_» `nsq "^" (num "2")))
               "*"
               (num "16")))
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
                   [(Tactic.rwRule [] `special_linear_group.im_smul_eq_div_norm_sq)
                    ","
                    (Tactic.rwRule [] `div_pow)]
                   "]")
                  [])
                 []
                 (Mathlib.Tactic.RingNF.ring "ring")]))))
            (calcStep
             («term_≤_» (Term.hole "_") "≤" (num "16"))
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
                   [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `mul_pow)]
                   "]")
                  [])
                 []
                 (linarith "linarith" [] (linarithArgsRest [] [] []))]))))])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (calcTactic
       "calc"
       (calcStep
        («term_<_»
         («term_*_» (num "9") "*" («term_^_» `c "^" (num "4")))
         "<"
         («term_*_»
          («term_*_»
           («term_*_» («term_^_» `c "^" (num "4")) "*" («term_^_» `z.im "^" (num "2")))
           "*"
           («term_^_» (Term.proj (Algebra.Group.Defs.«term_•_» `g " • " `z) "." `im) "^" (num "2")))
          "*"
          (num "16")))
        ":="
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented [(linarith "linarith" [] (linarithArgsRest [] [] []))]))))
       [(calcStep
         («term_=_»
          (Term.hole "_")
          "="
          («term_*_»
           («term_/_»
            («term_*_» («term_^_» `c "^" (num "4")) "*" («term_^_» `z.im "^" (num "4")))
            "/"
            («term_^_» `nsq "^" (num "2")))
           "*"
           (num "16")))
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
               [(Tactic.rwRule [] `special_linear_group.im_smul_eq_div_norm_sq)
                ","
                (Tactic.rwRule [] `div_pow)]
               "]")
              [])
             []
             (Mathlib.Tactic.RingNF.ring "ring")]))))
        (calcStep
         («term_≤_» (Term.hole "_") "≤" (num "16"))
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
               [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `mul_pow)]
               "]")
              [])
             []
             (linarith "linarith" [] (linarithArgsRest [] [] []))]))))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `mul_pow)] "]")
           [])
          []
          (linarith "linarith" [] (linarithArgsRest [] [] []))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (linarith "linarith" [] (linarithArgsRest [] [] []))
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `mul_pow)] "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_pow
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≤_» (Term.hole "_") "≤" (num "16"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "16")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
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
            [(Tactic.rwRule [] `special_linear_group.im_smul_eq_div_norm_sq)
             ","
             (Tactic.rwRule [] `div_pow)]
            "]")
           [])
          []
          (Mathlib.Tactic.RingNF.ring "ring")])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.RingNF.ring "ring")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `special_linear_group.im_smul_eq_div_norm_sq)
         ","
         (Tactic.rwRule [] `div_pow)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `div_pow
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `special_linear_group.im_smul_eq_div_norm_sq
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Term.hole "_")
       "="
       («term_*_»
        («term_/_»
         («term_*_» («term_^_» `c "^" (num "4")) "*" («term_^_» `z.im "^" (num "4")))
         "/"
         («term_^_» `nsq "^" (num "2")))
        "*"
        (num "16")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_»
       («term_/_»
        («term_*_» («term_^_» `c "^" (num "4")) "*" («term_^_» `z.im "^" (num "4")))
        "/"
        («term_^_» `nsq "^" (num "2")))
       "*"
       (num "16"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "16")
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      («term_/_»
       («term_*_» («term_^_» `c "^" (num "4")) "*" («term_^_» `z.im "^" (num "4")))
       "/"
       («term_^_» `nsq "^" (num "2")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_» `nsq "^" (num "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      `nsq
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      («term_*_» («term_^_» `c "^" (num "4")) "*" («term_^_» `z.im "^" (num "4")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_» `z.im "^" (num "4"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "4")
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      `z.im
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      («term_^_» `c "^" (num "4"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "4")
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      `c
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 80, (some 80, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 70, (some 71, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 70, (some 71, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented [(linarith "linarith" [] (linarithArgsRest [] [] []))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (linarith "linarith" [] (linarithArgsRest [] [] []))
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<_»
       («term_*_» (num "9") "*" («term_^_» `c "^" (num "4")))
       "<"
       («term_*_»
        («term_*_»
         («term_*_» («term_^_» `c "^" (num "4")) "*" («term_^_» `z.im "^" (num "2")))
         "*"
         («term_^_» (Term.proj (Algebra.Group.Defs.«term_•_» `g " • " `z) "." `im) "^" (num "2")))
        "*"
        (num "16")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_»
       («term_*_»
        («term_*_» («term_^_» `c "^" (num "4")) "*" («term_^_» `z.im "^" (num "2")))
        "*"
        («term_^_» (Term.proj (Algebra.Group.Defs.«term_•_» `g " • " `z) "." `im) "^" (num "2")))
       "*"
       (num "16"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "16")
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      («term_*_»
       («term_*_» («term_^_» `c "^" (num "4")) "*" («term_^_» `z.im "^" (num "2")))
       "*"
       («term_^_» (Term.proj (Algebra.Group.Defs.«term_•_» `g " • " `z) "." `im) "^" (num "2")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_» (Term.proj (Algebra.Group.Defs.«term_•_» `g " • " `z) "." `im) "^" (num "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Term.proj (Algebra.Group.Defs.«term_•_» `g " • " `z) "." `im)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Algebra.Group.Defs.«term_•_» `g " • " `z)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `z
[PrettyPrinter.parenthesize] ...precedences are 73 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 73, term))
      `g
[PrettyPrinter.parenthesize] ...precedences are 74 >? 1024, (none, [anonymous]) <=? (some 73, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 73, (some 73, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Algebra.Group.Defs.«term_•_» `g " • " `z)
     ")")
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      («term_*_» («term_^_» `c "^" (num "4")) "*" («term_^_» `z.im "^" (num "2")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_» `z.im "^" (num "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      `z.im
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      («term_^_» `c "^" (num "4"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "4")
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      `c
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 80, (some 80, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 70, (some 71, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 70, (some 71, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      («term_*_» (num "9") "*" («term_^_» `c "^" (num "4")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_» `c "^" (num "4"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "4")
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      `c
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (num "9")
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 70, (some 71, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticLet_
       "let"
       (Term.letDecl
        (Term.letIdDecl `nsq [] [] ":=" (Term.app `norm_sq [(Term.app `denom [`g `z])]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `norm_sq [(Term.app `denom [`g `z])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `denom [`g `z])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `z
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `denom
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `denom [`g `z]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `norm_sq
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`h₂ []]
         [(Term.typeSpec
           ":"
           («term_≤_»
            («term_/_»
             («term_^_» («term_*_» `c "*" `z.im) "^" (num "4"))
             "/"
             («term_^_»
              (Term.app `norm_sq [(Term.app `denom [(coeNotation "↑" `g) `z])])
              "^"
              (num "2")))
            "≤"
            (num "1")))]
         ":="
         (Term.app
          `div_le_one_of_le
          [(Term.app
            `pow_four_le_pow_two_of_pow_two_le
            [(Term.app `UpperHalfPlane.c_mul_im_sq_le_norm_sq_denom [`z `g])])
           (Term.app `sq_nonneg [(Term.hole "_")])]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `div_le_one_of_le
       [(Term.app
         `pow_four_le_pow_two_of_pow_two_le
         [(Term.app `UpperHalfPlane.c_mul_im_sq_le_norm_sq_denom [`z `g])])
        (Term.app `sq_nonneg [(Term.hole "_")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `sq_nonneg [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `sq_nonneg
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `sq_nonneg [(Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       `pow_four_le_pow_two_of_pow_two_le
       [(Term.app `UpperHalfPlane.c_mul_im_sq_le_norm_sq_denom [`z `g])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `UpperHalfPlane.c_mul_im_sq_le_norm_sq_denom [`z `g])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `z
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `UpperHalfPlane.c_mul_im_sq_le_norm_sq_denom
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `UpperHalfPlane.c_mul_im_sq_le_norm_sq_denom [`z `g])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `pow_four_le_pow_two_of_pow_two_le
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `pow_four_le_pow_two_of_pow_two_le
      [(Term.paren "(" (Term.app `UpperHalfPlane.c_mul_im_sq_le_norm_sq_denom [`z `g]) ")")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `div_le_one_of_le
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≤_»
       («term_/_»
        («term_^_» («term_*_» `c "*" `z.im) "^" (num "4"))
        "/"
        («term_^_» (Term.app `norm_sq [(Term.app `denom [(coeNotation "↑" `g) `z])]) "^" (num "2")))
       "≤"
       (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      («term_/_»
       («term_^_» («term_*_» `c "*" `z.im) "^" (num "4"))
       "/"
       («term_^_» (Term.app `norm_sq [(Term.app `denom [(coeNotation "↑" `g) `z])]) "^" (num "2")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_» (Term.app `norm_sq [(Term.app `denom [(coeNotation "↑" `g) `z])]) "^" (num "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Term.app `norm_sq [(Term.app `denom [(coeNotation "↑" `g) `z])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `denom [(coeNotation "↑" `g) `z])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `z
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'coeNotation', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'coeNotation', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (coeNotation "↑" `g)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 1024,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (coeNotation "↑" `g) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `denom
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `denom [(Term.paren "(" (coeNotation "↑" `g) ")") `z])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `norm_sq
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1022, (some 1023, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      («term_^_» («term_*_» `c "*" `z.im) "^" (num "4"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "4")
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      («term_*_» `c "*" `z.im)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `z.im
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `c
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 70, (some 71, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_*_» `c "*" `z.im) ")")
[PrettyPrinter.parenthesize] ...precedences are 70 >? 80, (some 80, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 70, (some 71, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`h₁ []]
         []
         ":="
         (Term.app
          `mul_lt_mul_of_pos_right
          [(Term.app
            `mul_lt_mul''
            [(Term.app `three_lt_four_mul_im_sq_of_mem_fdo [`hg])
             (Term.app `three_lt_four_mul_im_sq_of_mem_fdo [`hz])
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented [(linarith "linarith" [] (linarithArgsRest [] [] []))])))
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(linarith "linarith" [] (linarithArgsRest [] [] []))])))])
           `hc]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `mul_lt_mul_of_pos_right
       [(Term.app
         `mul_lt_mul''
         [(Term.app `three_lt_four_mul_im_sq_of_mem_fdo [`hg])
          (Term.app `three_lt_four_mul_im_sq_of_mem_fdo [`hz])
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented [(linarith "linarith" [] (linarithArgsRest [] [] []))])))
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented [(linarith "linarith" [] (linarithArgsRest [] [] []))])))])
        `hc])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hc
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       `mul_lt_mul''
       [(Term.app `three_lt_four_mul_im_sq_of_mem_fdo [`hg])
        (Term.app `three_lt_four_mul_im_sq_of_mem_fdo [`hz])
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented [(linarith "linarith" [] (linarithArgsRest [] [] []))])))
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented [(linarith "linarith" [] (linarithArgsRest [] [] []))])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented [(linarith "linarith" [] (linarithArgsRest [] [] []))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (linarith "linarith" [] (linarithArgsRest [] [] []))
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0,
     tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented [(linarith "linarith" [] (linarithArgsRest [] [] []))])))
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented [(linarith "linarith" [] (linarithArgsRest [] [] []))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (linarith "linarith" [] (linarithArgsRest [] [] []))
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, tactic) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented [(linarith "linarith" [] (linarithArgsRest [] [] []))])))
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `three_lt_four_mul_im_sq_of_mem_fdo [`hz])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hz
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `three_lt_four_mul_im_sq_of_mem_fdo
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `three_lt_four_mul_im_sq_of_mem_fdo [`hz])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `three_lt_four_mul_im_sq_of_mem_fdo [`hg])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hg
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `three_lt_four_mul_im_sq_of_mem_fdo
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `three_lt_four_mul_im_sq_of_mem_fdo [`hg])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `mul_lt_mul''
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `mul_lt_mul''
      [(Term.paren "(" (Term.app `three_lt_four_mul_im_sq_of_mem_fdo [`hg]) ")")
       (Term.paren "(" (Term.app `three_lt_four_mul_im_sq_of_mem_fdo [`hz]) ")")
       (Term.paren
        "("
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented [(linarith "linarith" [] (linarithArgsRest [] [] []))])))
        ")")
       (Term.paren
        "("
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented [(linarith "linarith" [] (linarithArgsRest [] [] []))])))
        ")")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `mul_lt_mul_of_pos_right
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.«tactic_<;>_»
         (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `pow_bit0_pos_iff)] "]") [])
         "<;>"
         (Tactic.tacticTrivial "trivial"))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.«tactic_<;>_»
       (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `pow_bit0_pos_iff)] "]") [])
       "<;>"
       (Tactic.tacticTrivial "trivial"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticTrivial "trivial")
[PrettyPrinter.parenthesize] ...precedences are 2 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
      (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `pow_bit0_pos_iff)] "]") [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `pow_bit0_pos_iff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.replace'
       "replace"
       [`hc []]
       [(Term.typeSpec ":" («term_<_» (num "0") "<" («term_^_» `c "^" (num "4"))))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<_» (num "0") "<" («term_^_» `c "^" (num "4")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_» `c "^" (num "4"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "4")
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      `c
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.intro "intro" [`hc])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hc
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticSuffices_
       "suffices"
       (Term.sufficesDecl
        []
        (Term.arrow
         («term_≠_» `c "≠" (num "0"))
         "→"
         («term_<_» («term_*_» (num "9") "*" («term_^_» `c "^" (num "4"))) "<" (num "16")))
        (Term.byTactic'
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Std.Tactic.rcases
             "rcases"
             [(Tactic.casesTarget [] (Term.app `eq_or_ne [`c (num "0")]))]
             ["with"
              (Std.Tactic.RCases.rcasesPatLo
               (Std.Tactic.RCases.rcasesPatMed
                [(Std.Tactic.RCases.rcasesPat.paren
                  "("
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed
                    [(Std.Tactic.RCases.rcasesPat.one `hc)
                     "|"
                     (Std.Tactic.RCases.rcasesPat.one `hc)])
                   [])
                  ")")])
               [])])
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `hc)] "]") [])
              []
              (Mathlib.Tactic.normNum "norm_num" [] [] [])])
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(Tactic.refine'
               "refine'"
               (Term.proj
                (Term.app
                 `abs_lt_of_sq_lt_sq'
                 [(Term.hole "_")
                  (Term.byTactic
                   "by"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented [(Mathlib.Tactic.normNum "norm_num" [] [] [])])))])
                "."
                (fieldIdx "2")))
              []
              (Tactic.specialize "specialize" (Term.app `this [`hc]))
              []
              (linarith "linarith" [] (linarithArgsRest [] [] []))])])))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic'', expected 'Lean.Parser.Term.fromTerm'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.refine'
         "refine'"
         (Term.proj
          (Term.app
           `abs_lt_of_sq_lt_sq'
           [(Term.hole "_")
            (Term.byTactic
             "by"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented [(Mathlib.Tactic.normNum "norm_num" [] [] [])])))])
          "."
          (fieldIdx "2")))
        []
        (Tactic.specialize "specialize" (Term.app `this [`hc]))
        []
        (linarith "linarith" [] (linarithArgsRest [] [] []))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (linarith "linarith" [] (linarithArgsRest [] [] []))
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.specialize "specialize" (Term.app `this [`hc]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `this [`hc])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hc
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `this
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine'
       "refine'"
       (Term.proj
        (Term.app
         `abs_lt_of_sq_lt_sq'
         [(Term.hole "_")
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented [(Mathlib.Tactic.normNum "norm_num" [] [] [])])))])
        "."
        (fieldIdx "2")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj
       (Term.app
        `abs_lt_of_sq_lt_sq'
        [(Term.hole "_")
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented [(Mathlib.Tactic.normNum "norm_num" [] [] [])])))])
       "."
       (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       `abs_lt_of_sq_lt_sq'
       [(Term.hole "_")
        (Term.byTactic
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `abs_lt_of_sq_lt_sq'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `abs_lt_of_sq_lt_sq'
      [(Term.hole "_")
       (Term.paren
        "("
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented [(Mathlib.Tactic.normNum "norm_num" [] [] [])])))
        ")")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `hc)] "]") [])
        []
        (Mathlib.Tactic.normNum "norm_num" [] [] [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.normNum "norm_num" [] [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `hc)] "]") [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hc
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.rcases
       "rcases"
       [(Tactic.casesTarget [] (Term.app `eq_or_ne [`c (num "0")]))]
       ["with"
        (Std.Tactic.RCases.rcasesPatLo
         (Std.Tactic.RCases.rcasesPatMed
          [(Std.Tactic.RCases.rcasesPat.paren
            "("
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed
              [(Std.Tactic.RCases.rcasesPat.one `hc) "|" (Std.Tactic.RCases.rcasesPat.one `hc)])
             [])
            ")")])
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `eq_or_ne [`c (num "0")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `c
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `eq_or_ne
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.arrow
       («term_≠_» `c "≠" (num "0"))
       "→"
       («term_<_» («term_*_» (num "9") "*" («term_^_» `c "^" (num "4"))) "<" (num "16")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<_» («term_*_» (num "9") "*" («term_^_» `c "^" (num "4"))) "<" (num "16"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "16")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      («term_*_» (num "9") "*" («term_^_» `c "^" (num "4")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_» `c "^" (num "4"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "4")
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      `c
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (num "9")
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 70, (some 71, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 25 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
      («term_≠_» `c "≠" (num "0"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `c
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (some 25, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 25, (some 25,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticSuffices_
       "suffices"
       (Term.sufficesDecl
        []
        («term_<_» («term_*_» (num "3") "*" («term_^_» `c "^" (num "2"))) "<" (num "4"))
        (Term.byTactic'
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Int.cast_pow)
               ","
               (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Int.cast_three)
               ","
               (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Int.cast_four)
               ","
               (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Int.cast_mul)
               ","
               (Tactic.rwRule [] `Int.cast_lt)]
              "]")
             [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
            []
            (Mathlib.Tactic.replace'
             "replace"
             [`this []]
             [(Term.typeSpec
               ":"
               («term_≤_» («term_^_» `c' "^" (num "2")) "≤" («term_^_» (num "1") "^" (num "2"))))])
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(linarith "linarith" [] (linarithArgsRest [] [] []))])
            []
            (Std.Tactic.tacticRwa__
             "rwa"
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] `sq_le_sq) "," (Tactic.rwRule [] `abs_one)]
              "]")
             [(Tactic.location "at" (Tactic.locationHyp [`this] []))])])))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic'', expected 'Lean.Parser.Term.fromTerm'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.tacticRwa__
       "rwa"
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `sq_le_sq) "," (Tactic.rwRule [] `abs_one)] "]")
       [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `this
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `abs_one
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `sq_le_sq
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(linarith "linarith" [] (linarithArgsRest [] [] []))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (linarith "linarith" [] (linarithArgsRest [] [] []))
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.replace'
       "replace"
       [`this []]
       [(Term.typeSpec
         ":"
         («term_≤_» («term_^_» `c' "^" (num "2")) "≤" («term_^_» (num "1") "^" (num "2"))))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≤_» («term_^_» `c' "^" (num "2")) "≤" («term_^_» (num "1") "^" (num "2")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_» (num "1") "^" (num "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      («term_^_» `c' "^" (num "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      `c'
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 80, (some 80, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Int.cast_pow)
         ","
         (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Int.cast_three)
         ","
         (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Int.cast_four)
         ","
         (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Int.cast_mul)
         ","
         (Tactic.rwRule [] `Int.cast_lt)]
        "]")
       [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `this
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Int.cast_lt
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Int.cast_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Int.cast_four
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Int.cast_three
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Int.cast_pow
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_<_» («term_*_» (num "3") "*" («term_^_» `c "^" (num "2"))) "<" (num "4"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "4")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      («term_*_» (num "3") "*" («term_^_» `c "^" (num "2")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_» `c "^" (num "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      `c
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (num "3")
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 70, (some 71, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticLet_
       "let"
       (Term.letDecl
        (Term.letIdDecl
         `c
         []
         [(Term.typeSpec ":" (Data.Real.Basic.termℝ "ℝ"))]
         ":="
         (Term.typeAscription "(" `c' ":" [(Data.Real.Basic.termℝ "ℝ")] ")"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription "(" `c' ":" [(Data.Real.Basic.termℝ "ℝ")] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Real.Basic.termℝ "ℝ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `c'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Real.Basic.termℝ "ℝ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticLet_
       "let"
       (Term.letDecl
        (Term.letIdDecl
         `c'
         []
         [(Term.typeSpec ":" (termℤ "ℤ"))]
         ":="
         (Term.app (NumberTheory.Modular.«term↑ₘ_» "↑ₘ" `g) [(num "1") (num "0")]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (NumberTheory.Modular.«term↑ₘ_» "↑ₘ" `g) [(num "1") (num "0")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (NumberTheory.Modular.«term↑ₘ_» "↑ₘ" `g)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.Modular.«term↑ₘ_»', expected 'NumberTheory.Modular.term↑ₘ_._@.NumberTheory.Modular._hyg.827'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letIdDecl', expected 'Lean.Parser.Term.letPatDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letIdDecl', expected 'Lean.Parser.Term.letEqnsDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/-- An auxiliary result en route to `modular_group.c_eq_zero`. -/
  theorem
    abs_c_le_one
    ( hz : z ∈ 𝒟ᵒ ) ( hg : g • z ∈ 𝒟ᵒ ) : | ↑ₘ g 1 0 | ≤ 1
    :=
      by
        let c' : ℤ := ↑ₘ g 1 0
          let c : ℝ := ( c' : ℝ )
          suffices
            3 * c ^ 2 < 4
              by
                rw
                    [
                      ← Int.cast_pow
                        ,
                        ← Int.cast_three
                        ,
                        ← Int.cast_four
                        ,
                        ← Int.cast_mul
                        ,
                        Int.cast_lt
                      ]
                    at this
                  replace this : c' ^ 2 ≤ 1 ^ 2
                  · linarith
                  rwa [ sq_le_sq , abs_one ] at this
          suffices
            c ≠ 0 → 9 * c ^ 4 < 16
              by
                rcases eq_or_ne c 0 with ( hc | hc )
                  · rw [ hc ] norm_num
                  · refine' abs_lt_of_sq_lt_sq' _ by norm_num . 2 specialize this hc linarith
          intro hc
          replace hc : 0 < c ^ 4
          · rw [ pow_bit0_pos_iff ] <;> trivial
          have
            h₁
              :=
              mul_lt_mul_of_pos_right
                mul_lt_mul''
                    three_lt_four_mul_im_sq_of_mem_fdo hg
                      three_lt_four_mul_im_sq_of_mem_fdo hz
                      by linarith
                      by linarith
                  hc
          have
            h₂
              : c * z.im ^ 4 / norm_sq denom ↑ g z ^ 2 ≤ 1
              :=
              div_le_one_of_le
                pow_four_le_pow_two_of_pow_two_le UpperHalfPlane.c_mul_im_sq_le_norm_sq_denom z g
                  sq_nonneg _
          let nsq := norm_sq denom g z
          calc
            9 * c ^ 4 < c ^ 4 * z.im ^ 2 * g • z . im ^ 2 * 16 := by linarith
            _ = c ^ 4 * z.im ^ 4 / nsq ^ 2 * 16
                :=
                by rw [ special_linear_group.im_smul_eq_div_norm_sq , div_pow ] ring
              _ ≤ 16 := by rw [ ← mul_pow ] linarith
#align modular_group.abs_c_le_one ModularGroup.abs_c_le_one

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "An auxiliary result en route to `modular_group.eq_smul_self_of_mem_fdo_mem_fdo`. -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `c_eq_zero [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`hz]
         [":" («term_∈_» `z "∈" (Modular.NumberTheory.Modular.modular_group.fdo "𝒟ᵒ"))]
         []
         ")")
        (Term.explicitBinder
         "("
         [`hg]
         [":"
          («term_∈_»
           (Algebra.Group.Defs.«term_•_» `g " • " `z)
           "∈"
           (Modular.NumberTheory.Modular.modular_group.fdo "𝒟ᵒ"))]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app (NumberTheory.Modular.«term↑ₘ_» "↑ₘ" `g) [(num "1") (num "0")])
         "="
         (num "0"))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`hp []]
              [(Term.typeSpec
                ":"
                (Term.forall
                 "∀"
                 [(Term.implicitBinder
                   "{"
                   [`g']
                   [":" (NumberTheory.Modular.«termSL(_,_)» "SL(" (num "2") ", " (termℤ "ℤ") ")")]
                   "}")
                  (Term.explicitBinder
                   "("
                   [`hg']
                   [":"
                    («term_∈_»
                     (Algebra.Group.Defs.«term_•_» `g' " • " `z)
                     "∈"
                     (Modular.NumberTheory.Modular.modular_group.fdo "𝒟ᵒ"))]
                   []
                   ")")]
                 []
                 ","
                 («term_≠_»
                  (Term.app (NumberTheory.Modular.«term↑ₘ_» "↑ₘ" `g') [(num "1") (num "0")])
                  "≠"
                  (num "1"))))]
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Tactic.intros "intros" [])
                  []
                  (Std.Tactic.byContra "by_contra" [(Lean.binderIdent `hc)])
                  []
                  (Tactic.tacticLet_
                   "let"
                   (Term.letDecl
                    (Term.letIdDecl
                     `a
                     []
                     []
                     ":="
                     (Term.app (NumberTheory.Modular.«term↑ₘ_» "↑ₘ" `g') [(num "0") (num "0")]))))
                  []
                  (Tactic.tacticLet_
                   "let"
                   (Term.letDecl
                    (Term.letIdDecl
                     `d
                     []
                     []
                     ":="
                     (Term.app (NumberTheory.Modular.«term↑ₘ_» "↑ₘ" `g') [(num "1") (num "1")]))))
                  []
                  (Tactic.tacticHave_
                   "have"
                   (Term.haveDecl
                    (Term.haveIdDecl
                     [`had []]
                     [(Term.typeSpec
                       ":"
                       («term_=_»
                        («term_*_» («term_^_» `T "^" («term-_» "-" `a)) "*" `g')
                        "="
                        («term_*_» `S "*" («term_^_» `T "^" `d))))]
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
                           [(Tactic.rwRule [] (Term.app `g_eq_of_c_eq_one [`hc]))]
                           "]")
                          [])
                         []
                         (Tactic.group "group" [])]))))))
                  []
                  (Tactic.tacticLet_
                   "let"
                   (Term.letDecl
                    (Term.letIdDecl
                     `w
                     []
                     []
                     ":="
                     (Algebra.Group.Defs.«term_•_»
                      («term_^_» `T "^" («term-_» "-" `a))
                      " • "
                      (Algebra.Group.Defs.«term_•_» `g' " • " `z)))))
                  []
                  (Tactic.tacticHave_
                   "have"
                   (Term.haveDecl
                    (Term.haveIdDecl
                     [`h₁ []]
                     [(Term.typeSpec
                       ":"
                       («term_=_»
                        `w
                        "="
                        (Algebra.Group.Defs.«term_•_»
                         `S
                         " • "
                         (Algebra.Group.Defs.«term_•_» («term_^_» `T "^" `d) " • " `z))))]
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
                           [(Tactic.simpLemma [] [] `w)
                            ","
                            (Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `mul_smul)
                            ","
                            (Tactic.simpLemma [] [] `had)]
                           "]"]
                          [])]))))))
                  []
                  (Mathlib.Tactic.tacticReplace_
                   "replace"
                   (Term.haveDecl
                    (Term.haveIdDecl
                     [`h₁ []]
                     [(Term.typeSpec ":" («term_<_» (Term.app `norm_sq [`w]) "<" (num "1")))]
                     ":="
                     (Term.subst
                      `h₁.symm
                      "▸"
                      [(Term.app
                        `norm_sq_S_smul_lt_one
                        [(Term.app `one_lt_norm_sq_T_zpow_smul [`hz `d])])]))))
                  []
                  (Tactic.tacticHave_
                   "have"
                   (Term.haveDecl
                    (Term.haveIdDecl
                     [`h₂ []]
                     [(Term.typeSpec ":" («term_<_» (num "1") "<" (Term.app `norm_sq [`w])))]
                     ":="
                     (Term.app `one_lt_norm_sq_T_zpow_smul [`hg' («term-_» "-" `a)]))))
                  []
                  (linarith "linarith" [] (linarithArgsRest [] [] []))]))))))
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`hn []]
              [(Term.typeSpec
                ":"
                («term_≠_»
                 (Term.app (NumberTheory.Modular.«term↑ₘ_» "↑ₘ" `g) [(num "1") (num "0")])
                 "≠"
                 («term-_» "-" (num "1"))))]
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Tactic.intro "intro" [`hc])
                  []
                  (Mathlib.Tactic.replace'
                   "replace"
                   [`hc []]
                   [(Term.typeSpec
                     ":"
                     («term_=_»
                      (Term.app
                       (NumberTheory.Modular.«term↑ₘ_» "↑ₘ" («term-_» "-" `g))
                       [(num "1") (num "0")])
                      "="
                      (num "1")))])
                  []
                  (tactic__
                   (cdotTk (patternIgnore (token.«· » "·")))
                   [(Tactic.simp
                     "simp"
                     []
                     []
                     []
                     ["[" [(Tactic.simpLemma [] [] (Term.app `eq_neg_of_eq_neg [`hc]))] "]"]
                     [])])
                  []
                  (Mathlib.Tactic.tacticReplace_
                   "replace"
                   (Term.haveDecl
                    (Term.haveIdDecl
                     [`hg []]
                     [(Term.typeSpec
                       ":"
                       («term_∈_»
                        (Algebra.Group.Defs.«term_•_» («term-_» "-" `g) " • " `z)
                        "∈"
                        (Modular.NumberTheory.Modular.modular_group.fdo "𝒟ᵒ")))]
                     ":="
                     (Term.subst (Term.proj (Term.app `SL_neg_smul [`g `z]) "." `symm) "▸" [`hg]))))
                  []
                  (Tactic.exact "exact" (Term.app `hp [`hg `hc]))]))))))
           []
           (Tactic.specialize "specialize" (Term.app `hp [`hg]))
           []
           (Tactic.«tactic_<;>_»
            (Std.Tactic.rcases
             "rcases"
             [(Tactic.casesTarget
               []
               («term_<|_» `int.abs_le_one_iff.mp "<|" (Term.app `abs_c_le_one [`hz `hg])))]
             ["with"
              (Std.Tactic.RCases.rcasesPatLo
               (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.tuple "⟨" [] "⟩")])
               [])])
            "<;>"
            (Mathlib.Tactic.Tauto.tauto "tauto" []))])))
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
         [(Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`hp []]
             [(Term.typeSpec
               ":"
               (Term.forall
                "∀"
                [(Term.implicitBinder
                  "{"
                  [`g']
                  [":" (NumberTheory.Modular.«termSL(_,_)» "SL(" (num "2") ", " (termℤ "ℤ") ")")]
                  "}")
                 (Term.explicitBinder
                  "("
                  [`hg']
                  [":"
                   («term_∈_»
                    (Algebra.Group.Defs.«term_•_» `g' " • " `z)
                    "∈"
                    (Modular.NumberTheory.Modular.modular_group.fdo "𝒟ᵒ"))]
                  []
                  ")")]
                []
                ","
                («term_≠_»
                 (Term.app (NumberTheory.Modular.«term↑ₘ_» "↑ₘ" `g') [(num "1") (num "0")])
                 "≠"
                 (num "1"))))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.intros "intros" [])
                 []
                 (Std.Tactic.byContra "by_contra" [(Lean.binderIdent `hc)])
                 []
                 (Tactic.tacticLet_
                  "let"
                  (Term.letDecl
                   (Term.letIdDecl
                    `a
                    []
                    []
                    ":="
                    (Term.app (NumberTheory.Modular.«term↑ₘ_» "↑ₘ" `g') [(num "0") (num "0")]))))
                 []
                 (Tactic.tacticLet_
                  "let"
                  (Term.letDecl
                   (Term.letIdDecl
                    `d
                    []
                    []
                    ":="
                    (Term.app (NumberTheory.Modular.«term↑ₘ_» "↑ₘ" `g') [(num "1") (num "1")]))))
                 []
                 (Tactic.tacticHave_
                  "have"
                  (Term.haveDecl
                   (Term.haveIdDecl
                    [`had []]
                    [(Term.typeSpec
                      ":"
                      («term_=_»
                       («term_*_» («term_^_» `T "^" («term-_» "-" `a)) "*" `g')
                       "="
                       («term_*_» `S "*" («term_^_» `T "^" `d))))]
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
                          [(Tactic.rwRule [] (Term.app `g_eq_of_c_eq_one [`hc]))]
                          "]")
                         [])
                        []
                        (Tactic.group "group" [])]))))))
                 []
                 (Tactic.tacticLet_
                  "let"
                  (Term.letDecl
                   (Term.letIdDecl
                    `w
                    []
                    []
                    ":="
                    (Algebra.Group.Defs.«term_•_»
                     («term_^_» `T "^" («term-_» "-" `a))
                     " • "
                     (Algebra.Group.Defs.«term_•_» `g' " • " `z)))))
                 []
                 (Tactic.tacticHave_
                  "have"
                  (Term.haveDecl
                   (Term.haveIdDecl
                    [`h₁ []]
                    [(Term.typeSpec
                      ":"
                      («term_=_»
                       `w
                       "="
                       (Algebra.Group.Defs.«term_•_»
                        `S
                        " • "
                        (Algebra.Group.Defs.«term_•_» («term_^_» `T "^" `d) " • " `z))))]
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
                          [(Tactic.simpLemma [] [] `w)
                           ","
                           (Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `mul_smul)
                           ","
                           (Tactic.simpLemma [] [] `had)]
                          "]"]
                         [])]))))))
                 []
                 (Mathlib.Tactic.tacticReplace_
                  "replace"
                  (Term.haveDecl
                   (Term.haveIdDecl
                    [`h₁ []]
                    [(Term.typeSpec ":" («term_<_» (Term.app `norm_sq [`w]) "<" (num "1")))]
                    ":="
                    (Term.subst
                     `h₁.symm
                     "▸"
                     [(Term.app
                       `norm_sq_S_smul_lt_one
                       [(Term.app `one_lt_norm_sq_T_zpow_smul [`hz `d])])]))))
                 []
                 (Tactic.tacticHave_
                  "have"
                  (Term.haveDecl
                   (Term.haveIdDecl
                    [`h₂ []]
                    [(Term.typeSpec ":" («term_<_» (num "1") "<" (Term.app `norm_sq [`w])))]
                    ":="
                    (Term.app `one_lt_norm_sq_T_zpow_smul [`hg' («term-_» "-" `a)]))))
                 []
                 (linarith "linarith" [] (linarithArgsRest [] [] []))]))))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`hn []]
             [(Term.typeSpec
               ":"
               («term_≠_»
                (Term.app (NumberTheory.Modular.«term↑ₘ_» "↑ₘ" `g) [(num "1") (num "0")])
                "≠"
                («term-_» "-" (num "1"))))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.intro "intro" [`hc])
                 []
                 (Mathlib.Tactic.replace'
                  "replace"
                  [`hc []]
                  [(Term.typeSpec
                    ":"
                    («term_=_»
                     (Term.app
                      (NumberTheory.Modular.«term↑ₘ_» "↑ₘ" («term-_» "-" `g))
                      [(num "1") (num "0")])
                     "="
                     (num "1")))])
                 []
                 (tactic__
                  (cdotTk (patternIgnore (token.«· » "·")))
                  [(Tactic.simp
                    "simp"
                    []
                    []
                    []
                    ["[" [(Tactic.simpLemma [] [] (Term.app `eq_neg_of_eq_neg [`hc]))] "]"]
                    [])])
                 []
                 (Mathlib.Tactic.tacticReplace_
                  "replace"
                  (Term.haveDecl
                   (Term.haveIdDecl
                    [`hg []]
                    [(Term.typeSpec
                      ":"
                      («term_∈_»
                       (Algebra.Group.Defs.«term_•_» («term-_» "-" `g) " • " `z)
                       "∈"
                       (Modular.NumberTheory.Modular.modular_group.fdo "𝒟ᵒ")))]
                    ":="
                    (Term.subst (Term.proj (Term.app `SL_neg_smul [`g `z]) "." `symm) "▸" [`hg]))))
                 []
                 (Tactic.exact "exact" (Term.app `hp [`hg `hc]))]))))))
          []
          (Tactic.specialize "specialize" (Term.app `hp [`hg]))
          []
          (Tactic.«tactic_<;>_»
           (Std.Tactic.rcases
            "rcases"
            [(Tactic.casesTarget
              []
              («term_<|_» `int.abs_le_one_iff.mp "<|" (Term.app `abs_c_le_one [`hz `hg])))]
            ["with"
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.tuple "⟨" [] "⟩")])
              [])])
           "<;>"
           (Mathlib.Tactic.Tauto.tauto "tauto" []))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.«tactic_<;>_»
       (Std.Tactic.rcases
        "rcases"
        [(Tactic.casesTarget
          []
          («term_<|_» `int.abs_le_one_iff.mp "<|" (Term.app `abs_c_le_one [`hz `hg])))]
        ["with"
         (Std.Tactic.RCases.rcasesPatLo
          (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.tuple "⟨" [] "⟩")])
          [])])
       "<;>"
       (Mathlib.Tactic.Tauto.tauto "tauto" []))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.Tauto.tauto "tauto" [])
[PrettyPrinter.parenthesize] ...precedences are 2 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
      (Std.Tactic.rcases
       "rcases"
       [(Tactic.casesTarget
         []
         («term_<|_» `int.abs_le_one_iff.mp "<|" (Term.app `abs_c_le_one [`hz `hg])))]
       ["with"
        (Std.Tactic.RCases.rcasesPatLo
         (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.tuple "⟨" [] "⟩")])
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_» `int.abs_le_one_iff.mp "<|" (Term.app `abs_c_le_one [`hz `hg]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `abs_c_le_one [`hz `hg])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hg
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hz
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `abs_c_le_one
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      `int.abs_le_one_iff.mp
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 10, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.specialize "specialize" (Term.app `hp [`hg]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `hp [`hg])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hg
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `hp
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`hn []]
         [(Term.typeSpec
           ":"
           («term_≠_»
            (Term.app (NumberTheory.Modular.«term↑ₘ_» "↑ₘ" `g) [(num "1") (num "0")])
            "≠"
            («term-_» "-" (num "1"))))]
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.intro "intro" [`hc])
             []
             (Mathlib.Tactic.replace'
              "replace"
              [`hc []]
              [(Term.typeSpec
                ":"
                («term_=_»
                 (Term.app
                  (NumberTheory.Modular.«term↑ₘ_» "↑ₘ" («term-_» "-" `g))
                  [(num "1") (num "0")])
                 "="
                 (num "1")))])
             []
             (tactic__
              (cdotTk (patternIgnore (token.«· » "·")))
              [(Tactic.simp
                "simp"
                []
                []
                []
                ["[" [(Tactic.simpLemma [] [] (Term.app `eq_neg_of_eq_neg [`hc]))] "]"]
                [])])
             []
             (Mathlib.Tactic.tacticReplace_
              "replace"
              (Term.haveDecl
               (Term.haveIdDecl
                [`hg []]
                [(Term.typeSpec
                  ":"
                  («term_∈_»
                   (Algebra.Group.Defs.«term_•_» («term-_» "-" `g) " • " `z)
                   "∈"
                   (Modular.NumberTheory.Modular.modular_group.fdo "𝒟ᵒ")))]
                ":="
                (Term.subst (Term.proj (Term.app `SL_neg_smul [`g `z]) "." `symm) "▸" [`hg]))))
             []
             (Tactic.exact "exact" (Term.app `hp [`hg `hc]))]))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.intro "intro" [`hc])
          []
          (Mathlib.Tactic.replace'
           "replace"
           [`hc []]
           [(Term.typeSpec
             ":"
             («term_=_»
              (Term.app
               (NumberTheory.Modular.«term↑ₘ_» "↑ₘ" («term-_» "-" `g))
               [(num "1") (num "0")])
              "="
              (num "1")))])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.simp
             "simp"
             []
             []
             []
             ["[" [(Tactic.simpLemma [] [] (Term.app `eq_neg_of_eq_neg [`hc]))] "]"]
             [])])
          []
          (Mathlib.Tactic.tacticReplace_
           "replace"
           (Term.haveDecl
            (Term.haveIdDecl
             [`hg []]
             [(Term.typeSpec
               ":"
               («term_∈_»
                (Algebra.Group.Defs.«term_•_» («term-_» "-" `g) " • " `z)
                "∈"
                (Modular.NumberTheory.Modular.modular_group.fdo "𝒟ᵒ")))]
             ":="
             (Term.subst (Term.proj (Term.app `SL_neg_smul [`g `z]) "." `symm) "▸" [`hg]))))
          []
          (Tactic.exact "exact" (Term.app `hp [`hg `hc]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" (Term.app `hp [`hg `hc]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `hp [`hg `hc])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hc
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hg
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `hp
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.tacticReplace_
       "replace"
       (Term.haveDecl
        (Term.haveIdDecl
         [`hg []]
         [(Term.typeSpec
           ":"
           («term_∈_»
            (Algebra.Group.Defs.«term_•_» («term-_» "-" `g) " • " `z)
            "∈"
            (Modular.NumberTheory.Modular.modular_group.fdo "𝒟ᵒ")))]
         ":="
         (Term.subst (Term.proj (Term.app `SL_neg_smul [`g `z]) "." `symm) "▸" [`hg]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.subst (Term.proj (Term.app `SL_neg_smul [`g `z]) "." `symm) "▸" [`hg])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hg
[PrettyPrinter.parenthesize] ...precedences are 75 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 75, term))
      (Term.proj (Term.app `SL_neg_smul [`g `z]) "." `symm)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `SL_neg_smul [`g `z])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `z
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `SL_neg_smul
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `SL_neg_smul [`g `z]) ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 75, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 75, (some 75, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∈_»
       (Algebra.Group.Defs.«term_•_» («term-_» "-" `g) " • " `z)
       "∈"
       (Modular.NumberTheory.Modular.modular_group.fdo "𝒟ᵒ"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Modular.NumberTheory.Modular.modular_group.fdo "𝒟ᵒ")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Algebra.Group.Defs.«term_•_» («term-_» "-" `g) " • " `z)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `z
[PrettyPrinter.parenthesize] ...precedences are 73 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 73, term))
      («term-_» "-" `g)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g
[PrettyPrinter.parenthesize] ...precedences are 75 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 74 >? 75, (some 75, term) <=? (some 73, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 73, (some 73, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.simp
         "simp"
         []
         []
         []
         ["[" [(Tactic.simpLemma [] [] (Term.app `eq_neg_of_eq_neg [`hc]))] "]"]
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       []
       ["[" [(Tactic.simpLemma [] [] (Term.app `eq_neg_of_eq_neg [`hc]))] "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `eq_neg_of_eq_neg [`hc])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hc
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `eq_neg_of_eq_neg
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.replace'
       "replace"
       [`hc []]
       [(Term.typeSpec
         ":"
         («term_=_»
          (Term.app (NumberTheory.Modular.«term↑ₘ_» "↑ₘ" («term-_» "-" `g)) [(num "1") (num "0")])
          "="
          (num "1")))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Term.app (NumberTheory.Modular.«term↑ₘ_» "↑ₘ" («term-_» "-" `g)) [(num "1") (num "0")])
       "="
       (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app (NumberTheory.Modular.«term↑ₘ_» "↑ₘ" («term-_» "-" `g)) [(num "1") (num "0")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (NumberTheory.Modular.«term↑ₘ_» "↑ₘ" («term-_» "-" `g))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.Modular.«term↑ₘ_»', expected 'NumberTheory.Modular.term↑ₘ_._@.NumberTheory.Modular._hyg.827'
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
/-- An auxiliary result en route to `modular_group.eq_smul_self_of_mem_fdo_mem_fdo`. -/
  theorem
    c_eq_zero
    ( hz : z ∈ 𝒟ᵒ ) ( hg : g • z ∈ 𝒟ᵒ ) : ↑ₘ g 1 0 = 0
    :=
      by
        have
            hp
              : ∀ { g' : SL( 2 , ℤ ) } ( hg' : g' • z ∈ 𝒟ᵒ ) , ↑ₘ g' 1 0 ≠ 1
              :=
              by
                intros
                  by_contra hc
                  let a := ↑ₘ g' 0 0
                  let d := ↑ₘ g' 1 1
                  have had : T ^ - a * g' = S * T ^ d := by rw [ g_eq_of_c_eq_one hc ] group
                  let w := T ^ - a • g' • z
                  have h₁ : w = S • T ^ d • z := by simp only [ w , ← mul_smul , had ]
                  replace
                    h₁
                      : norm_sq w < 1
                      :=
                      h₁.symm ▸ norm_sq_S_smul_lt_one one_lt_norm_sq_T_zpow_smul hz d
                  have h₂ : 1 < norm_sq w := one_lt_norm_sq_T_zpow_smul hg' - a
                  linarith
          have
            hn
              : ↑ₘ g 1 0 ≠ - 1
              :=
              by
                intro hc
                  replace hc : ↑ₘ - g 1 0 = 1
                  · simp [ eq_neg_of_eq_neg hc ]
                  replace hg : - g • z ∈ 𝒟ᵒ := SL_neg_smul g z . symm ▸ hg
                  exact hp hg hc
          specialize hp hg
          rcases int.abs_le_one_iff.mp <| abs_c_le_one hz hg with ⟨ ⟩ <;> tauto
#align modular_group.c_eq_zero ModularGroup.c_eq_zero

/-- Second Main Fundamental Domain Lemma: if both `z` and `g • z` are in the open domain `𝒟ᵒ`,
where `z : ℍ` and `g : SL(2,ℤ)`, then `z = g • z`. -/
theorem eq_smul_self_of_mem_fdo_mem_fdo (hz : z ∈ 𝒟ᵒ) (hg : g • z ∈ 𝒟ᵒ) : z = g • z :=
  by
  obtain ⟨n, hn⟩ := exists_eq_T_zpow_of_c_eq_zero (c_eq_zero hz hg)
  rw [hn] at hg⊢
  simp [eq_zero_of_mem_fdo_of_T_zpow_mem_fdo hz hg, one_smul]
#align modular_group.eq_smul_self_of_mem_fdo_mem_fdo ModularGroup.eq_smul_self_of_mem_fdo_mem_fdo

end UniqueRepresentative

end FundamentalDomain

end ModularGroup

