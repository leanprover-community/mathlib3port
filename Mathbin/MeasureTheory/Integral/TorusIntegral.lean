/-
Copyright (c) 2022 Cuma Kökmen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cuma Kökmen, Yury Kudryashov

! This file was ported from Lean 3 source module measure_theory.integral.torus_integral
! leanprover-community/mathlib commit 18a5306c091183ac90884daa9373fa3b178e8607
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.MeasureTheory.Integral.CircleIntegral

/-!
# Integral over a torus in `ℂⁿ`

In this file we define the integral of a function `f : ℂⁿ → E` over a torus
`{z : ℂⁿ | ∀ i, z i ∈ metric.sphere (c i) (R i)}`. In order to do this, we define
`torus_map (c : ℂⁿ) (R θ : ℝⁿ)` to be the point in `ℂⁿ` given by $z_k=c_k+R_ke^{θ_ki}$,
where $i$ is the imaginary unit, then define `torus_integral f c R` as the integral over
the cube $[0, (λ _, 2π)] = \{θ\|∀ k, 0 ≤ θ_k ≤ 2π\}$ of the Jacobian of the
`torus_map` multiplied by `f (torus_map c R θ)`.

We also define a predicate saying that `f ∘ torus_map c R` is integrable on the cube
`[0, (λ _, 2\pi)]`.

## Main definitions

* `torus_map c R`: the generalized multidimensional exponential map from `ℝⁿ` to `ℂⁿ` that sends
  $θ=(θ_0,…,θ_{n-1})$ to $z=(z_0,…,z_{n-1})$, where $z_k= c_k + R_ke^{θ_k i}$;

* `torus_integrable f c R`: a function `f : ℂⁿ → E` is integrable over the generalized torus
  with center `c : ℂⁿ` and radius `R : ℝⁿ` if `f ∘ torus_map c R` is integrable on the
  closed cube `Icc (0 : ℝⁿ) (λ _, 2 * π)`;

* `torus_integral f c R`: the integral of a function `f : ℂⁿ → E` over a torus with
  center `c ∈ ℂⁿ` and radius `R ∈ ℝⁿ` defined as
  $\iiint_{[0, 2 * π]} (∏_{k = 1}^{n} i R_k e^{θ_k * i}) • f (c + Re^{θ_k i})\,dθ_0…dθ_{k-1}$.

## Main statements

* `torus_integral_dim0`, `torus_integral_dim1`, `torus_integral_succ`: formulas for `torus_integral`
  in cases of dimension `0`, `1`, and `n + 1`.

## Notations

- `ℝ⁰`, `ℝ¹`, `ℝⁿ`, `ℝⁿ⁺¹`: local notation for `fin 0 → ℝ`, `fin 1 → ℝ`, `fin n → ℝ`, and
  `fin (n + 1) → ℝ`, respectively;
- `ℂ⁰`, `ℂ¹`, `ℂⁿ`, `ℂⁿ⁺¹`: local notation for `fin 0 → ℂ`, `fin 1 → ℂ`, `fin n → ℂ`, and
  `fin (n + 1) → ℂ`, respectively;
- `∯ z in T(c, R), f z`: notation for `torus_integral f c R`;
- `∮ z in C(c, R), f z`: notation for `circle_integral f c R`, defined elsewhere;
- `∏ k, f k`: notation for `finset.prod`, defined elsewhere;
- `π`: notation for `real.pi`, defined elsewhere.

## Tags

integral, torus
-/


variable {n : ℕ}

variable {E : Type _} [NormedAddCommGroup E]

noncomputable section

open Complex Set MeasureTheory Function Filter TopologicalSpace

open Real BigOperators

-- mathport name: «exprℝ⁰»
local notation "ℝ⁰" => Fin 0 → ℝ

-- mathport name: «exprℂ⁰»
local notation "ℂ⁰" => Fin 0 → ℂ

-- mathport name: «exprℝ¹»
local notation "ℝ¹" => Fin 1 → ℝ

-- mathport name: «exprℂ¹»
local notation "ℂ¹" => Fin 1 → ℂ

-- mathport name: «exprℝⁿ»
local notation "ℝⁿ" => Fin n → ℝ

-- mathport name: «exprℂⁿ»
local notation "ℂⁿ" => Fin n → ℂ

-- mathport name: «exprℝⁿ⁺¹»
local notation "ℝⁿ⁺¹" => Fin (n + 1) → ℝ

-- mathport name: «exprℂⁿ⁺¹»
local notation "ℂⁿ⁺¹" => Fin (n + 1) → ℂ

/-!
### `torus_map`, a generalization of a torus
-/


/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "The n dimensional exponential map $θ_i ↦ c + R e^{θ_i*I}, θ ∈ ℝⁿ$ representing\na torus in `ℂⁿ` with center `c ∈ ℂⁿ` and generalized radius `R ∈ ℝⁿ`, so we can adjust\nit to every n axis. -/")]
      []
      []
      []
      []
      [])
     (Command.def
      "def"
      (Command.declId `torusMap [])
      (Command.optDeclSig
       [(Term.explicitBinder
         "("
         [`c]
         [":" (MeasureTheory.Integral.TorusIntegral.«termℂⁿ» "ℂⁿ")]
         []
         ")")
        (Term.explicitBinder
         "("
         [`R]
         [":" (MeasureTheory.Integral.TorusIntegral.«termℝⁿ» "ℝⁿ")]
         []
         ")")]
       [(Term.typeSpec
         ":"
         (Term.arrow
          (MeasureTheory.Integral.TorusIntegral.«termℝⁿ» "ℝⁿ")
          "→"
          (MeasureTheory.Integral.TorusIntegral.«termℂⁿ» "ℂⁿ")))])
      (Command.declValSimple
       ":="
       (Term.fun
        "fun"
        (Term.basicFun
         [`θ `i]
         []
         "=>"
         («term_+_»
          (Term.app `c [`i])
          "+"
          («term_*_»
           (Term.app `R [`i])
           "*"
           (Term.app `exp [(«term_*_» (Term.app `θ [`i]) "*" `I)])))))
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`θ `i]
        []
        "=>"
        («term_+_»
         (Term.app `c [`i])
         "+"
         («term_*_»
          (Term.app `R [`i])
          "*"
          (Term.app `exp [(«term_*_» (Term.app `θ [`i]) "*" `I)])))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_»
       (Term.app `c [`i])
       "+"
       («term_*_» (Term.app `R [`i]) "*" (Term.app `exp [(«term_*_» (Term.app `θ [`i]) "*" `I)])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_» (Term.app `R [`i]) "*" (Term.app `exp [(«term_*_» (Term.app `θ [`i]) "*" `I)]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `exp [(«term_*_» (Term.app `θ [`i]) "*" `I)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_*_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_*_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_» (Term.app `θ [`i]) "*" `I)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `I
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (Term.app `θ [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `θ
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1022, (some 1023, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_*_» (Term.app `θ [`i]) "*" `I)
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `exp
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (Term.app `R [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `R
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1022, (some 1023, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      (Term.app `c [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `c
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1022, (some 1023, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `θ
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.arrow
       (MeasureTheory.Integral.TorusIntegral.«termℝⁿ» "ℝⁿ")
       "→"
       (MeasureTheory.Integral.TorusIntegral.«termℂⁿ» "ℂⁿ"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (MeasureTheory.Integral.TorusIntegral.«termℂⁿ» "ℂⁿ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'MeasureTheory.Integral.TorusIntegral.«termℂⁿ»', expected 'MeasureTheory.Integral.TorusIntegral.termℂⁿ._@.MeasureTheory.Integral.TorusIntegral._hyg.195'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    The n dimensional exponential map $θ_i ↦ c + R e^{θ_i*I}, θ ∈ ℝⁿ$ representing
    a torus in `ℂⁿ` with center `c ∈ ℂⁿ` and generalized radius `R ∈ ℝⁿ`, so we can adjust
    it to every n axis. -/
  def torusMap ( c : ℂⁿ ) ( R : ℝⁿ ) : ℝⁿ → ℂⁿ := fun θ i => c i + R i * exp θ i * I
#align torus_map torusMap

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `torus_map_sub_center [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`c]
         [":" (MeasureTheory.Integral.TorusIntegral.«termℂⁿ» "ℂⁿ")]
         []
         ")")
        (Term.explicitBinder
         "("
         [`R]
         [":" (MeasureTheory.Integral.TorusIntegral.«termℝⁿ» "ℝⁿ")]
         []
         ")")
        (Term.explicitBinder
         "("
         [`θ]
         [":" (MeasureTheory.Integral.TorusIntegral.«termℝⁿ» "ℝⁿ")]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         («term_-_» (Term.app `torusMap [`c `R `θ]) "-" `c)
         "="
         (Term.app `torusMap [(num "0") `R `θ]))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Std.Tactic.Ext.tacticExt1___
            "ext1"
            [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `i))])
           []
           (Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `torusMap)] "]"] [])])))
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
         [(Std.Tactic.Ext.tacticExt1___
           "ext1"
           [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `i))])
          []
          (Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `torusMap)] "]"] [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `torusMap)] "]"] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `torusMap
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Ext.tacticExt1___
       "ext1"
       [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `i))])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       («term_-_» (Term.app `torusMap [`c `R `θ]) "-" `c)
       "="
       (Term.app `torusMap [(num "0") `R `θ]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `torusMap [(num "0") `R `θ])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `θ
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `R
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `torusMap
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      («term_-_» (Term.app `torusMap [`c `R `θ]) "-" `c)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `c
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      (Term.app `torusMap [`c `R `θ])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `θ
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `R
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `c
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `torusMap
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1022, (some 1023, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 65, (some 66, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (MeasureTheory.Integral.TorusIntegral.«termℝⁿ» "ℝⁿ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'MeasureTheory.Integral.TorusIntegral.«termℝⁿ»', expected 'MeasureTheory.Integral.TorusIntegral.termℝⁿ._@.MeasureTheory.Integral.TorusIntegral._hyg.158'
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
  torus_map_sub_center
  ( c : ℂⁿ ) ( R : ℝⁿ ) ( θ : ℝⁿ ) : torusMap c R θ - c = torusMap 0 R θ
  := by ext1 i simp [ torusMap ]
#align torus_map_sub_center torus_map_sub_center

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `torus_map_eq_center_iff [])
      (Command.declSig
       [(Term.implicitBinder
         "{"
         [`c]
         [":" (MeasureTheory.Integral.TorusIntegral.«termℂⁿ» "ℂⁿ")]
         "}")
        (Term.implicitBinder
         "{"
         [`R]
         [":" (MeasureTheory.Integral.TorusIntegral.«termℝⁿ» "ℝⁿ")]
         "}")
        (Term.implicitBinder
         "{"
         [`θ]
         [":" (MeasureTheory.Integral.TorusIntegral.«termℝⁿ» "ℝⁿ")]
         "}")]
       (Term.typeSpec
        ":"
        («term_↔_»
         («term_=_» (Term.app `torusMap [`c `R `θ]) "=" `c)
         "↔"
         («term_=_» `R "=" (num "0")))))
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
             [(Tactic.simpLemma [] [] `funext_iff)
              ","
              (Tactic.simpLemma [] [] `torusMap)
              ","
              (Tactic.simpLemma [] [] `exp_ne_zero)]
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
            [(Tactic.simpLemma [] [] `funext_iff)
             ","
             (Tactic.simpLemma [] [] `torusMap)
             ","
             (Tactic.simpLemma [] [] `exp_ne_zero)]
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
        [(Tactic.simpLemma [] [] `funext_iff)
         ","
         (Tactic.simpLemma [] [] `torusMap)
         ","
         (Tactic.simpLemma [] [] `exp_ne_zero)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `exp_ne_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `torusMap
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `funext_iff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_↔_»
       («term_=_» (Term.app `torusMap [`c `R `θ]) "=" `c)
       "↔"
       («term_=_» `R "=" (num "0")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_» `R "=" (num "0"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `R
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 21 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 20, term))
      («term_=_» (Term.app `torusMap [`c `R `θ]) "=" `c)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `c
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app `torusMap [`c `R `θ])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `θ
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `R
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `c
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `torusMap
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
      (MeasureTheory.Integral.TorusIntegral.«termℝⁿ» "ℝⁿ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'MeasureTheory.Integral.TorusIntegral.«termℝⁿ»', expected 'MeasureTheory.Integral.TorusIntegral.termℝⁿ._@.MeasureTheory.Integral.TorusIntegral._hyg.158'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.implicitBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  torus_map_eq_center_iff
  { c : ℂⁿ } { R : ℝⁿ } { θ : ℝⁿ } : torusMap c R θ = c ↔ R = 0
  := by simp [ funext_iff , torusMap , exp_ne_zero ]
#align torus_map_eq_center_iff torus_map_eq_center_iff

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
      (Command.declId `torus_map_zero_radius [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`c]
         [":" (MeasureTheory.Integral.TorusIntegral.«termℂⁿ» "ℂⁿ")]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app `torusMap [`c (num "0")])
         "="
         (Term.app `const [(MeasureTheory.Integral.TorusIntegral.«termℝⁿ» "ℝⁿ") `c]))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Std.Tactic.Ext.tacticExt1___ "ext1" [])
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule
               []
               (Term.app (Term.proj `torus_map_eq_center_iff "." (fieldIdx "2")) [`rfl]))]
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
         [(Std.Tactic.Ext.tacticExt1___ "ext1" [])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule
              []
              (Term.app (Term.proj `torus_map_eq_center_iff "." (fieldIdx "2")) [`rfl]))]
            "]")
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule
          []
          (Term.app (Term.proj `torus_map_eq_center_iff "." (fieldIdx "2")) [`rfl]))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj `torus_map_eq_center_iff "." (fieldIdx "2")) [`rfl])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rfl
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `torus_map_eq_center_iff "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `torus_map_eq_center_iff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Ext.tacticExt1___ "ext1" [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app `torusMap [`c (num "0")])
       "="
       (Term.app `const [(MeasureTheory.Integral.TorusIntegral.«termℝⁿ» "ℝⁿ") `c]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `const [(MeasureTheory.Integral.TorusIntegral.«termℝⁿ» "ℝⁿ") `c])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `c
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'MeasureTheory.Integral.TorusIntegral.«termℝⁿ»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'MeasureTheory.Integral.TorusIntegral.«termℝⁿ»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (MeasureTheory.Integral.TorusIntegral.«termℝⁿ» "ℝⁿ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'MeasureTheory.Integral.TorusIntegral.«termℝⁿ»', expected 'MeasureTheory.Integral.TorusIntegral.termℝⁿ._@.MeasureTheory.Integral.TorusIntegral._hyg.158'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ simp ]
  theorem
    torus_map_zero_radius
    ( c : ℂⁿ ) : torusMap c 0 = const ℝⁿ c
    := by ext1 rw [ torus_map_eq_center_iff . 2 rfl ]
#align torus_map_zero_radius torus_map_zero_radius

/-!
### Integrability of a function on a generalized torus
-/


/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "A function `f : ℂⁿ → E` is integrable on the generalized torus if the function\n`f ∘ torus_map c R θ` is integrable on `Icc (0 : ℝⁿ) (λ _, 2 * π)`-/")]
      []
      []
      []
      []
      [])
     (Command.def
      "def"
      (Command.declId `TorusIntegrable [])
      (Command.optDeclSig
       [(Term.explicitBinder
         "("
         [`f]
         [":" (Term.arrow (MeasureTheory.Integral.TorusIntegral.«termℂⁿ» "ℂⁿ") "→" `E)]
         []
         ")")
        (Term.explicitBinder
         "("
         [`c]
         [":" (MeasureTheory.Integral.TorusIntegral.«termℂⁿ» "ℂⁿ")]
         []
         ")")
        (Term.explicitBinder
         "("
         [`R]
         [":" (MeasureTheory.Integral.TorusIntegral.«termℝⁿ» "ℝⁿ")]
         []
         ")")]
       [(Term.typeSpec ":" (Term.prop "Prop"))])
      (Command.declValSimple
       ":="
       (Term.app
        `IntegrableOn
        [(Term.fun
          "fun"
          (Term.basicFun
           [`θ]
           [(Term.typeSpec ":" (MeasureTheory.Integral.TorusIntegral.«termℝⁿ» "ℝⁿ"))]
           "=>"
           (Term.app `f [(Term.app `torusMap [`c `R `θ])])))
         (Term.app
          `Icc
          [(Term.typeAscription
            "("
            (num "0")
            ":"
            [(MeasureTheory.Integral.TorusIntegral.«termℝⁿ» "ℝⁿ")]
            ")")
           (Term.fun
            "fun"
            (Term.basicFun
             [(Term.hole "_")]
             []
             "=>"
             («term_*_»
              (num "2")
              "*"
              (Real.Analysis.SpecialFunctions.Trigonometric.Basic.real.pi "π"))))])
         `volume])
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `IntegrableOn
       [(Term.fun
         "fun"
         (Term.basicFun
          [`θ]
          [(Term.typeSpec ":" (MeasureTheory.Integral.TorusIntegral.«termℝⁿ» "ℝⁿ"))]
          "=>"
          (Term.app `f [(Term.app `torusMap [`c `R `θ])])))
        (Term.app
         `Icc
         [(Term.typeAscription
           "("
           (num "0")
           ":"
           [(MeasureTheory.Integral.TorusIntegral.«termℝⁿ» "ℝⁿ")]
           ")")
          (Term.fun
           "fun"
           (Term.basicFun
            [(Term.hole "_")]
            []
            "=>"
            («term_*_»
             (num "2")
             "*"
             (Real.Analysis.SpecialFunctions.Trigonometric.Basic.real.pi "π"))))])
        `volume])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `volume
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       `Icc
       [(Term.typeAscription
         "("
         (num "0")
         ":"
         [(MeasureTheory.Integral.TorusIntegral.«termℝⁿ» "ℝⁿ")]
         ")")
        (Term.fun
         "fun"
         (Term.basicFun
          [(Term.hole "_")]
          []
          "=>"
          («term_*_»
           (num "2")
           "*"
           (Real.Analysis.SpecialFunctions.Trigonometric.Basic.real.pi "π"))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [(Term.hole "_")]
        []
        "=>"
        («term_*_» (num "2") "*" (Real.Analysis.SpecialFunctions.Trigonometric.Basic.real.pi "π"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_» (num "2") "*" (Real.Analysis.SpecialFunctions.Trigonometric.Basic.real.pi "π"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Real.Analysis.SpecialFunctions.Trigonometric.Basic.real.pi "π")
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.typeAscription
       "("
       (num "0")
       ":"
       [(MeasureTheory.Integral.TorusIntegral.«termℝⁿ» "ℝⁿ")]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (MeasureTheory.Integral.TorusIntegral.«termℝⁿ» "ℝⁿ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'MeasureTheory.Integral.TorusIntegral.«termℝⁿ»', expected 'MeasureTheory.Integral.TorusIntegral.termℝⁿ._@.MeasureTheory.Integral.TorusIntegral._hyg.158'
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
    A function `f : ℂⁿ → E` is integrable on the generalized torus if the function
    `f ∘ torus_map c R θ` is integrable on `Icc (0 : ℝⁿ) (λ _, 2 * π)`-/
  def
    TorusIntegrable
    ( f : ℂⁿ → E ) ( c : ℂⁿ ) ( R : ℝⁿ ) : Prop
    := IntegrableOn fun θ : ℝⁿ => f torusMap c R θ Icc ( 0 : ℝⁿ ) fun _ => 2 * π volume
#align torus_integrable TorusIntegrable

namespace TorusIntegrable

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.variable
     "variable"
     [(Term.implicitBinder
       "{"
       [`f `g]
       [":" (Term.arrow (MeasureTheory.Integral.TorusIntegral.«termℂⁿ» "ℂⁿ") "→" `E)]
       "}")
      (Term.implicitBinder "{" [`c] [":" (MeasureTheory.Integral.TorusIntegral.«termℂⁿ» "ℂⁿ")] "}")
      (Term.implicitBinder
       "{"
       [`R]
       [":" (MeasureTheory.Integral.TorusIntegral.«termℝⁿ» "ℝⁿ")]
       "}")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.implicitBinder', expected 'Lean.Parser.Term.explicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.implicitBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (MeasureTheory.Integral.TorusIntegral.«termℝⁿ» "ℝⁿ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'MeasureTheory.Integral.TorusIntegral.«termℝⁿ»', expected 'MeasureTheory.Integral.TorusIntegral.termℝⁿ._@.MeasureTheory.Integral.TorusIntegral._hyg.158'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.implicitBinder', expected 'Lean.Parser.Term.instBinder'-/-- failed to format: format: uncaught backtrack exception
variable { f g : ℂⁿ → E } { c : ℂⁿ } { R : ℝⁿ }

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment "/--" "Constant functions are torus integrable -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `torus_integrable_const [])
      (Command.declSig
       [(Term.explicitBinder "(" [`a] [":" `E] [] ")")
        (Term.explicitBinder
         "("
         [`c]
         [":" (MeasureTheory.Integral.TorusIntegral.«termℂⁿ» "ℂⁿ")]
         []
         ")")
        (Term.explicitBinder
         "("
         [`R]
         [":" (MeasureTheory.Integral.TorusIntegral.«termℝⁿ» "ℝⁿ")]
         []
         ")")]
       (Term.typeSpec
        ":"
        (Term.app
         `TorusIntegrable
         [(Term.fun "fun" (Term.basicFun [(Term.hole "_")] [] "=>" `a)) `c `R])))
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
             [(Tactic.simpLemma [] [] `TorusIntegrable)
              ","
              (Tactic.simpLemma [] [] `measure_Icc_lt_top)]
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
            [(Tactic.simpLemma [] [] `TorusIntegrable)
             ","
             (Tactic.simpLemma [] [] `measure_Icc_lt_top)]
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
        [(Tactic.simpLemma [] [] `TorusIntegrable) "," (Tactic.simpLemma [] [] `measure_Icc_lt_top)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `measure_Icc_lt_top
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `TorusIntegrable
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app
       `TorusIntegrable
       [(Term.fun "fun" (Term.basicFun [(Term.hole "_")] [] "=>" `a)) `c `R])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `R
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `c
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.fun "fun" (Term.basicFun [(Term.hole "_")] [] "=>" `a))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.fun "fun" (Term.basicFun [(Term.hole "_")] [] "=>" `a))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `TorusIntegrable
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (MeasureTheory.Integral.TorusIntegral.«termℝⁿ» "ℝⁿ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'MeasureTheory.Integral.TorusIntegral.«termℝⁿ»', expected 'MeasureTheory.Integral.TorusIntegral.termℝⁿ._@.MeasureTheory.Integral.TorusIntegral._hyg.158'
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
/-- Constant functions are torus integrable -/
  theorem
    torus_integrable_const
    ( a : E ) ( c : ℂⁿ ) ( R : ℝⁿ ) : TorusIntegrable fun _ => a c R
    := by simp [ TorusIntegrable , measure_Icc_lt_top ]
#align torus_integrable.torus_integrable_const TorusIntegrable.torus_integrable_const

/-- If `f` is torus integrable then `-f` is torus integrable. -/
protected theorem neg (hf : TorusIntegrable f c R) : TorusIntegrable (-f) c R :=
  hf.neg
#align torus_integrable.neg TorusIntegrable.neg

/-- If `f` and `g` are two torus integrable functions, then so is `f + g`. -/
protected theorem add (hf : TorusIntegrable f c R) (hg : TorusIntegrable g c R) :
    TorusIntegrable (f + g) c R :=
  hf.add hg
#align torus_integrable.add TorusIntegrable.add

/-- If `f` and `g` are two torus integrable functions, then so is `f - g`. -/
protected theorem sub (hf : TorusIntegrable f c R) (hg : TorusIntegrable g c R) :
    TorusIntegrable (f - g) c R :=
  hf.sub hg
#align torus_integrable.sub TorusIntegrable.sub

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `torus_integrable_zero_radius [])
      (Command.declSig
       [(Term.implicitBinder
         "{"
         [`f]
         [":" (Term.arrow (MeasureTheory.Integral.TorusIntegral.«termℂⁿ» "ℂⁿ") "→" `E)]
         "}")
        (Term.implicitBinder
         "{"
         [`c]
         [":" (MeasureTheory.Integral.TorusIntegral.«termℂⁿ» "ℂⁿ")]
         "}")]
       (Term.typeSpec ":" (Term.app `TorusIntegrable [`f `c (num "0")])))
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
             [(Tactic.rwRule [] `TorusIntegrable) "," (Tactic.rwRule [] `torus_map_zero_radius)]
             "]")
            [])
           []
           (Tactic.apply
            "apply"
            (Term.app `torus_integrable_const [(Term.app `f [`c]) `c (num "0")]))])))
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
            [(Tactic.rwRule [] `TorusIntegrable) "," (Tactic.rwRule [] `torus_map_zero_radius)]
            "]")
           [])
          []
          (Tactic.apply
           "apply"
           (Term.app `torus_integrable_const [(Term.app `f [`c]) `c (num "0")]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.apply "apply" (Term.app `torus_integrable_const [(Term.app `f [`c]) `c (num "0")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `torus_integrable_const [(Term.app `f [`c]) `c (num "0")])
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `f [`c])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `c
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `f [`c]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `torus_integrable_const
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
        [(Tactic.rwRule [] `TorusIntegrable) "," (Tactic.rwRule [] `torus_map_zero_radius)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `torus_map_zero_radius
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `TorusIntegrable
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app `TorusIntegrable [`f `c (num "0")])
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `TorusIntegrable
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.implicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.implicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.implicitBinder', expected 'Lean.Parser.Term.explicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.implicitBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (MeasureTheory.Integral.TorusIntegral.«termℂⁿ» "ℂⁿ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'MeasureTheory.Integral.TorusIntegral.«termℂⁿ»', expected 'MeasureTheory.Integral.TorusIntegral.termℂⁿ._@.MeasureTheory.Integral.TorusIntegral._hyg.195'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.implicitBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  torus_integrable_zero_radius
  { f : ℂⁿ → E } { c : ℂⁿ } : TorusIntegrable f c 0
  := by rw [ TorusIntegrable , torus_map_zero_radius ] apply torus_integrable_const f c c 0
#align torus_integrable.torus_integrable_zero_radius TorusIntegrable.torus_integrable_zero_radius

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "The function given in the definition of `torus_integral` is integrable. -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `functionIntegrable [])
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `NormedSpace [(Data.Complex.Basic.termℂ "ℂ") `E]) "]")
        (Term.explicitBinder "(" [`hf] [":" (Term.app `TorusIntegrable [`f `c `R])] [] ")")]
       (Term.typeSpec
        ":"
        (Term.app
         `IntegrableOn
         [(Term.fun
           "fun"
           (Term.basicFun
            [`θ]
            [(Term.typeSpec ":" (MeasureTheory.Integral.TorusIntegral.«termℝⁿ» "ℝⁿ"))]
            "=>"
            (Algebra.Group.Defs.«term_•_»
             (Term.typeAscription
              "("
              (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
               "∏"
               (Std.ExtendedBinder.extBinders
                (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
               ", "
               («term_*_»
                («term_*_»
                 (Term.app `R [`i])
                 "*"
                 (Term.app `exp [(«term_*_» (Term.app `θ [`i]) "*" `I)]))
                "*"
                `I))
              ":"
              [(Data.Complex.Basic.termℂ "ℂ")]
              ")")
             " • "
             (Term.app `f [(Term.app `torusMap [`c `R `θ])]))))
          (Term.app
           `Icc
           [(Term.typeAscription
             "("
             (num "0")
             ":"
             [(MeasureTheory.Integral.TorusIntegral.«termℝⁿ» "ℝⁿ")]
             ")")
            (Term.fun
             "fun"
             (Term.basicFun
              [(Term.hole "_")]
              []
              "=>"
              («term_*_»
               (num "2")
               "*"
               (Real.Analysis.SpecialFunctions.Trigonometric.Basic.real.pi "π"))))])
          `volume])))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.refine'
            "refine'"
            (Term.app
             (Term.proj
              (Term.app
               `hf.norm.const_mul
               [(BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
                 "∏"
                 (Std.ExtendedBinder.extBinders
                  (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
                 ", "
                 («term|___|» (group "|") (Term.app `R [`i]) (group) "|"))])
              "."
              `mono')
             [(Term.hole "_") (Term.hole "_")]))
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.refine'
              "refine'"
              (Term.app
               (Term.proj (Term.app `Continuous.aeStronglyMeasurable [(Term.hole "_")]) "." `smul)
               [(Term.proj `hf "." (fieldIdx "1"))]))
             []
             (Tactic.exact
              "exact"
              (Term.app
               `continuous_finset_prod
               [`Finset.univ
                (Term.fun
                 "fun"
                 (Term.basicFun
                  [`i `hi]
                  []
                  "=>"
                  (Term.app
                   (Term.proj
                    (Term.app
                     `continuous_const.mul
                     [(Term.proj
                       (Term.app
                        (Term.proj
                         (Term.app `continuous_of_real.comp [(Term.app `continuous_apply [`i])])
                         "."
                         `mul)
                        [`continuous_const])
                       "."
                       `cexp)])
                    "."
                    `mul)
                   [`continuous_const])))]))])
           []
           (Tactic.simp
            "simp"
            []
            []
            []
            ["[" [(Tactic.simpLemma [] [] `norm_smul) "," (Tactic.simpLemma [] [] `map_prod)] "]"]
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
         [(Tactic.refine'
           "refine'"
           (Term.app
            (Term.proj
             (Term.app
              `hf.norm.const_mul
              [(BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
                "∏"
                (Std.ExtendedBinder.extBinders
                 (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
                ", "
                («term|___|» (group "|") (Term.app `R [`i]) (group) "|"))])
             "."
             `mono')
            [(Term.hole "_") (Term.hole "_")]))
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.refine'
             "refine'"
             (Term.app
              (Term.proj (Term.app `Continuous.aeStronglyMeasurable [(Term.hole "_")]) "." `smul)
              [(Term.proj `hf "." (fieldIdx "1"))]))
            []
            (Tactic.exact
             "exact"
             (Term.app
              `continuous_finset_prod
              [`Finset.univ
               (Term.fun
                "fun"
                (Term.basicFun
                 [`i `hi]
                 []
                 "=>"
                 (Term.app
                  (Term.proj
                   (Term.app
                    `continuous_const.mul
                    [(Term.proj
                      (Term.app
                       (Term.proj
                        (Term.app `continuous_of_real.comp [(Term.app `continuous_apply [`i])])
                        "."
                        `mul)
                       [`continuous_const])
                      "."
                      `cexp)])
                   "."
                   `mul)
                  [`continuous_const])))]))])
          []
          (Tactic.simp
           "simp"
           []
           []
           []
           ["[" [(Tactic.simpLemma [] [] `norm_smul) "," (Tactic.simpLemma [] [] `map_prod)] "]"]
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       []
       ["[" [(Tactic.simpLemma [] [] `norm_smul) "," (Tactic.simpLemma [] [] `map_prod)] "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `map_prod
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `norm_smul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.refine'
         "refine'"
         (Term.app
          (Term.proj (Term.app `Continuous.aeStronglyMeasurable [(Term.hole "_")]) "." `smul)
          [(Term.proj `hf "." (fieldIdx "1"))]))
        []
        (Tactic.exact
         "exact"
         (Term.app
          `continuous_finset_prod
          [`Finset.univ
           (Term.fun
            "fun"
            (Term.basicFun
             [`i `hi]
             []
             "=>"
             (Term.app
              (Term.proj
               (Term.app
                `continuous_const.mul
                [(Term.proj
                  (Term.app
                   (Term.proj
                    (Term.app `continuous_of_real.comp [(Term.app `continuous_apply [`i])])
                    "."
                    `mul)
                   [`continuous_const])
                  "."
                  `cexp)])
               "."
               `mul)
              [`continuous_const])))]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.app
        `continuous_finset_prod
        [`Finset.univ
         (Term.fun
          "fun"
          (Term.basicFun
           [`i `hi]
           []
           "=>"
           (Term.app
            (Term.proj
             (Term.app
              `continuous_const.mul
              [(Term.proj
                (Term.app
                 (Term.proj
                  (Term.app `continuous_of_real.comp [(Term.app `continuous_apply [`i])])
                  "."
                  `mul)
                 [`continuous_const])
                "."
                `cexp)])
             "."
             `mul)
            [`continuous_const])))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `continuous_finset_prod
       [`Finset.univ
        (Term.fun
         "fun"
         (Term.basicFun
          [`i `hi]
          []
          "=>"
          (Term.app
           (Term.proj
            (Term.app
             `continuous_const.mul
             [(Term.proj
               (Term.app
                (Term.proj
                 (Term.app `continuous_of_real.comp [(Term.app `continuous_apply [`i])])
                 "."
                 `mul)
                [`continuous_const])
               "."
               `cexp)])
            "."
            `mul)
           [`continuous_const])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`i `hi]
        []
        "=>"
        (Term.app
         (Term.proj
          (Term.app
           `continuous_const.mul
           [(Term.proj
             (Term.app
              (Term.proj
               (Term.app `continuous_of_real.comp [(Term.app `continuous_apply [`i])])
               "."
               `mul)
              [`continuous_const])
             "."
             `cexp)])
          "."
          `mul)
         [`continuous_const])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (Term.app
         `continuous_const.mul
         [(Term.proj
           (Term.app
            (Term.proj
             (Term.app `continuous_of_real.comp [(Term.app `continuous_apply [`i])])
             "."
             `mul)
            [`continuous_const])
           "."
           `cexp)])
        "."
        `mul)
       [`continuous_const])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `continuous_const
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (Term.app
        `continuous_const.mul
        [(Term.proj
          (Term.app
           (Term.proj
            (Term.app `continuous_of_real.comp [(Term.app `continuous_apply [`i])])
            "."
            `mul)
           [`continuous_const])
          "."
          `cexp)])
       "."
       `mul)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       `continuous_const.mul
       [(Term.proj
         (Term.app
          (Term.proj
           (Term.app `continuous_of_real.comp [(Term.app `continuous_apply [`i])])
           "."
           `mul)
          [`continuous_const])
         "."
         `cexp)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj
       (Term.app
        (Term.proj (Term.app `continuous_of_real.comp [(Term.app `continuous_apply [`i])]) "." `mul)
        [`continuous_const])
       "."
       `cexp)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       (Term.proj (Term.app `continuous_of_real.comp [(Term.app `continuous_apply [`i])]) "." `mul)
       [`continuous_const])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `continuous_const
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app `continuous_of_real.comp [(Term.app `continuous_apply [`i])]) "." `mul)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `continuous_of_real.comp [(Term.app `continuous_apply [`i])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
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
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `continuous_apply [`i]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `continuous_of_real.comp
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `continuous_of_real.comp [(Term.paren "(" (Term.app `continuous_apply [`i]) ")")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      (Term.proj
       (Term.paren
        "("
        (Term.app `continuous_of_real.comp [(Term.paren "(" (Term.app `continuous_apply [`i]) ")")])
        ")")
       "."
       `mul)
      [`continuous_const])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `continuous_const.mul
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `continuous_const.mul
      [(Term.proj
        (Term.paren
         "("
         (Term.app
          (Term.proj
           (Term.paren
            "("
            (Term.app
             `continuous_of_real.comp
             [(Term.paren "(" (Term.app `continuous_apply [`i]) ")")])
            ")")
           "."
           `mul)
          [`continuous_const])
         ")")
        "."
        `cexp)])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hi
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      `Finset.univ
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `continuous_finset_prod
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine'
       "refine'"
       (Term.app
        (Term.proj (Term.app `Continuous.aeStronglyMeasurable [(Term.hole "_")]) "." `smul)
        [(Term.proj `hf "." (fieldIdx "1"))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj (Term.app `Continuous.aeStronglyMeasurable [(Term.hole "_")]) "." `smul)
       [(Term.proj `hf "." (fieldIdx "1"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `hf "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hf
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app `Continuous.aeStronglyMeasurable [(Term.hole "_")]) "." `smul)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `Continuous.aeStronglyMeasurable [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Continuous.aeStronglyMeasurable
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `Continuous.aeStronglyMeasurable [(Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine'
       "refine'"
       (Term.app
        (Term.proj
         (Term.app
          `hf.norm.const_mul
          [(BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
            "∏"
            (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
            ", "
            («term|___|» (group "|") (Term.app `R [`i]) (group) "|"))])
         "."
         `mono')
        [(Term.hole "_") (Term.hole "_")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (Term.app
         `hf.norm.const_mul
         [(BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
           "∏"
           (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
           ", "
           («term|___|» (group "|") (Term.app `R [`i]) (group) "|"))])
        "."
        `mono')
       [(Term.hole "_") (Term.hole "_")])
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
      (Term.proj
       (Term.app
        `hf.norm.const_mul
        [(BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
          "∏"
          (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
          ", "
          («term|___|» (group "|") (Term.app `R [`i]) (group) "|"))])
       "."
       `mono')
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       `hf.norm.const_mul
       [(BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
         "∏"
         (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
         ", "
         («term|___|» (group "|") (Term.app `R [`i]) (group) "|"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'BigOperators.Algebra.BigOperators.Basic.finset.prod_univ', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'BigOperators.Algebra.BigOperators.Basic.finset.prod_univ', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
       "∏"
       (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
       ", "
       («term|___|» (group "|") (Term.app `R [`i]) (group) "|"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term|___|» (group "|") (Term.app `R [`i]) (group) "|")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `R [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `R
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
      "∏"
      (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
      ", "
      («term|___|» (group "|") (Term.app `R [`i]) (group) "|"))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `hf.norm.const_mul
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `hf.norm.const_mul
      [(Term.paren
        "("
        (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
         "∏"
         (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
         ", "
         («term|___|» (group "|") (Term.app `R [`i]) (group) "|"))
        ")")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app
       `IntegrableOn
       [(Term.fun
         "fun"
         (Term.basicFun
          [`θ]
          [(Term.typeSpec ":" (MeasureTheory.Integral.TorusIntegral.«termℝⁿ» "ℝⁿ"))]
          "=>"
          (Algebra.Group.Defs.«term_•_»
           (Term.typeAscription
            "("
            (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
             "∏"
             (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
             ", "
             («term_*_»
              («term_*_»
               (Term.app `R [`i])
               "*"
               (Term.app `exp [(«term_*_» (Term.app `θ [`i]) "*" `I)]))
              "*"
              `I))
            ":"
            [(Data.Complex.Basic.termℂ "ℂ")]
            ")")
           " • "
           (Term.app `f [(Term.app `torusMap [`c `R `θ])]))))
        (Term.app
         `Icc
         [(Term.typeAscription
           "("
           (num "0")
           ":"
           [(MeasureTheory.Integral.TorusIntegral.«termℝⁿ» "ℝⁿ")]
           ")")
          (Term.fun
           "fun"
           (Term.basicFun
            [(Term.hole "_")]
            []
            "=>"
            («term_*_»
             (num "2")
             "*"
             (Real.Analysis.SpecialFunctions.Trigonometric.Basic.real.pi "π"))))])
        `volume])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `volume
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       `Icc
       [(Term.typeAscription
         "("
         (num "0")
         ":"
         [(MeasureTheory.Integral.TorusIntegral.«termℝⁿ» "ℝⁿ")]
         ")")
        (Term.fun
         "fun"
         (Term.basicFun
          [(Term.hole "_")]
          []
          "=>"
          («term_*_»
           (num "2")
           "*"
           (Real.Analysis.SpecialFunctions.Trigonometric.Basic.real.pi "π"))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [(Term.hole "_")]
        []
        "=>"
        («term_*_» (num "2") "*" (Real.Analysis.SpecialFunctions.Trigonometric.Basic.real.pi "π"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_» (num "2") "*" (Real.Analysis.SpecialFunctions.Trigonometric.Basic.real.pi "π"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Real.Analysis.SpecialFunctions.Trigonometric.Basic.real.pi "π")
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.typeAscription
       "("
       (num "0")
       ":"
       [(MeasureTheory.Integral.TorusIntegral.«termℝⁿ» "ℝⁿ")]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (MeasureTheory.Integral.TorusIntegral.«termℝⁿ» "ℝⁿ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'MeasureTheory.Integral.TorusIntegral.«termℝⁿ»', expected 'MeasureTheory.Integral.TorusIntegral.termℝⁿ._@.MeasureTheory.Integral.TorusIntegral._hyg.158'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/-- The function given in the definition of `torus_integral` is integrable. -/
  theorem
    functionIntegrable
    [ NormedSpace ℂ E ] ( hf : TorusIntegrable f c R )
      :
        IntegrableOn
          fun θ : ℝⁿ => ( ∏ i , R i * exp θ i * I * I : ℂ ) • f torusMap c R θ
            Icc ( 0 : ℝⁿ ) fun _ => 2 * π
            volume
    :=
      by
        refine' hf.norm.const_mul ∏ i , | R i | . mono' _ _
          ·
            refine' Continuous.aeStronglyMeasurable _ . smul hf . 1
              exact
                continuous_finset_prod
                  Finset.univ
                    fun
                      i hi
                        =>
                        continuous_const.mul
                              continuous_of_real.comp continuous_apply i . mul continuous_const
                                .
                                cexp
                            .
                            mul
                          continuous_const
          simp [ norm_smul , map_prod ]
#align torus_integrable.function_integrable TorusIntegrable.functionIntegrable

end TorusIntegrable

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.variable
     "variable"
     [(Term.instBinder "[" [] (Term.app `NormedSpace [(Data.Complex.Basic.termℂ "ℂ") `E]) "]")
      (Term.instBinder "[" [] (Term.app `CompleteSpace [`E]) "]")
      (Term.implicitBinder
       "{"
       [`f `g]
       [":" (Term.arrow (MeasureTheory.Integral.TorusIntegral.«termℂⁿ» "ℂⁿ") "→" `E)]
       "}")
      (Term.implicitBinder "{" [`c] [":" (MeasureTheory.Integral.TorusIntegral.«termℂⁿ» "ℂⁿ")] "}")
      (Term.implicitBinder
       "{"
       [`R]
       [":" (MeasureTheory.Integral.TorusIntegral.«termℝⁿ» "ℝⁿ")]
       "}")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.implicitBinder', expected 'Lean.Parser.Term.explicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.implicitBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (MeasureTheory.Integral.TorusIntegral.«termℝⁿ» "ℝⁿ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'MeasureTheory.Integral.TorusIntegral.«termℝⁿ»', expected 'MeasureTheory.Integral.TorusIntegral.termℝⁿ._@.MeasureTheory.Integral.TorusIntegral._hyg.158'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.implicitBinder', expected 'Lean.Parser.Term.instBinder'-/-- failed to format: format: uncaught backtrack exception
variable [ NormedSpace ℂ E ] [ CompleteSpace E ] { f g : ℂⁿ → E } { c : ℂⁿ } { R : ℝⁿ }

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "The definition of the integral over a generalized torus with center `c ∈ ℂⁿ` and radius `R ∈ ℝⁿ`\nas the `•`-product of the derivative of `torus_map` and `f (torus_map c R θ)`-/")]
      []
      []
      []
      []
      [])
     (Command.def
      "def"
      (Command.declId `torusIntegral [])
      (Command.optDeclSig
       [(Term.explicitBinder
         "("
         [`f]
         [":" (Term.arrow (MeasureTheory.Integral.TorusIntegral.«termℂⁿ» "ℂⁿ") "→" `E)]
         []
         ")")
        (Term.explicitBinder
         "("
         [`c]
         [":" (MeasureTheory.Integral.TorusIntegral.«termℂⁿ» "ℂⁿ")]
         []
         ")")
        (Term.explicitBinder
         "("
         [`R]
         [":" (MeasureTheory.Integral.TorusIntegral.«termℝⁿ» "ℝⁿ")]
         []
         ")")]
       [])
      (Command.declValSimple
       ":="
       (MeasureTheory.MeasureTheory.Integral.Bochner.«term∫_in_,_»
        "∫"
        (Std.ExtendedBinder.extBinders
         (Std.ExtendedBinder.extBinder
          (Lean.binderIdent `θ)
          [(group ":" (MeasureTheory.Integral.TorusIntegral.«termℝⁿ» "ℝⁿ"))]))
        " in "
        (Term.app
         `Icc
         [(Term.typeAscription
           "("
           (num "0")
           ":"
           [(MeasureTheory.Integral.TorusIntegral.«termℝⁿ» "ℝⁿ")]
           ")")
          (Term.fun
           "fun"
           (Term.basicFun
            [(Term.hole "_")]
            []
            "=>"
            («term_*_»
             (num "2")
             "*"
             (Real.Analysis.SpecialFunctions.Trigonometric.Basic.real.pi "π"))))])
        ", "
        (Algebra.Group.Defs.«term_•_»
         (Term.typeAscription
          "("
          (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
           "∏"
           (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
           ", "
           («term_*_»
            («term_*_»
             (Term.app `R [`i])
             "*"
             (Term.app `exp [(«term_*_» (Term.app `θ [`i]) "*" `I)]))
            "*"
            `I))
          ":"
          [(Data.Complex.Basic.termℂ "ℂ")]
          ")")
         " • "
         (Term.app `f [(Term.app `torusMap [`c `R `θ])])))
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (MeasureTheory.MeasureTheory.Integral.Bochner.«term∫_in_,_»
       "∫"
       (Std.ExtendedBinder.extBinders
        (Std.ExtendedBinder.extBinder
         (Lean.binderIdent `θ)
         [(group ":" (MeasureTheory.Integral.TorusIntegral.«termℝⁿ» "ℝⁿ"))]))
       " in "
       (Term.app
        `Icc
        [(Term.typeAscription
          "("
          (num "0")
          ":"
          [(MeasureTheory.Integral.TorusIntegral.«termℝⁿ» "ℝⁿ")]
          ")")
         (Term.fun
          "fun"
          (Term.basicFun
           [(Term.hole "_")]
           []
           "=>"
           («term_*_»
            (num "2")
            "*"
            (Real.Analysis.SpecialFunctions.Trigonometric.Basic.real.pi "π"))))])
       ", "
       (Algebra.Group.Defs.«term_•_»
        (Term.typeAscription
         "("
         (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
          "∏"
          (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
          ", "
          («term_*_»
           («term_*_»
            (Term.app `R [`i])
            "*"
            (Term.app `exp [(«term_*_» (Term.app `θ [`i]) "*" `I)]))
           "*"
           `I))
         ":"
         [(Data.Complex.Basic.termℂ "ℂ")]
         ")")
        " • "
        (Term.app `f [(Term.app `torusMap [`c `R `θ])])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Algebra.Group.Defs.«term_•_»
       (Term.typeAscription
        "("
        (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
         "∏"
         (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
         ", "
         («term_*_»
          («term_*_» (Term.app `R [`i]) "*" (Term.app `exp [(«term_*_» (Term.app `θ [`i]) "*" `I)]))
          "*"
          `I))
        ":"
        [(Data.Complex.Basic.termℂ "ℂ")]
        ")")
       " • "
       (Term.app `f [(Term.app `torusMap [`c `R `θ])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `f [(Term.app `torusMap [`c `R `θ])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `torusMap [`c `R `θ])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `θ
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `R
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `c
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `torusMap
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `torusMap [`c `R `θ]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 73 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 73, term))
      (Term.typeAscription
       "("
       (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
        "∏"
        (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
        ", "
        («term_*_»
         («term_*_» (Term.app `R [`i]) "*" (Term.app `exp [(«term_*_» (Term.app `θ [`i]) "*" `I)]))
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
      (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
       "∏"
       (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
       ", "
       («term_*_»
        («term_*_» (Term.app `R [`i]) "*" (Term.app `exp [(«term_*_» (Term.app `θ [`i]) "*" `I)]))
        "*"
        `I))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_»
       («term_*_» (Term.app `R [`i]) "*" (Term.app `exp [(«term_*_» (Term.app `θ [`i]) "*" `I)]))
       "*"
       `I)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `I
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      («term_*_» (Term.app `R [`i]) "*" (Term.app `exp [(«term_*_» (Term.app `θ [`i]) "*" `I)]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `exp [(«term_*_» (Term.app `θ [`i]) "*" `I)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_*_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_*_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_» (Term.app `θ [`i]) "*" `I)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `I
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (Term.app `θ [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `θ
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1022, (some 1023, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_*_» (Term.app `θ [`i]) "*" `I)
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `exp
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (Term.app `R [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `R
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1022, (some 1023, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 70, (some 71, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 74 >? 1024, (none, [anonymous]) <=? (some 73, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 73, (some 73, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Icc
       [(Term.typeAscription
         "("
         (num "0")
         ":"
         [(MeasureTheory.Integral.TorusIntegral.«termℝⁿ» "ℝⁿ")]
         ")")
        (Term.fun
         "fun"
         (Term.basicFun
          [(Term.hole "_")]
          []
          "=>"
          («term_*_»
           (num "2")
           "*"
           (Real.Analysis.SpecialFunctions.Trigonometric.Basic.real.pi "π"))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [(Term.hole "_")]
        []
        "=>"
        («term_*_» (num "2") "*" (Real.Analysis.SpecialFunctions.Trigonometric.Basic.real.pi "π"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_» (num "2") "*" (Real.Analysis.SpecialFunctions.Trigonometric.Basic.real.pi "π"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Real.Analysis.SpecialFunctions.Trigonometric.Basic.real.pi "π")
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.typeAscription
       "("
       (num "0")
       ":"
       [(MeasureTheory.Integral.TorusIntegral.«termℝⁿ» "ℝⁿ")]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (MeasureTheory.Integral.TorusIntegral.«termℝⁿ» "ℝⁿ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'MeasureTheory.Integral.TorusIntegral.«termℝⁿ»', expected 'MeasureTheory.Integral.TorusIntegral.termℝⁿ._@.MeasureTheory.Integral.TorusIntegral._hyg.158'
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
    The definition of the integral over a generalized torus with center `c ∈ ℂⁿ` and radius `R ∈ ℝⁿ`
    as the `•`-product of the derivative of `torus_map` and `f (torus_map c R θ)`-/
  def
    torusIntegral
    ( f : ℂⁿ → E ) ( c : ℂⁿ ) ( R : ℝⁿ )
    :=
      ∫
        θ : ℝⁿ
        in
        Icc ( 0 : ℝⁿ ) fun _ => 2 * π
        ,
        ( ∏ i , R i * exp θ i * I * I : ℂ ) • f torusMap c R θ
#align torus_integral torusIntegral

-- mathport name: «expr∯ inT( , ), »
notation3"∯ "(...)" in ""T("c", "R")"", "r:(scoped f => torusIntegral f c R) => r

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `torus_integral_radius_zero [])
      (Command.declSig
       [(Term.explicitBinder "(" [`hn] [":" («term_≠_» `n "≠" (num "0"))] [] ")")
        (Term.explicitBinder
         "("
         [`f]
         [":" (Term.arrow (MeasureTheory.Integral.TorusIntegral.«termℂⁿ» "ℂⁿ") "→" `E)]
         []
         ")")
        (Term.explicitBinder
         "("
         [`c]
         [":" (MeasureTheory.Integral.TorusIntegral.«termℂⁿ» "ℂⁿ")]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (MeasureTheory.Integral.TorusIntegral.«term∯_inT(_,_),_»
          "∯"
          (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
          " in "
          "T("
          `c
          ", "
          (num "0")
          ")"
          ", "
          (Term.app `f [`x]))
         "="
         (num "0"))))
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
            ["["
             [(Tactic.simpLemma [] [] `torusIntegral)
              ","
              (Tactic.simpLemma [] [] `Pi.zero_apply)
              ","
              (Tactic.simpLemma [] [] `of_real_zero)
              ","
              (Tactic.simpLemma [] [] `mul_zero)
              ","
              (Tactic.simpLemma [] [] `zero_mul)
              ","
              (Tactic.simpLemma [] [] `Fin.prod_const)
              ","
              (Tactic.simpLemma [] [] (Term.app `zero_pow' [`n `hn]))
              ","
              (Tactic.simpLemma [] [] `zero_smul)
              ","
              (Tactic.simpLemma [] [] `integral_zero)]
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
           ["only"]
           ["["
            [(Tactic.simpLemma [] [] `torusIntegral)
             ","
             (Tactic.simpLemma [] [] `Pi.zero_apply)
             ","
             (Tactic.simpLemma [] [] `of_real_zero)
             ","
             (Tactic.simpLemma [] [] `mul_zero)
             ","
             (Tactic.simpLemma [] [] `zero_mul)
             ","
             (Tactic.simpLemma [] [] `Fin.prod_const)
             ","
             (Tactic.simpLemma [] [] (Term.app `zero_pow' [`n `hn]))
             ","
             (Tactic.simpLemma [] [] `zero_smul)
             ","
             (Tactic.simpLemma [] [] `integral_zero)]
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
        [(Tactic.simpLemma [] [] `torusIntegral)
         ","
         (Tactic.simpLemma [] [] `Pi.zero_apply)
         ","
         (Tactic.simpLemma [] [] `of_real_zero)
         ","
         (Tactic.simpLemma [] [] `mul_zero)
         ","
         (Tactic.simpLemma [] [] `zero_mul)
         ","
         (Tactic.simpLemma [] [] `Fin.prod_const)
         ","
         (Tactic.simpLemma [] [] (Term.app `zero_pow' [`n `hn]))
         ","
         (Tactic.simpLemma [] [] `zero_smul)
         ","
         (Tactic.simpLemma [] [] `integral_zero)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `integral_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `zero_smul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `zero_pow' [`n `hn])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hn
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `zero_pow'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Fin.prod_const
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `zero_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `of_real_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Pi.zero_apply
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `torusIntegral
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (MeasureTheory.Integral.TorusIntegral.«term∯_inT(_,_),_»
        "∯"
        (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
        " in "
        "T("
        `c
        ", "
        (num "0")
        ")"
        ", "
        (Term.app `f [`x]))
       "="
       (num "0"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (MeasureTheory.Integral.TorusIntegral.«term∯_inT(_,_),_»
       "∯"
       (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
       " in "
       "T("
       `c
       ", "
       (num "0")
       ")"
       ", "
       (Term.app `f [`x]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `f [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `c
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 0, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (MeasureTheory.Integral.TorusIntegral.«term∯_inT(_,_),_»
      "∯"
      (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
      " in "
      "T("
      `c
      ", "
      (num "0")
      ")"
      ", "
      (Term.app `f [`x]))
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (MeasureTheory.Integral.TorusIntegral.«termℂⁿ» "ℂⁿ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'MeasureTheory.Integral.TorusIntegral.«termℂⁿ»', expected 'MeasureTheory.Integral.TorusIntegral.termℂⁿ._@.MeasureTheory.Integral.TorusIntegral._hyg.195'
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
  torus_integral_radius_zero
  ( hn : n ≠ 0 ) ( f : ℂⁿ → E ) ( c : ℂⁿ ) : ∯ x in T( c , 0 ) , f x = 0
  :=
    by
      simp
        only
        [
          torusIntegral
            ,
            Pi.zero_apply
            ,
            of_real_zero
            ,
            mul_zero
            ,
            zero_mul
            ,
            Fin.prod_const
            ,
            zero_pow' n hn
            ,
            zero_smul
            ,
            integral_zero
          ]
#align torus_integral_radius_zero torus_integral_radius_zero

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `torus_integral_neg [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`f]
         [":" (Term.arrow (MeasureTheory.Integral.TorusIntegral.«termℂⁿ» "ℂⁿ") "→" `E)]
         []
         ")")
        (Term.explicitBinder
         "("
         [`c]
         [":" (MeasureTheory.Integral.TorusIntegral.«termℂⁿ» "ℂⁿ")]
         []
         ")")
        (Term.explicitBinder
         "("
         [`R]
         [":" (MeasureTheory.Integral.TorusIntegral.«termℝⁿ» "ℝⁿ")]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (MeasureTheory.Integral.TorusIntegral.«term∯_inT(_,_),_»
          "∯"
          (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
          " in "
          "T("
          `c
          ", "
          `R
          ")"
          ", "
          («term-_» "-" (Term.app `f [`x])))
         "="
         («term-_»
          "-"
          (MeasureTheory.Integral.TorusIntegral.«term∯_inT(_,_),_»
           "∯"
           (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
           " in "
           "T("
           `c
           ", "
           `R
           ")"
           ", "
           (Term.app `f [`x]))))))
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
             [(Tactic.simpLemma [] [] `torusIntegral) "," (Tactic.simpLemma [] [] `integral_neg)]
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
            [(Tactic.simpLemma [] [] `torusIntegral) "," (Tactic.simpLemma [] [] `integral_neg)]
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
        [(Tactic.simpLemma [] [] `torusIntegral) "," (Tactic.simpLemma [] [] `integral_neg)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `integral_neg
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `torusIntegral
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (MeasureTheory.Integral.TorusIntegral.«term∯_inT(_,_),_»
        "∯"
        (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
        " in "
        "T("
        `c
        ", "
        `R
        ")"
        ", "
        («term-_» "-" (Term.app `f [`x])))
       "="
       («term-_»
        "-"
        (MeasureTheory.Integral.TorusIntegral.«term∯_inT(_,_),_»
         "∯"
         (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
         " in "
         "T("
         `c
         ", "
         `R
         ")"
         ", "
         (Term.app `f [`x]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term-_»
       "-"
       (MeasureTheory.Integral.TorusIntegral.«term∯_inT(_,_),_»
        "∯"
        (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
        " in "
        "T("
        `c
        ", "
        `R
        ")"
        ", "
        (Term.app `f [`x])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (MeasureTheory.Integral.TorusIntegral.«term∯_inT(_,_),_»
       "∯"
       (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
       " in "
       "T("
       `c
       ", "
       `R
       ")"
       ", "
       (Term.app `f [`x]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `f [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `R
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `c
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 75 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 75, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (MeasureTheory.Integral.TorusIntegral.«term∯_inT(_,_),_»
       "∯"
       (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
       " in "
       "T("
       `c
       ", "
       `R
       ")"
       ", "
       («term-_» "-" (Term.app `f [`x])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term-_» "-" (Term.app `f [`x]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `f [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 75 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 75, (some 75, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `R
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `c
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 0, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (MeasureTheory.Integral.TorusIntegral.«term∯_inT(_,_),_»
      "∯"
      (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
      " in "
      "T("
      `c
      ", "
      `R
      ")"
      ", "
      («term-_» "-" (Term.app `f [`x])))
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 0, term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (MeasureTheory.Integral.TorusIntegral.«termℝⁿ» "ℝⁿ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'MeasureTheory.Integral.TorusIntegral.«termℝⁿ»', expected 'MeasureTheory.Integral.TorusIntegral.termℝⁿ._@.MeasureTheory.Integral.TorusIntegral._hyg.158'
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
  torus_integral_neg
  ( f : ℂⁿ → E ) ( c : ℂⁿ ) ( R : ℝⁿ ) : ∯ x in T( c , R ) , - f x = - ∯ x in T( c , R ) , f x
  := by simp [ torusIntegral , integral_neg ]
#align torus_integral_neg torus_integral_neg

theorem torus_integral_add (hf : TorusIntegrable f c R) (hg : TorusIntegrable g c R) :
    (∯ x in T(c, R), f x + g x) = (∯ x in T(c, R), f x) + ∯ x in T(c, R), g x := by
  simpa only [torusIntegral, smul_add, Pi.add_apply] using
    integral_add hf.function_integrable hg.function_integrable
#align torus_integral_add torus_integral_add

theorem torus_integral_sub (hf : TorusIntegrable f c R) (hg : TorusIntegrable g c R) :
    (∯ x in T(c, R), f x - g x) = (∯ x in T(c, R), f x) - ∯ x in T(c, R), g x := by
  simpa only [sub_eq_add_neg, ← torus_integral_neg] using torus_integral_add hf hg.neg
#align torus_integral_sub torus_integral_sub

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `torus_integral_smul [])
      (Command.declSig
       [(Term.implicitBinder "{" [`𝕜] [":" (Term.type "Type" [(Level.hole "_")])] "}")
        (Term.instBinder "[" [] (Term.app `IsROrC [`𝕜]) "]")
        (Term.instBinder "[" [] (Term.app `NormedSpace [`𝕜 `E]) "]")
        (Term.instBinder
         "["
         []
         (Term.app `SMulCommClass [`𝕜 (Data.Complex.Basic.termℂ "ℂ") `E])
         "]")
        (Term.explicitBinder "(" [`a] [":" `𝕜] [] ")")
        (Term.explicitBinder
         "("
         [`f]
         [":" (Term.arrow (MeasureTheory.Integral.TorusIntegral.«termℂⁿ» "ℂⁿ") "→" `E)]
         []
         ")")
        (Term.explicitBinder
         "("
         [`c]
         [":" (MeasureTheory.Integral.TorusIntegral.«termℂⁿ» "ℂⁿ")]
         []
         ")")
        (Term.explicitBinder
         "("
         [`R]
         [":" (MeasureTheory.Integral.TorusIntegral.«termℝⁿ» "ℝⁿ")]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (MeasureTheory.Integral.TorusIntegral.«term∯_inT(_,_),_»
          "∯"
          (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
          " in "
          "T("
          `c
          ", "
          `R
          ")"
          ", "
          (Algebra.Group.Defs.«term_•_» `a " • " (Term.app `f [`x])))
         "="
         (Algebra.Group.Defs.«term_•_»
          `a
          " • "
          (MeasureTheory.Integral.TorusIntegral.«term∯_inT(_,_),_»
           "∯"
           (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
           " in "
           "T("
           `c
           ", "
           `R
           ")"
           ", "
           (Term.app `f [`x]))))))
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
            ["["
             [(Tactic.simpLemma [] [] `torusIntegral)
              ","
              (Tactic.simpLemma [] [] `integral_smul)
              ","
              (Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] (Term.app `smul_comm [`a]))]
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
           ["only"]
           ["["
            [(Tactic.simpLemma [] [] `torusIntegral)
             ","
             (Tactic.simpLemma [] [] `integral_smul)
             ","
             (Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] (Term.app `smul_comm [`a]))]
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
        [(Tactic.simpLemma [] [] `torusIntegral)
         ","
         (Tactic.simpLemma [] [] `integral_smul)
         ","
         (Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] (Term.app `smul_comm [`a]))]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `smul_comm [`a])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `smul_comm
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `integral_smul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `torusIntegral
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (MeasureTheory.Integral.TorusIntegral.«term∯_inT(_,_),_»
        "∯"
        (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
        " in "
        "T("
        `c
        ", "
        `R
        ")"
        ", "
        (Algebra.Group.Defs.«term_•_» `a " • " (Term.app `f [`x])))
       "="
       (Algebra.Group.Defs.«term_•_»
        `a
        " • "
        (MeasureTheory.Integral.TorusIntegral.«term∯_inT(_,_),_»
         "∯"
         (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
         " in "
         "T("
         `c
         ", "
         `R
         ")"
         ", "
         (Term.app `f [`x]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Algebra.Group.Defs.«term_•_»
       `a
       " • "
       (MeasureTheory.Integral.TorusIntegral.«term∯_inT(_,_),_»
        "∯"
        (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
        " in "
        "T("
        `c
        ", "
        `R
        ")"
        ", "
        (Term.app `f [`x])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (MeasureTheory.Integral.TorusIntegral.«term∯_inT(_,_),_»
       "∯"
       (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
       " in "
       "T("
       `c
       ", "
       `R
       ")"
       ", "
       (Term.app `f [`x]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `f [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `R
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `c
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 73 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 73, term))
      `a
[PrettyPrinter.parenthesize] ...precedences are 74 >? 1024, (none, [anonymous]) <=? (some 73, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 73, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (MeasureTheory.Integral.TorusIntegral.«term∯_inT(_,_),_»
       "∯"
       (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
       " in "
       "T("
       `c
       ", "
       `R
       ")"
       ", "
       (Algebra.Group.Defs.«term_•_» `a " • " (Term.app `f [`x])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Algebra.Group.Defs.«term_•_» `a " • " (Term.app `f [`x]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `f [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 73 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 73, term))
      `a
[PrettyPrinter.parenthesize] ...precedences are 74 >? 1024, (none, [anonymous]) <=? (some 73, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 73, (some 73, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `R
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `c
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 0, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (MeasureTheory.Integral.TorusIntegral.«term∯_inT(_,_),_»
      "∯"
      (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
      " in "
      "T("
      `c
      ", "
      `R
      ")"
      ", "
      (Algebra.Group.Defs.«term_•_» `a " • " (Term.app `f [`x])))
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 0, term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (MeasureTheory.Integral.TorusIntegral.«termℝⁿ» "ℝⁿ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'MeasureTheory.Integral.TorusIntegral.«termℝⁿ»', expected 'MeasureTheory.Integral.TorusIntegral.termℝⁿ._@.MeasureTheory.Integral.TorusIntegral._hyg.158'
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
  torus_integral_smul
  { 𝕜 : Type _ }
      [ IsROrC 𝕜 ]
      [ NormedSpace 𝕜 E ]
      [ SMulCommClass 𝕜 ℂ E ]
      ( a : 𝕜 )
      ( f : ℂⁿ → E )
      ( c : ℂⁿ )
      ( R : ℝⁿ )
    : ∯ x in T( c , R ) , a • f x = a • ∯ x in T( c , R ) , f x
  := by simp only [ torusIntegral , integral_smul , ← smul_comm a ]
#align torus_integral_smul torus_integral_smul

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `torus_integral_const_mul [])
      (Command.declSig
       [(Term.explicitBinder "(" [`a] [":" (Data.Complex.Basic.termℂ "ℂ")] [] ")")
        (Term.explicitBinder
         "("
         [`f]
         [":"
          (Term.arrow
           (MeasureTheory.Integral.TorusIntegral.«termℂⁿ» "ℂⁿ")
           "→"
           (Data.Complex.Basic.termℂ "ℂ"))]
         []
         ")")
        (Term.explicitBinder
         "("
         [`c]
         [":" (MeasureTheory.Integral.TorusIntegral.«termℂⁿ» "ℂⁿ")]
         []
         ")")
        (Term.explicitBinder
         "("
         [`R]
         [":" (MeasureTheory.Integral.TorusIntegral.«termℝⁿ» "ℝⁿ")]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (MeasureTheory.Integral.TorusIntegral.«term∯_inT(_,_),_»
          "∯"
          (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
          " in "
          "T("
          `c
          ", "
          `R
          ")"
          ", "
          («term_*_» `a "*" (Term.app `f [`x])))
         "="
         («term_*_»
          `a
          "*"
          (MeasureTheory.Integral.TorusIntegral.«term∯_inT(_,_),_»
           "∯"
           (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
           " in "
           "T("
           `c
           ", "
           `R
           ")"
           ", "
           (Term.app `f [`x]))))))
      (Command.declValSimple ":=" (Term.app `torus_integral_smul [`a `f `c `R]) [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `torus_integral_smul [`a `f `c `R])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `R
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `c
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `torus_integral_smul
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (MeasureTheory.Integral.TorusIntegral.«term∯_inT(_,_),_»
        "∯"
        (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
        " in "
        "T("
        `c
        ", "
        `R
        ")"
        ", "
        («term_*_» `a "*" (Term.app `f [`x])))
       "="
       («term_*_»
        `a
        "*"
        (MeasureTheory.Integral.TorusIntegral.«term∯_inT(_,_),_»
         "∯"
         (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
         " in "
         "T("
         `c
         ", "
         `R
         ")"
         ", "
         (Term.app `f [`x]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_»
       `a
       "*"
       (MeasureTheory.Integral.TorusIntegral.«term∯_inT(_,_),_»
        "∯"
        (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
        " in "
        "T("
        `c
        ", "
        `R
        ")"
        ", "
        (Term.app `f [`x])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (MeasureTheory.Integral.TorusIntegral.«term∯_inT(_,_),_»
       "∯"
       (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
       " in "
       "T("
       `c
       ", "
       `R
       ")"
       ", "
       (Term.app `f [`x]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `f [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `R
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `c
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `a
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 70, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (MeasureTheory.Integral.TorusIntegral.«term∯_inT(_,_),_»
       "∯"
       (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
       " in "
       "T("
       `c
       ", "
       `R
       ")"
       ", "
       («term_*_» `a "*" (Term.app `f [`x])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_» `a "*" (Term.app `f [`x]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `f [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `a
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `R
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `c
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 0, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (MeasureTheory.Integral.TorusIntegral.«term∯_inT(_,_),_»
      "∯"
      (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
      " in "
      "T("
      `c
      ", "
      `R
      ")"
      ", "
      («term_*_» `a "*" (Term.app `f [`x])))
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 0, term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (MeasureTheory.Integral.TorusIntegral.«termℝⁿ» "ℝⁿ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'MeasureTheory.Integral.TorusIntegral.«termℝⁿ»', expected 'MeasureTheory.Integral.TorusIntegral.termℝⁿ._@.MeasureTheory.Integral.TorusIntegral._hyg.158'
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
  torus_integral_const_mul
  ( a : ℂ ) ( f : ℂⁿ → ℂ ) ( c : ℂⁿ ) ( R : ℝⁿ )
    : ∯ x in T( c , R ) , a * f x = a * ∯ x in T( c , R ) , f x
  := torus_integral_smul a f c R
#align torus_integral_const_mul torus_integral_const_mul

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "If for all `θ : ℝⁿ`, `‖f (torus_map c R θ)‖` is less than or equal to a constant `C : ℝ`, then\n`‖∯ x in T(c, R), f x‖` is less than or equal to `(2 * π)^n * (∏ i, |R i|) * C`-/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `norm_torus_integral_le_of_norm_le_const [])
      (Command.declSig
       [(Term.implicitBinder "{" [`C] [":" (Data.Real.Basic.termℝ "ℝ")] "}")
        (Term.explicitBinder
         "("
         [`hf]
         [":"
          (Term.forall
           "∀"
           [`θ]
           []
           ","
           («term_≤_»
            (Analysis.Normed.Group.Basic.«term‖_‖»
             "‖"
             (Term.app `f [(Term.app `torusMap [`c `R `θ])])
             "‖")
            "≤"
            `C))]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_≤_»
         (Analysis.Normed.Group.Basic.«term‖_‖»
          "‖"
          (MeasureTheory.Integral.TorusIntegral.«term∯_inT(_,_),_»
           "∯"
           (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
           " in "
           "T("
           `c
           ", "
           `R
           ")"
           ", "
           (Term.app `f [`x]))
          "‖")
         "≤"
         («term_*_»
          («term_*_»
           («term_^_»
            («term_*_»
             (num "2")
             "*"
             (Real.Analysis.SpecialFunctions.Trigonometric.Basic.real.pi "π"))
            "^"
            (Term.typeAscription "(" `n ":" [(termℕ "ℕ")] ")"))
           "*"
           (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
            "∏"
            (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
            ", "
            («term|___|» (group "|") (Term.app `R [`i]) (group) "|")))
          "*"
          `C))))
      (Command.declValSimple
       ":="
       (calc
        "calc"
        (calcStep
         («term_≤_»
          (Analysis.Normed.Group.Basic.«term‖_‖»
           "‖"
           (MeasureTheory.Integral.TorusIntegral.«term∯_inT(_,_),_»
            "∯"
            (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
            " in "
            "T("
            `c
            ", "
            `R
            ")"
            ", "
            (Term.app `f [`x]))
           "‖")
          "≤"
          («term_*_»
           («term_*_»
            (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
             "∏"
             (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
             ", "
             («term|___|» (group "|") (Term.app `R [`i]) (group) "|"))
            "*"
            `C)
           "*"
           (Term.proj
            (Term.app
             `volume
             [(Term.app
               `Icc
               [(Term.typeAscription
                 "("
                 (num "0")
                 ":"
                 [(MeasureTheory.Integral.TorusIntegral.«termℝⁿ» "ℝⁿ")]
                 ")")
                (Term.fun
                 "fun"
                 (Term.basicFun
                  [(Term.hole "_")]
                  []
                  "=>"
                  («term_*_»
                   (num "2")
                   "*"
                   (Real.Analysis.SpecialFunctions.Trigonometric.Basic.real.pi "π"))))])])
            "."
            `toReal)))
         ":="
         (Term.app
          (Term.app
           `norm_set_integral_le_of_norm_le_const'
           [`measure_Icc_lt_top `measurable_set_Icc])
          [(Term.fun
            "fun"
            (Term.basicFun
             [`θ `hθ]
             []
             "=>"
             (calc
              "calc"
              (calcStep
               («term_=_»
                (Analysis.Normed.Group.Basic.«term‖_‖»
                 "‖"
                 (Algebra.Group.Defs.«term_•_»
                  (Term.typeAscription
                   "("
                   (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
                    "∏"
                    (Std.ExtendedBinder.extBinders
                     (Std.ExtendedBinder.extBinder
                      (Lean.binderIdent `i)
                      [(group ":" (Term.app `Fin [`n]))]))
                    ", "
                    («term_*_»
                     («term_*_»
                      (Term.app `R [`i])
                      "*"
                      (Term.app `exp [(«term_*_» (Term.app `θ [`i]) "*" `I)]))
                     "*"
                     `I))
                   ":"
                   [(Data.Complex.Basic.termℂ "ℂ")]
                   ")")
                  " • "
                  (Term.app `f [(Term.app `torusMap [`c `R `θ])]))
                 "‖")
                "="
                («term_*_»
                 (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
                  "∏"
                  (Std.ExtendedBinder.extBinders
                   (Std.ExtendedBinder.extBinder
                    (Lean.binderIdent `i)
                    [(group ":" (Term.app `Fin [`n]))]))
                  ", "
                  («term|___|» (group "|") (Term.app `R [`i]) (group) "|"))
                 "*"
                 (Analysis.Normed.Group.Basic.«term‖_‖»
                  "‖"
                  (Term.app `f [(Term.app `torusMap [`c `R `θ])])
                  "‖")))
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
                    ["[" [(Tactic.simpLemma [] [] `norm_smul)] "]"]
                    [])]))))
              [(calcStep
                («term_≤_»
                 (Term.hole "_")
                 "≤"
                 («term_*_»
                  (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
                   "∏"
                   (Std.ExtendedBinder.extBinders
                    (Std.ExtendedBinder.extBinder
                     (Lean.binderIdent `i)
                     [(group ":" (Term.app `Fin [`n]))]))
                   ", "
                   («term|___|» (group "|") (Term.app `R [`i]) (group) "|"))
                  "*"
                  `C))
                ":="
                (Term.app
                 `mul_le_mul_of_nonneg_left
                 [(Term.app `hf [(Term.hole "_")])
                  (Term.app
                   `Finset.prod_nonneg
                   [(Term.fun
                     "fun"
                     (Term.basicFun
                      [(Term.hole "_") (Term.hole "_")]
                      []
                      "=>"
                      (Term.app `abs_nonneg [(Term.hole "_")])))])]))])))]))
        [(calcStep
          («term_=_»
           (Term.hole "_")
           "="
           («term_*_»
            («term_*_»
             («term_^_»
              («term_*_»
               (num "2")
               "*"
               (Real.Analysis.SpecialFunctions.Trigonometric.Basic.real.pi "π"))
              "^"
              (Term.typeAscription "(" `n ":" [(termℕ "ℕ")] ")"))
             "*"
             (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
              "∏"
              (Std.ExtendedBinder.extBinders
               (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
              ", "
              («term|___|» (group "|") (Term.app `R [`i]) (group) "|")))
            "*"
            `C))
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
                [(Tactic.simpLemma [] [] `Pi.zero_def)
                 ","
                 (Tactic.simpLemma
                  []
                  []
                  (Term.app
                   `Real.volume_Icc_pi_to_real
                   [(Term.fun
                     "fun"
                     (Term.basicFun [(Term.hole "_")] [] "=>" `real.two_pi_pos.le))]))
                 ","
                 (Tactic.simpLemma [] [] `sub_zero)
                 ","
                 (Tactic.simpLemma [] [] `Fin.prod_const)
                 ","
                 (Tactic.simpLemma [] [] `mul_assoc)
                 ","
                 (Tactic.simpLemma
                  []
                  []
                  (Term.app
                   `mul_comm
                   [(«term_^_»
                     («term_*_»
                      (num "2")
                      "*"
                      (Real.Analysis.SpecialFunctions.Trigonometric.Basic.real.pi "π"))
                     "^"
                     (Term.typeAscription "(" `n ":" [(termℕ "ℕ")] ")"))]))]
                "]"]
               [])]))))])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (calc
       "calc"
       (calcStep
        («term_≤_»
         (Analysis.Normed.Group.Basic.«term‖_‖»
          "‖"
          (MeasureTheory.Integral.TorusIntegral.«term∯_inT(_,_),_»
           "∯"
           (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
           " in "
           "T("
           `c
           ", "
           `R
           ")"
           ", "
           (Term.app `f [`x]))
          "‖")
         "≤"
         («term_*_»
          («term_*_»
           (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
            "∏"
            (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
            ", "
            («term|___|» (group "|") (Term.app `R [`i]) (group) "|"))
           "*"
           `C)
          "*"
          (Term.proj
           (Term.app
            `volume
            [(Term.app
              `Icc
              [(Term.typeAscription
                "("
                (num "0")
                ":"
                [(MeasureTheory.Integral.TorusIntegral.«termℝⁿ» "ℝⁿ")]
                ")")
               (Term.fun
                "fun"
                (Term.basicFun
                 [(Term.hole "_")]
                 []
                 "=>"
                 («term_*_»
                  (num "2")
                  "*"
                  (Real.Analysis.SpecialFunctions.Trigonometric.Basic.real.pi "π"))))])])
           "."
           `toReal)))
        ":="
        (Term.app
         (Term.app
          `norm_set_integral_le_of_norm_le_const'
          [`measure_Icc_lt_top `measurable_set_Icc])
         [(Term.fun
           "fun"
           (Term.basicFun
            [`θ `hθ]
            []
            "=>"
            (calc
             "calc"
             (calcStep
              («term_=_»
               (Analysis.Normed.Group.Basic.«term‖_‖»
                "‖"
                (Algebra.Group.Defs.«term_•_»
                 (Term.typeAscription
                  "("
                  (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
                   "∏"
                   (Std.ExtendedBinder.extBinders
                    (Std.ExtendedBinder.extBinder
                     (Lean.binderIdent `i)
                     [(group ":" (Term.app `Fin [`n]))]))
                   ", "
                   («term_*_»
                    («term_*_»
                     (Term.app `R [`i])
                     "*"
                     (Term.app `exp [(«term_*_» (Term.app `θ [`i]) "*" `I)]))
                    "*"
                    `I))
                  ":"
                  [(Data.Complex.Basic.termℂ "ℂ")]
                  ")")
                 " • "
                 (Term.app `f [(Term.app `torusMap [`c `R `θ])]))
                "‖")
               "="
               («term_*_»
                (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
                 "∏"
                 (Std.ExtendedBinder.extBinders
                  (Std.ExtendedBinder.extBinder
                   (Lean.binderIdent `i)
                   [(group ":" (Term.app `Fin [`n]))]))
                 ", "
                 («term|___|» (group "|") (Term.app `R [`i]) (group) "|"))
                "*"
                (Analysis.Normed.Group.Basic.«term‖_‖»
                 "‖"
                 (Term.app `f [(Term.app `torusMap [`c `R `θ])])
                 "‖")))
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
                   ["[" [(Tactic.simpLemma [] [] `norm_smul)] "]"]
                   [])]))))
             [(calcStep
               («term_≤_»
                (Term.hole "_")
                "≤"
                («term_*_»
                 (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
                  "∏"
                  (Std.ExtendedBinder.extBinders
                   (Std.ExtendedBinder.extBinder
                    (Lean.binderIdent `i)
                    [(group ":" (Term.app `Fin [`n]))]))
                  ", "
                  («term|___|» (group "|") (Term.app `R [`i]) (group) "|"))
                 "*"
                 `C))
               ":="
               (Term.app
                `mul_le_mul_of_nonneg_left
                [(Term.app `hf [(Term.hole "_")])
                 (Term.app
                  `Finset.prod_nonneg
                  [(Term.fun
                    "fun"
                    (Term.basicFun
                     [(Term.hole "_") (Term.hole "_")]
                     []
                     "=>"
                     (Term.app `abs_nonneg [(Term.hole "_")])))])]))])))]))
       [(calcStep
         («term_=_»
          (Term.hole "_")
          "="
          («term_*_»
           («term_*_»
            («term_^_»
             («term_*_»
              (num "2")
              "*"
              (Real.Analysis.SpecialFunctions.Trigonometric.Basic.real.pi "π"))
             "^"
             (Term.typeAscription "(" `n ":" [(termℕ "ℕ")] ")"))
            "*"
            (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
             "∏"
             (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
             ", "
             («term|___|» (group "|") (Term.app `R [`i]) (group) "|")))
           "*"
           `C))
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
               [(Tactic.simpLemma [] [] `Pi.zero_def)
                ","
                (Tactic.simpLemma
                 []
                 []
                 (Term.app
                  `Real.volume_Icc_pi_to_real
                  [(Term.fun "fun" (Term.basicFun [(Term.hole "_")] [] "=>" `real.two_pi_pos.le))]))
                ","
                (Tactic.simpLemma [] [] `sub_zero)
                ","
                (Tactic.simpLemma [] [] `Fin.prod_const)
                ","
                (Tactic.simpLemma [] [] `mul_assoc)
                ","
                (Tactic.simpLemma
                 []
                 []
                 (Term.app
                  `mul_comm
                  [(«term_^_»
                    («term_*_»
                     (num "2")
                     "*"
                     (Real.Analysis.SpecialFunctions.Trigonometric.Basic.real.pi "π"))
                    "^"
                    (Term.typeAscription "(" `n ":" [(termℕ "ℕ")] ")"))]))]
               "]"]
              [])]))))])
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
            [(Tactic.simpLemma [] [] `Pi.zero_def)
             ","
             (Tactic.simpLemma
              []
              []
              (Term.app
               `Real.volume_Icc_pi_to_real
               [(Term.fun "fun" (Term.basicFun [(Term.hole "_")] [] "=>" `real.two_pi_pos.le))]))
             ","
             (Tactic.simpLemma [] [] `sub_zero)
             ","
             (Tactic.simpLemma [] [] `Fin.prod_const)
             ","
             (Tactic.simpLemma [] [] `mul_assoc)
             ","
             (Tactic.simpLemma
              []
              []
              (Term.app
               `mul_comm
               [(«term_^_»
                 («term_*_»
                  (num "2")
                  "*"
                  (Real.Analysis.SpecialFunctions.Trigonometric.Basic.real.pi "π"))
                 "^"
                 (Term.typeAscription "(" `n ":" [(termℕ "ℕ")] ")"))]))]
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
        [(Tactic.simpLemma [] [] `Pi.zero_def)
         ","
         (Tactic.simpLemma
          []
          []
          (Term.app
           `Real.volume_Icc_pi_to_real
           [(Term.fun "fun" (Term.basicFun [(Term.hole "_")] [] "=>" `real.two_pi_pos.le))]))
         ","
         (Tactic.simpLemma [] [] `sub_zero)
         ","
         (Tactic.simpLemma [] [] `Fin.prod_const)
         ","
         (Tactic.simpLemma [] [] `mul_assoc)
         ","
         (Tactic.simpLemma
          []
          []
          (Term.app
           `mul_comm
           [(«term_^_»
             («term_*_»
              (num "2")
              "*"
              (Real.Analysis.SpecialFunctions.Trigonometric.Basic.real.pi "π"))
             "^"
             (Term.typeAscription "(" `n ":" [(termℕ "ℕ")] ")"))]))]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `mul_comm
       [(«term_^_»
         («term_*_» (num "2") "*" (Real.Analysis.SpecialFunctions.Trigonometric.Basic.real.pi "π"))
         "^"
         (Term.typeAscription "(" `n ":" [(termℕ "ℕ")] ")"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_^_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_^_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_»
       («term_*_» (num "2") "*" (Real.Analysis.SpecialFunctions.Trigonometric.Basic.real.pi "π"))
       "^"
       (Term.typeAscription "(" `n ":" [(termℕ "ℕ")] ")"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription "(" `n ":" [(termℕ "ℕ")] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (termℕ "ℕ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      («term_*_» (num "2") "*" (Real.Analysis.SpecialFunctions.Trigonometric.Basic.real.pi "π"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Real.Analysis.SpecialFunctions.Trigonometric.Basic.real.pi "π")
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 70, (some 71, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_*_» (num "2") "*" (Real.Analysis.SpecialFunctions.Trigonometric.Basic.real.pi "π"))
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_^_»
      (Term.paren
       "("
       («term_*_» (num "2") "*" (Real.Analysis.SpecialFunctions.Trigonometric.Basic.real.pi "π"))
       ")")
      "^"
      (Term.typeAscription "(" `n ":" [(termℕ "ℕ")] ")"))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `mul_comm
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_assoc
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Fin.prod_const
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `sub_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Real.volume_Icc_pi_to_real
       [(Term.fun "fun" (Term.basicFun [(Term.hole "_")] [] "=>" `real.two_pi_pos.le))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun "fun" (Term.basicFun [(Term.hole "_")] [] "=>" `real.two_pi_pos.le))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `real.two_pi_pos.le
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
      `Real.volume_Icc_pi_to_real
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Pi.zero_def
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Term.hole "_")
       "="
       («term_*_»
        («term_*_»
         («term_^_»
          («term_*_» (num "2") "*" (Real.Analysis.SpecialFunctions.Trigonometric.Basic.real.pi "π"))
          "^"
          (Term.typeAscription "(" `n ":" [(termℕ "ℕ")] ")"))
         "*"
         (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
          "∏"
          (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
          ", "
          («term|___|» (group "|") (Term.app `R [`i]) (group) "|")))
        "*"
        `C))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_»
       («term_*_»
        («term_^_»
         («term_*_» (num "2") "*" (Real.Analysis.SpecialFunctions.Trigonometric.Basic.real.pi "π"))
         "^"
         (Term.typeAscription "(" `n ":" [(termℕ "ℕ")] ")"))
        "*"
        (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
         "∏"
         (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
         ", "
         («term|___|» (group "|") (Term.app `R [`i]) (group) "|")))
       "*"
       `C)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `C
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      («term_*_»
       («term_^_»
        («term_*_» (num "2") "*" (Real.Analysis.SpecialFunctions.Trigonometric.Basic.real.pi "π"))
        "^"
        (Term.typeAscription "(" `n ":" [(termℕ "ℕ")] ")"))
       "*"
       (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
        "∏"
        (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
        ", "
        («term|___|» (group "|") (Term.app `R [`i]) (group) "|")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
       "∏"
       (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
       ", "
       («term|___|» (group "|") (Term.app `R [`i]) (group) "|"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term|___|» (group "|") (Term.app `R [`i]) (group) "|")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `R [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `R
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      («term_^_»
       («term_*_» (num "2") "*" (Real.Analysis.SpecialFunctions.Trigonometric.Basic.real.pi "π"))
       "^"
       (Term.typeAscription "(" `n ":" [(termℕ "ℕ")] ")"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription "(" `n ":" [(termℕ "ℕ")] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (termℕ "ℕ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      («term_*_» (num "2") "*" (Real.Analysis.SpecialFunctions.Trigonometric.Basic.real.pi "π"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Real.Analysis.SpecialFunctions.Trigonometric.Basic.real.pi "π")
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 70, (some 71, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_*_» (num "2") "*" (Real.Analysis.SpecialFunctions.Trigonometric.Basic.real.pi "π"))
     ")")
[PrettyPrinter.parenthesize] ...precedences are 70 >? 80, (some 80, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 70, (some 0, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_*_»
      («term_^_»
       (Term.paren
        "("
        («term_*_» (num "2") "*" (Real.Analysis.SpecialFunctions.Trigonometric.Basic.real.pi "π"))
        ")")
       "^"
       (Term.typeAscription "(" `n ":" [(termℕ "ℕ")] ")"))
      "*"
      (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
       "∏"
       (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
       ", "
       («term|___|» (group "|") (Term.app `R [`i]) (group) "|")))
     ")")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
      (Term.app
       (Term.app `norm_set_integral_le_of_norm_le_const' [`measure_Icc_lt_top `measurable_set_Icc])
       [(Term.fun
         "fun"
         (Term.basicFun
          [`θ `hθ]
          []
          "=>"
          (calc
           "calc"
           (calcStep
            («term_=_»
             (Analysis.Normed.Group.Basic.«term‖_‖»
              "‖"
              (Algebra.Group.Defs.«term_•_»
               (Term.typeAscription
                "("
                (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
                 "∏"
                 (Std.ExtendedBinder.extBinders
                  (Std.ExtendedBinder.extBinder
                   (Lean.binderIdent `i)
                   [(group ":" (Term.app `Fin [`n]))]))
                 ", "
                 («term_*_»
                  («term_*_»
                   (Term.app `R [`i])
                   "*"
                   (Term.app `exp [(«term_*_» (Term.app `θ [`i]) "*" `I)]))
                  "*"
                  `I))
                ":"
                [(Data.Complex.Basic.termℂ "ℂ")]
                ")")
               " • "
               (Term.app `f [(Term.app `torusMap [`c `R `θ])]))
              "‖")
             "="
             («term_*_»
              (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
               "∏"
               (Std.ExtendedBinder.extBinders
                (Std.ExtendedBinder.extBinder
                 (Lean.binderIdent `i)
                 [(group ":" (Term.app `Fin [`n]))]))
               ", "
               («term|___|» (group "|") (Term.app `R [`i]) (group) "|"))
              "*"
              (Analysis.Normed.Group.Basic.«term‖_‖»
               "‖"
               (Term.app `f [(Term.app `torusMap [`c `R `θ])])
               "‖")))
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
                 ["[" [(Tactic.simpLemma [] [] `norm_smul)] "]"]
                 [])]))))
           [(calcStep
             («term_≤_»
              (Term.hole "_")
              "≤"
              («term_*_»
               (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
                "∏"
                (Std.ExtendedBinder.extBinders
                 (Std.ExtendedBinder.extBinder
                  (Lean.binderIdent `i)
                  [(group ":" (Term.app `Fin [`n]))]))
                ", "
                («term|___|» (group "|") (Term.app `R [`i]) (group) "|"))
               "*"
               `C))
             ":="
             (Term.app
              `mul_le_mul_of_nonneg_left
              [(Term.app `hf [(Term.hole "_")])
               (Term.app
                `Finset.prod_nonneg
                [(Term.fun
                  "fun"
                  (Term.basicFun
                   [(Term.hole "_") (Term.hole "_")]
                   []
                   "=>"
                   (Term.app `abs_nonneg [(Term.hole "_")])))])]))])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`θ `hθ]
        []
        "=>"
        (calc
         "calc"
         (calcStep
          («term_=_»
           (Analysis.Normed.Group.Basic.«term‖_‖»
            "‖"
            (Algebra.Group.Defs.«term_•_»
             (Term.typeAscription
              "("
              (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
               "∏"
               (Std.ExtendedBinder.extBinders
                (Std.ExtendedBinder.extBinder
                 (Lean.binderIdent `i)
                 [(group ":" (Term.app `Fin [`n]))]))
               ", "
               («term_*_»
                («term_*_»
                 (Term.app `R [`i])
                 "*"
                 (Term.app `exp [(«term_*_» (Term.app `θ [`i]) "*" `I)]))
                "*"
                `I))
              ":"
              [(Data.Complex.Basic.termℂ "ℂ")]
              ")")
             " • "
             (Term.app `f [(Term.app `torusMap [`c `R `θ])]))
            "‖")
           "="
           («term_*_»
            (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
             "∏"
             (Std.ExtendedBinder.extBinders
              (Std.ExtendedBinder.extBinder
               (Lean.binderIdent `i)
               [(group ":" (Term.app `Fin [`n]))]))
             ", "
             («term|___|» (group "|") (Term.app `R [`i]) (group) "|"))
            "*"
            (Analysis.Normed.Group.Basic.«term‖_‖»
             "‖"
             (Term.app `f [(Term.app `torusMap [`c `R `θ])])
             "‖")))
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `norm_smul)] "]"] [])]))))
         [(calcStep
           («term_≤_»
            (Term.hole "_")
            "≤"
            («term_*_»
             (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
              "∏"
              (Std.ExtendedBinder.extBinders
               (Std.ExtendedBinder.extBinder
                (Lean.binderIdent `i)
                [(group ":" (Term.app `Fin [`n]))]))
              ", "
              («term|___|» (group "|") (Term.app `R [`i]) (group) "|"))
             "*"
             `C))
           ":="
           (Term.app
            `mul_le_mul_of_nonneg_left
            [(Term.app `hf [(Term.hole "_")])
             (Term.app
              `Finset.prod_nonneg
              [(Term.fun
                "fun"
                (Term.basicFun
                 [(Term.hole "_") (Term.hole "_")]
                 []
                 "=>"
                 (Term.app `abs_nonneg [(Term.hole "_")])))])]))])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (calc
       "calc"
       (calcStep
        («term_=_»
         (Analysis.Normed.Group.Basic.«term‖_‖»
          "‖"
          (Algebra.Group.Defs.«term_•_»
           (Term.typeAscription
            "("
            (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
             "∏"
             (Std.ExtendedBinder.extBinders
              (Std.ExtendedBinder.extBinder
               (Lean.binderIdent `i)
               [(group ":" (Term.app `Fin [`n]))]))
             ", "
             («term_*_»
              («term_*_»
               (Term.app `R [`i])
               "*"
               (Term.app `exp [(«term_*_» (Term.app `θ [`i]) "*" `I)]))
              "*"
              `I))
            ":"
            [(Data.Complex.Basic.termℂ "ℂ")]
            ")")
           " • "
           (Term.app `f [(Term.app `torusMap [`c `R `θ])]))
          "‖")
         "="
         («term_*_»
          (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
           "∏"
           (Std.ExtendedBinder.extBinders
            (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) [(group ":" (Term.app `Fin [`n]))]))
           ", "
           («term|___|» (group "|") (Term.app `R [`i]) (group) "|"))
          "*"
          (Analysis.Normed.Group.Basic.«term‖_‖»
           "‖"
           (Term.app `f [(Term.app `torusMap [`c `R `θ])])
           "‖")))
        ":="
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `norm_smul)] "]"] [])]))))
       [(calcStep
         («term_≤_»
          (Term.hole "_")
          "≤"
          («term_*_»
           (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
            "∏"
            (Std.ExtendedBinder.extBinders
             (Std.ExtendedBinder.extBinder
              (Lean.binderIdent `i)
              [(group ":" (Term.app `Fin [`n]))]))
            ", "
            («term|___|» (group "|") (Term.app `R [`i]) (group) "|"))
           "*"
           `C))
         ":="
         (Term.app
          `mul_le_mul_of_nonneg_left
          [(Term.app `hf [(Term.hole "_")])
           (Term.app
            `Finset.prod_nonneg
            [(Term.fun
              "fun"
              (Term.basicFun
               [(Term.hole "_") (Term.hole "_")]
               []
               "=>"
               (Term.app `abs_nonneg [(Term.hole "_")])))])]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `mul_le_mul_of_nonneg_left
       [(Term.app `hf [(Term.hole "_")])
        (Term.app
         `Finset.prod_nonneg
         [(Term.fun
           "fun"
           (Term.basicFun
            [(Term.hole "_") (Term.hole "_")]
            []
            "=>"
            (Term.app `abs_nonneg [(Term.hole "_")])))])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Finset.prod_nonneg
       [(Term.fun
         "fun"
         (Term.basicFun
          [(Term.hole "_") (Term.hole "_")]
          []
          "=>"
          (Term.app `abs_nonneg [(Term.hole "_")])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [(Term.hole "_") (Term.hole "_")]
        []
        "=>"
        (Term.app `abs_nonneg [(Term.hole "_")])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `abs_nonneg [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `abs_nonneg
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Finset.prod_nonneg
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `Finset.prod_nonneg
      [(Term.fun
        "fun"
        (Term.basicFun
         [(Term.hole "_") (Term.hole "_")]
         []
         "=>"
         (Term.app `abs_nonneg [(Term.hole "_")])))])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `hf [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `hf
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `hf [(Term.hole "_")]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `mul_le_mul_of_nonneg_left
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≤_»
       (Term.hole "_")
       "≤"
       («term_*_»
        (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
         "∏"
         (Std.ExtendedBinder.extBinders
          (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) [(group ":" (Term.app `Fin [`n]))]))
         ", "
         («term|___|» (group "|") (Term.app `R [`i]) (group) "|"))
        "*"
        `C))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_»
       (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
        "∏"
        (Std.ExtendedBinder.extBinders
         (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) [(group ":" (Term.app `Fin [`n]))]))
        ", "
        («term|___|» (group "|") (Term.app `R [`i]) (group) "|"))
       "*"
       `C)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `C
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
       "∏"
       (Std.ExtendedBinder.extBinders
        (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) [(group ":" (Term.app `Fin [`n]))]))
       ", "
       («term|___|» (group "|") (Term.app `R [`i]) (group) "|"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term|___|» (group "|") (Term.app `R [`i]) (group) "|")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `R [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `R
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Fin [`n])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Fin
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1022, (some 0, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
      "∏"
      (Std.ExtendedBinder.extBinders
       (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) [(group ":" (Term.app `Fin [`n]))]))
      ", "
      («term|___|» (group "|") (Term.app `R [`i]) (group) "|"))
     ")")
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
         [(Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `norm_smul)] "]"] [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `norm_smul)] "]"] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `norm_smul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Analysis.Normed.Group.Basic.«term‖_‖»
        "‖"
        (Algebra.Group.Defs.«term_•_»
         (Term.typeAscription
          "("
          (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
           "∏"
           (Std.ExtendedBinder.extBinders
            (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) [(group ":" (Term.app `Fin [`n]))]))
           ", "
           («term_*_»
            («term_*_»
             (Term.app `R [`i])
             "*"
             (Term.app `exp [(«term_*_» (Term.app `θ [`i]) "*" `I)]))
            "*"
            `I))
          ":"
          [(Data.Complex.Basic.termℂ "ℂ")]
          ")")
         " • "
         (Term.app `f [(Term.app `torusMap [`c `R `θ])]))
        "‖")
       "="
       («term_*_»
        (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
         "∏"
         (Std.ExtendedBinder.extBinders
          (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) [(group ":" (Term.app `Fin [`n]))]))
         ", "
         («term|___|» (group "|") (Term.app `R [`i]) (group) "|"))
        "*"
        (Analysis.Normed.Group.Basic.«term‖_‖»
         "‖"
         (Term.app `f [(Term.app `torusMap [`c `R `θ])])
         "‖")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_»
       (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
        "∏"
        (Std.ExtendedBinder.extBinders
         (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) [(group ":" (Term.app `Fin [`n]))]))
        ", "
        («term|___|» (group "|") (Term.app `R [`i]) (group) "|"))
       "*"
       (Analysis.Normed.Group.Basic.«term‖_‖»
        "‖"
        (Term.app `f [(Term.app `torusMap [`c `R `θ])])
        "‖"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.Normed.Group.Basic.«term‖_‖»
       "‖"
       (Term.app `f [(Term.app `torusMap [`c `R `θ])])
       "‖")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `f [(Term.app `torusMap [`c `R `θ])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `torusMap [`c `R `θ])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `θ
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `R
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `c
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `torusMap
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `torusMap [`c `R `θ]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
       "∏"
       (Std.ExtendedBinder.extBinders
        (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) [(group ":" (Term.app `Fin [`n]))]))
       ", "
       («term|___|» (group "|") (Term.app `R [`i]) (group) "|"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term|___|» (group "|") (Term.app `R [`i]) (group) "|")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `R [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `R
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Fin [`n])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Fin
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1022, (some 0, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
      "∏"
      (Std.ExtendedBinder.extBinders
       (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) [(group ":" (Term.app `Fin [`n]))]))
      ", "
      («term|___|» (group "|") (Term.app `R [`i]) (group) "|"))
     ")")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Analysis.Normed.Group.Basic.«term‖_‖»
       "‖"
       (Algebra.Group.Defs.«term_•_»
        (Term.typeAscription
         "("
         (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
          "∏"
          (Std.ExtendedBinder.extBinders
           (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) [(group ":" (Term.app `Fin [`n]))]))
          ", "
          («term_*_»
           («term_*_»
            (Term.app `R [`i])
            "*"
            (Term.app `exp [(«term_*_» (Term.app `θ [`i]) "*" `I)]))
           "*"
           `I))
         ":"
         [(Data.Complex.Basic.termℂ "ℂ")]
         ")")
        " • "
        (Term.app `f [(Term.app `torusMap [`c `R `θ])]))
       "‖")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Algebra.Group.Defs.«term_•_»
       (Term.typeAscription
        "("
        (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
         "∏"
         (Std.ExtendedBinder.extBinders
          (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) [(group ":" (Term.app `Fin [`n]))]))
         ", "
         («term_*_»
          («term_*_» (Term.app `R [`i]) "*" (Term.app `exp [(«term_*_» (Term.app `θ [`i]) "*" `I)]))
          "*"
          `I))
        ":"
        [(Data.Complex.Basic.termℂ "ℂ")]
        ")")
       " • "
       (Term.app `f [(Term.app `torusMap [`c `R `θ])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `f [(Term.app `torusMap [`c `R `θ])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `torusMap [`c `R `θ])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `θ
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `R
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `c
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `torusMap
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `torusMap [`c `R `θ]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 73 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 73, term))
      (Term.typeAscription
       "("
       (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
        "∏"
        (Std.ExtendedBinder.extBinders
         (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) [(group ":" (Term.app `Fin [`n]))]))
        ", "
        («term_*_»
         («term_*_» (Term.app `R [`i]) "*" (Term.app `exp [(«term_*_» (Term.app `θ [`i]) "*" `I)]))
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
      (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
       "∏"
       (Std.ExtendedBinder.extBinders
        (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) [(group ":" (Term.app `Fin [`n]))]))
       ", "
       («term_*_»
        («term_*_» (Term.app `R [`i]) "*" (Term.app `exp [(«term_*_» (Term.app `θ [`i]) "*" `I)]))
        "*"
        `I))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_»
       («term_*_» (Term.app `R [`i]) "*" (Term.app `exp [(«term_*_» (Term.app `θ [`i]) "*" `I)]))
       "*"
       `I)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `I
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      («term_*_» (Term.app `R [`i]) "*" (Term.app `exp [(«term_*_» (Term.app `θ [`i]) "*" `I)]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `exp [(«term_*_» (Term.app `θ [`i]) "*" `I)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_*_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_*_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_» (Term.app `θ [`i]) "*" `I)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `I
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (Term.app `θ [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `θ
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1022, (some 1023, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_*_» (Term.app `θ [`i]) "*" `I)
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `exp
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (Term.app `R [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `R
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1022, (some 1023, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 70, (some 71, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Fin [`n])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Fin
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 74 >? 1024, (none, [anonymous]) <=? (some 73, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 73, (some 73, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hθ
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `θ
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.app `norm_set_integral_le_of_norm_le_const' [`measure_Icc_lt_top `measurable_set_Icc])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `measurable_set_Icc
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `measure_Icc_lt_top
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `norm_set_integral_le_of_norm_le_const'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1022, (some 1023,
     term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `norm_set_integral_le_of_norm_le_const' [`measure_Icc_lt_top `measurable_set_Icc])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≤_»
       (Analysis.Normed.Group.Basic.«term‖_‖»
        "‖"
        (MeasureTheory.Integral.TorusIntegral.«term∯_inT(_,_),_»
         "∯"
         (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
         " in "
         "T("
         `c
         ", "
         `R
         ")"
         ", "
         (Term.app `f [`x]))
        "‖")
       "≤"
       («term_*_»
        («term_*_»
         (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
          "∏"
          (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
          ", "
          («term|___|» (group "|") (Term.app `R [`i]) (group) "|"))
         "*"
         `C)
        "*"
        (Term.proj
         (Term.app
          `volume
          [(Term.app
            `Icc
            [(Term.typeAscription
              "("
              (num "0")
              ":"
              [(MeasureTheory.Integral.TorusIntegral.«termℝⁿ» "ℝⁿ")]
              ")")
             (Term.fun
              "fun"
              (Term.basicFun
               [(Term.hole "_")]
               []
               "=>"
               («term_*_»
                (num "2")
                "*"
                (Real.Analysis.SpecialFunctions.Trigonometric.Basic.real.pi "π"))))])])
         "."
         `toReal)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_»
       («term_*_»
        (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
         "∏"
         (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
         ", "
         («term|___|» (group "|") (Term.app `R [`i]) (group) "|"))
        "*"
        `C)
       "*"
       (Term.proj
        (Term.app
         `volume
         [(Term.app
           `Icc
           [(Term.typeAscription
             "("
             (num "0")
             ":"
             [(MeasureTheory.Integral.TorusIntegral.«termℝⁿ» "ℝⁿ")]
             ")")
            (Term.fun
             "fun"
             (Term.basicFun
              [(Term.hole "_")]
              []
              "=>"
              («term_*_»
               (num "2")
               "*"
               (Real.Analysis.SpecialFunctions.Trigonometric.Basic.real.pi "π"))))])])
        "."
        `toReal))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj
       (Term.app
        `volume
        [(Term.app
          `Icc
          [(Term.typeAscription
            "("
            (num "0")
            ":"
            [(MeasureTheory.Integral.TorusIntegral.«termℝⁿ» "ℝⁿ")]
            ")")
           (Term.fun
            "fun"
            (Term.basicFun
             [(Term.hole "_")]
             []
             "=>"
             («term_*_»
              (num "2")
              "*"
              (Real.Analysis.SpecialFunctions.Trigonometric.Basic.real.pi "π"))))])])
       "."
       `toReal)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       `volume
       [(Term.app
         `Icc
         [(Term.typeAscription
           "("
           (num "0")
           ":"
           [(MeasureTheory.Integral.TorusIntegral.«termℝⁿ» "ℝⁿ")]
           ")")
          (Term.fun
           "fun"
           (Term.basicFun
            [(Term.hole "_")]
            []
            "=>"
            («term_*_»
             (num "2")
             "*"
             (Real.Analysis.SpecialFunctions.Trigonometric.Basic.real.pi "π"))))])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Icc
       [(Term.typeAscription
         "("
         (num "0")
         ":"
         [(MeasureTheory.Integral.TorusIntegral.«termℝⁿ» "ℝⁿ")]
         ")")
        (Term.fun
         "fun"
         (Term.basicFun
          [(Term.hole "_")]
          []
          "=>"
          («term_*_»
           (num "2")
           "*"
           (Real.Analysis.SpecialFunctions.Trigonometric.Basic.real.pi "π"))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [(Term.hole "_")]
        []
        "=>"
        («term_*_» (num "2") "*" (Real.Analysis.SpecialFunctions.Trigonometric.Basic.real.pi "π"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_» (num "2") "*" (Real.Analysis.SpecialFunctions.Trigonometric.Basic.real.pi "π"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Real.Analysis.SpecialFunctions.Trigonometric.Basic.real.pi "π")
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.typeAscription
       "("
       (num "0")
       ":"
       [(MeasureTheory.Integral.TorusIntegral.«termℝⁿ» "ℝⁿ")]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (MeasureTheory.Integral.TorusIntegral.«termℝⁿ» "ℝⁿ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'MeasureTheory.Integral.TorusIntegral.«termℝⁿ»', expected 'MeasureTheory.Integral.TorusIntegral.termℝⁿ._@.MeasureTheory.Integral.TorusIntegral._hyg.158'
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
    If for all `θ : ℝⁿ`, `‖f (torus_map c R θ)‖` is less than or equal to a constant `C : ℝ`, then
    `‖∯ x in T(c, R), f x‖` is less than or equal to `(2 * π)^n * (∏ i, |R i|) * C`-/
  theorem
    norm_torus_integral_le_of_norm_le_const
    { C : ℝ } ( hf : ∀ θ , ‖ f torusMap c R θ ‖ ≤ C )
      : ‖ ∯ x in T( c , R ) , f x ‖ ≤ 2 * π ^ ( n : ℕ ) * ∏ i , | R i | * C
    :=
      calc
        ‖ ∯ x in T( c , R ) , f x ‖
            ≤
            ∏ i , | R i | * C * volume Icc ( 0 : ℝⁿ ) fun _ => 2 * π . toReal
          :=
          norm_set_integral_le_of_norm_le_const' measure_Icc_lt_top measurable_set_Icc
            fun
              θ hθ
                =>
                calc
                  ‖ ( ∏ i : Fin n , R i * exp θ i * I * I : ℂ ) • f torusMap c R θ ‖
                      =
                      ∏ i : Fin n , | R i | * ‖ f torusMap c R θ ‖
                    :=
                    by simp [ norm_smul ]
                  _ ≤ ∏ i : Fin n , | R i | * C
                    :=
                    mul_le_mul_of_nonneg_left hf _ Finset.prod_nonneg fun _ _ => abs_nonneg _
        _ = 2 * π ^ ( n : ℕ ) * ∏ i , | R i | * C
          :=
          by
            simp
              only
              [
                Pi.zero_def
                  ,
                  Real.volume_Icc_pi_to_real fun _ => real.two_pi_pos.le
                  ,
                  sub_zero
                  ,
                  Fin.prod_const
                  ,
                  mul_assoc
                  ,
                  mul_comm 2 * π ^ ( n : ℕ )
                ]
#align norm_torus_integral_le_of_norm_le_const norm_torus_integral_le_of_norm_le_const

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
      (Command.declId `torus_integral_dim0 [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`f]
         [":" (Term.arrow (MeasureTheory.Integral.TorusIntegral.«termℂ⁰» "ℂ⁰") "→" `E)]
         []
         ")")
        (Term.explicitBinder
         "("
         [`c]
         [":" (MeasureTheory.Integral.TorusIntegral.«termℂ⁰» "ℂ⁰")]
         []
         ")")
        (Term.explicitBinder
         "("
         [`R]
         [":" (MeasureTheory.Integral.TorusIntegral.«termℝ⁰» "ℝ⁰")]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (MeasureTheory.Integral.TorusIntegral.«term∯_inT(_,_),_»
          "∯"
          (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
          " in "
          "T("
          `c
          ", "
          `R
          ")"
          ", "
          (Term.app `f [`x]))
         "="
         (Term.app `f [`c]))))
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
            ["["
             [(Tactic.simpLemma [] [] `torusIntegral)
              ","
              (Tactic.simpLemma [] [] `Fin.prod_univ_zero)
              ","
              (Tactic.simpLemma [] [] `one_smul)
              ","
              (Tactic.simpLemma
               []
               []
               (Term.app
                `Subsingleton.elim
                [(Term.fun
                  "fun"
                  (Term.basicFun
                   [`i]
                   [(Term.typeSpec ":" (Term.app `Fin [(num "0")]))]
                   "=>"
                   («term_*_»
                    (num "2")
                    "*"
                    (Real.Analysis.SpecialFunctions.Trigonometric.Basic.real.pi "π"))))
                 (num "0")]))
              ","
              (Tactic.simpLemma [] [] `Icc_self)
              ","
              (Tactic.simpLemma [] [] `measure.restrict_singleton)
              ","
              (Tactic.simpLemma [] [] `volume_pi)
              ","
              (Tactic.simpLemma [] [] `integral_smul_measure)
              ","
              (Tactic.simpLemma [] [] `integral_dirac)
              ","
              (Tactic.simpLemma [] [] (Term.app `measure.pi_of_empty [(Term.hole "_") (num "0")]))
              ","
              (Tactic.simpLemma
               []
               []
               (Term.app `measure.dirac_apply_of_mem [(Term.app `mem_singleton [(Term.hole "_")])]))
              ","
              (Tactic.simpLemma
               []
               []
               (Term.app `Subsingleton.elim [(Term.app `torusMap [`c `R (num "0")]) `c]))]
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
           ["only"]
           ["["
            [(Tactic.simpLemma [] [] `torusIntegral)
             ","
             (Tactic.simpLemma [] [] `Fin.prod_univ_zero)
             ","
             (Tactic.simpLemma [] [] `one_smul)
             ","
             (Tactic.simpLemma
              []
              []
              (Term.app
               `Subsingleton.elim
               [(Term.fun
                 "fun"
                 (Term.basicFun
                  [`i]
                  [(Term.typeSpec ":" (Term.app `Fin [(num "0")]))]
                  "=>"
                  («term_*_»
                   (num "2")
                   "*"
                   (Real.Analysis.SpecialFunctions.Trigonometric.Basic.real.pi "π"))))
                (num "0")]))
             ","
             (Tactic.simpLemma [] [] `Icc_self)
             ","
             (Tactic.simpLemma [] [] `measure.restrict_singleton)
             ","
             (Tactic.simpLemma [] [] `volume_pi)
             ","
             (Tactic.simpLemma [] [] `integral_smul_measure)
             ","
             (Tactic.simpLemma [] [] `integral_dirac)
             ","
             (Tactic.simpLemma [] [] (Term.app `measure.pi_of_empty [(Term.hole "_") (num "0")]))
             ","
             (Tactic.simpLemma
              []
              []
              (Term.app `measure.dirac_apply_of_mem [(Term.app `mem_singleton [(Term.hole "_")])]))
             ","
             (Tactic.simpLemma
              []
              []
              (Term.app `Subsingleton.elim [(Term.app `torusMap [`c `R (num "0")]) `c]))]
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
        [(Tactic.simpLemma [] [] `torusIntegral)
         ","
         (Tactic.simpLemma [] [] `Fin.prod_univ_zero)
         ","
         (Tactic.simpLemma [] [] `one_smul)
         ","
         (Tactic.simpLemma
          []
          []
          (Term.app
           `Subsingleton.elim
           [(Term.fun
             "fun"
             (Term.basicFun
              [`i]
              [(Term.typeSpec ":" (Term.app `Fin [(num "0")]))]
              "=>"
              («term_*_»
               (num "2")
               "*"
               (Real.Analysis.SpecialFunctions.Trigonometric.Basic.real.pi "π"))))
            (num "0")]))
         ","
         (Tactic.simpLemma [] [] `Icc_self)
         ","
         (Tactic.simpLemma [] [] `measure.restrict_singleton)
         ","
         (Tactic.simpLemma [] [] `volume_pi)
         ","
         (Tactic.simpLemma [] [] `integral_smul_measure)
         ","
         (Tactic.simpLemma [] [] `integral_dirac)
         ","
         (Tactic.simpLemma [] [] (Term.app `measure.pi_of_empty [(Term.hole "_") (num "0")]))
         ","
         (Tactic.simpLemma
          []
          []
          (Term.app `measure.dirac_apply_of_mem [(Term.app `mem_singleton [(Term.hole "_")])]))
         ","
         (Tactic.simpLemma
          []
          []
          (Term.app `Subsingleton.elim [(Term.app `torusMap [`c `R (num "0")]) `c]))]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Subsingleton.elim [(Term.app `torusMap [`c `R (num "0")]) `c])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `c
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `torusMap [`c `R (num "0")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `R
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `c
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `torusMap
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `torusMap [`c `R (num "0")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Subsingleton.elim
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `measure.dirac_apply_of_mem [(Term.app `mem_singleton [(Term.hole "_")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `mem_singleton [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `mem_singleton
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `mem_singleton [(Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `measure.dirac_apply_of_mem
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `measure.pi_of_empty [(Term.hole "_") (num "0")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `measure.pi_of_empty
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `integral_dirac
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `integral_smul_measure
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `volume_pi
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `measure.restrict_singleton
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Icc_self
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Subsingleton.elim
       [(Term.fun
         "fun"
         (Term.basicFun
          [`i]
          [(Term.typeSpec ":" (Term.app `Fin [(num "0")]))]
          "=>"
          («term_*_»
           (num "2")
           "*"
           (Real.Analysis.SpecialFunctions.Trigonometric.Basic.real.pi "π"))))
        (num "0")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.fun
       "fun"
       (Term.basicFun
        [`i]
        [(Term.typeSpec ":" (Term.app `Fin [(num "0")]))]
        "=>"
        («term_*_» (num "2") "*" (Real.Analysis.SpecialFunctions.Trigonometric.Basic.real.pi "π"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_» (num "2") "*" (Real.Analysis.SpecialFunctions.Trigonometric.Basic.real.pi "π"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Real.Analysis.SpecialFunctions.Trigonometric.Basic.real.pi "π")
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Fin [(num "0")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
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
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.fun
      "fun"
      (Term.basicFun
       [`i]
       [(Term.typeSpec ":" (Term.app `Fin [(num "0")]))]
       "=>"
       («term_*_» (num "2") "*" (Real.Analysis.SpecialFunctions.Trigonometric.Basic.real.pi "π"))))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Subsingleton.elim
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `one_smul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Fin.prod_univ_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `torusIntegral
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (MeasureTheory.Integral.TorusIntegral.«term∯_inT(_,_),_»
        "∯"
        (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
        " in "
        "T("
        `c
        ", "
        `R
        ")"
        ", "
        (Term.app `f [`x]))
       "="
       (Term.app `f [`c]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `f [`c])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `c
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (MeasureTheory.Integral.TorusIntegral.«term∯_inT(_,_),_»
       "∯"
       (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
       " in "
       "T("
       `c
       ", "
       `R
       ")"
       ", "
       (Term.app `f [`x]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `f [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `R
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `c
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 0, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (MeasureTheory.Integral.TorusIntegral.«term∯_inT(_,_),_»
      "∯"
      (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
      " in "
      "T("
      `c
      ", "
      `R
      ")"
      ", "
      (Term.app `f [`x]))
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (MeasureTheory.Integral.TorusIntegral.«termℝ⁰» "ℝ⁰")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'MeasureTheory.Integral.TorusIntegral.«termℝ⁰»', expected 'MeasureTheory.Integral.TorusIntegral.termℝ⁰._@.MeasureTheory.Integral.TorusIntegral._hyg.6'
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
    torus_integral_dim0
    ( f : ℂ⁰ → E ) ( c : ℂ⁰ ) ( R : ℝ⁰ ) : ∯ x in T( c , R ) , f x = f c
    :=
      by
        simp
          only
          [
            torusIntegral
              ,
              Fin.prod_univ_zero
              ,
              one_smul
              ,
              Subsingleton.elim fun i : Fin 0 => 2 * π 0
              ,
              Icc_self
              ,
              measure.restrict_singleton
              ,
              volume_pi
              ,
              integral_smul_measure
              ,
              integral_dirac
              ,
              measure.pi_of_empty _ 0
              ,
              measure.dirac_apply_of_mem mem_singleton _
              ,
              Subsingleton.elim torusMap c R 0 c
            ]
#align torus_integral_dim0 torus_integral_dim0

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "In dimension one, `torus_integral` is the same as `circle_integral`\n(up to the natural equivalence between `ℂ` and `fin 1 → ℂ`). -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `torus_integral_dim1 [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`f]
         [":" (Term.arrow (MeasureTheory.Integral.TorusIntegral.«termℂ¹» "ℂ¹") "→" `E)]
         []
         ")")
        (Term.explicitBinder
         "("
         [`c]
         [":" (MeasureTheory.Integral.TorusIntegral.«termℂ¹» "ℂ¹")]
         []
         ")")
        (Term.explicitBinder
         "("
         [`R]
         [":" (MeasureTheory.Integral.TorusIntegral.«termℝ¹» "ℝ¹")]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (MeasureTheory.Integral.TorusIntegral.«term∯_inT(_,_),_»
          "∯"
          (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
          " in "
          "T("
          `c
          ", "
          `R
          ")"
          ", "
          (Term.app `f [`x]))
         "="
         (MeasureTheory.Integral.CircleIntegral.«term∮_inC(_,_),_»
          "∮"
          (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `z) []))
          " in "
          "C("
          (Term.app `c [(num "0")])
          ", "
          (Term.app `R [(num "0")])
          ")"
          ", "
          (Term.app `f [(Term.fun "fun" (Term.basicFun [(Term.hole "_")] [] "=>" `z))])))))
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
              []
              [(Term.typeSpec
                ":"
                («term_=_»
                 (Set.Data.Set.Image.«term_⁻¹'_»
                  (Term.fun
                   "fun"
                   (Term.basicFun
                    [(Term.typeAscription
                      "("
                      (Term.app `x [])
                      ":"
                      [(Data.Real.Basic.termℝ "ℝ")]
                      ")")
                     (Term.typeAscription
                      "("
                      (Term.app `b [])
                      ":"
                      [(Term.app `Fin [(num "1")])]
                      ")")]
                    []
                    "=>"
                    `x))
                  " ⁻¹' "
                  (Term.app
                   `Icc
                   [(num "0")
                    (Term.fun
                     "fun"
                     (Term.basicFun
                      [(Term.hole "_")]
                      []
                      "=>"
                      («term_*_»
                       (num "2")
                       "*"
                       (Real.Analysis.SpecialFunctions.Trigonometric.Basic.real.pi "π"))))]))
                 "="
                 (Term.app
                  `Icc
                  [(num "0")
                   («term_*_»
                    (num "2")
                    "*"
                    (Real.Analysis.SpecialFunctions.Trigonometric.Basic.real.pi "π"))])))]
              ":="
              (Term.app
               (Term.proj
                (Term.proj
                 (Term.app
                  `OrderIso.funUnique
                  [(Term.app `Fin [(num "1")]) (Data.Real.Basic.termℝ "ℝ")])
                 "."
                 `symm)
                "."
                `preimage_Icc)
               [(Term.hole "_") (Term.hole "_")]))))
           []
           (Tactic.simp
            "simp"
            []
            []
            ["only"]
            ["["
             [(Tactic.simpLemma [] [] `torusIntegral)
              ","
              (Tactic.simpLemma [] [] `circleIntegral)
              ","
              (Tactic.simpLemma
               []
               []
               (Term.app `intervalIntegral.integral_of_le [`real.two_pi_pos.le]))
              ","
              (Tactic.simpLemma [] [] (Term.app `measure.restrict_congr_set [`Ioc_ae_eq_Icc]))
              ","
              (Tactic.simpLemma [] [] `deriv_circle_map)
              ","
              (Tactic.simpLemma [] [] `Fin.prod_univ_one)
              ","
              (Tactic.simpLemma
               []
               [(patternIgnore (token.«← » "←"))]
               (Term.app
                (Term.proj
                 (Term.app
                  (Term.proj
                   (Term.app
                    `volume_preserving_fun_unique
                    [(Term.app `Fin [(num "1")]) (Data.Real.Basic.termℝ "ℝ")])
                   "."
                   `symm)
                  [(Term.hole "_")])
                 "."
                 `set_integral_preimage_emb)
                [(Term.app `MeasurableEquiv.measurable_embedding [(Term.hole "_")])]))
              ","
              (Tactic.simpLemma [] [] `this)
              ","
              (Tactic.simpLemma [] [] `MeasurableEquiv.fun_unique_symm_apply)]
             "]"]
            [])
           []
           (Tactic.simp
            "simp"
            []
            []
            ["only"]
            ["["
             [(Tactic.simpLemma [] [] `torusMap)
              ","
              (Tactic.simpLemma [] [] `circleMap)
              ","
              (Tactic.simpLemma [] [] `zero_add)]
             "]"]
            [])
           []
           (Std.Tactic.rcongr "rcongr" [])])))
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
             []
             [(Term.typeSpec
               ":"
               («term_=_»
                (Set.Data.Set.Image.«term_⁻¹'_»
                 (Term.fun
                  "fun"
                  (Term.basicFun
                   [(Term.typeAscription "(" (Term.app `x []) ":" [(Data.Real.Basic.termℝ "ℝ")] ")")
                    (Term.typeAscription
                     "("
                     (Term.app `b [])
                     ":"
                     [(Term.app `Fin [(num "1")])]
                     ")")]
                   []
                   "=>"
                   `x))
                 " ⁻¹' "
                 (Term.app
                  `Icc
                  [(num "0")
                   (Term.fun
                    "fun"
                    (Term.basicFun
                     [(Term.hole "_")]
                     []
                     "=>"
                     («term_*_»
                      (num "2")
                      "*"
                      (Real.Analysis.SpecialFunctions.Trigonometric.Basic.real.pi "π"))))]))
                "="
                (Term.app
                 `Icc
                 [(num "0")
                  («term_*_»
                   (num "2")
                   "*"
                   (Real.Analysis.SpecialFunctions.Trigonometric.Basic.real.pi "π"))])))]
             ":="
             (Term.app
              (Term.proj
               (Term.proj
                (Term.app
                 `OrderIso.funUnique
                 [(Term.app `Fin [(num "1")]) (Data.Real.Basic.termℝ "ℝ")])
                "."
                `symm)
               "."
               `preimage_Icc)
              [(Term.hole "_") (Term.hole "_")]))))
          []
          (Tactic.simp
           "simp"
           []
           []
           ["only"]
           ["["
            [(Tactic.simpLemma [] [] `torusIntegral)
             ","
             (Tactic.simpLemma [] [] `circleIntegral)
             ","
             (Tactic.simpLemma
              []
              []
              (Term.app `intervalIntegral.integral_of_le [`real.two_pi_pos.le]))
             ","
             (Tactic.simpLemma [] [] (Term.app `measure.restrict_congr_set [`Ioc_ae_eq_Icc]))
             ","
             (Tactic.simpLemma [] [] `deriv_circle_map)
             ","
             (Tactic.simpLemma [] [] `Fin.prod_univ_one)
             ","
             (Tactic.simpLemma
              []
              [(patternIgnore (token.«← » "←"))]
              (Term.app
               (Term.proj
                (Term.app
                 (Term.proj
                  (Term.app
                   `volume_preserving_fun_unique
                   [(Term.app `Fin [(num "1")]) (Data.Real.Basic.termℝ "ℝ")])
                  "."
                  `symm)
                 [(Term.hole "_")])
                "."
                `set_integral_preimage_emb)
               [(Term.app `MeasurableEquiv.measurable_embedding [(Term.hole "_")])]))
             ","
             (Tactic.simpLemma [] [] `this)
             ","
             (Tactic.simpLemma [] [] `MeasurableEquiv.fun_unique_symm_apply)]
            "]"]
           [])
          []
          (Tactic.simp
           "simp"
           []
           []
           ["only"]
           ["["
            [(Tactic.simpLemma [] [] `torusMap)
             ","
             (Tactic.simpLemma [] [] `circleMap)
             ","
             (Tactic.simpLemma [] [] `zero_add)]
            "]"]
           [])
          []
          (Std.Tactic.rcongr "rcongr" [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.rcongr "rcongr" [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["["
        [(Tactic.simpLemma [] [] `torusMap)
         ","
         (Tactic.simpLemma [] [] `circleMap)
         ","
         (Tactic.simpLemma [] [] `zero_add)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `zero_add
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `circleMap
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `torusMap
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["["
        [(Tactic.simpLemma [] [] `torusIntegral)
         ","
         (Tactic.simpLemma [] [] `circleIntegral)
         ","
         (Tactic.simpLemma [] [] (Term.app `intervalIntegral.integral_of_le [`real.two_pi_pos.le]))
         ","
         (Tactic.simpLemma [] [] (Term.app `measure.restrict_congr_set [`Ioc_ae_eq_Icc]))
         ","
         (Tactic.simpLemma [] [] `deriv_circle_map)
         ","
         (Tactic.simpLemma [] [] `Fin.prod_univ_one)
         ","
         (Tactic.simpLemma
          []
          [(patternIgnore (token.«← » "←"))]
          (Term.app
           (Term.proj
            (Term.app
             (Term.proj
              (Term.app
               `volume_preserving_fun_unique
               [(Term.app `Fin [(num "1")]) (Data.Real.Basic.termℝ "ℝ")])
              "."
              `symm)
             [(Term.hole "_")])
            "."
            `set_integral_preimage_emb)
           [(Term.app `MeasurableEquiv.measurable_embedding [(Term.hole "_")])]))
         ","
         (Tactic.simpLemma [] [] `this)
         ","
         (Tactic.simpLemma [] [] `MeasurableEquiv.fun_unique_symm_apply)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `MeasurableEquiv.fun_unique_symm_apply
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
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
       (Term.proj
        (Term.app
         (Term.proj
          (Term.app
           `volume_preserving_fun_unique
           [(Term.app `Fin [(num "1")]) (Data.Real.Basic.termℝ "ℝ")])
          "."
          `symm)
         [(Term.hole "_")])
        "."
        `set_integral_preimage_emb)
       [(Term.app `MeasurableEquiv.measurable_embedding [(Term.hole "_")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `MeasurableEquiv.measurable_embedding [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `MeasurableEquiv.measurable_embedding
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `MeasurableEquiv.measurable_embedding [(Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (Term.app
        (Term.proj
         (Term.app
          `volume_preserving_fun_unique
          [(Term.app `Fin [(num "1")]) (Data.Real.Basic.termℝ "ℝ")])
         "."
         `symm)
        [(Term.hole "_")])
       "."
       `set_integral_preimage_emb)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       (Term.proj
        (Term.app
         `volume_preserving_fun_unique
         [(Term.app `Fin [(num "1")]) (Data.Real.Basic.termℝ "ℝ")])
        "."
        `symm)
       [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (Term.app
        `volume_preserving_fun_unique
        [(Term.app `Fin [(num "1")]) (Data.Real.Basic.termℝ "ℝ")])
       "."
       `symm)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       `volume_preserving_fun_unique
       [(Term.app `Fin [(num "1")]) (Data.Real.Basic.termℝ "ℝ")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Basic.termℝ', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Basic.termℝ', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Real.Basic.termℝ "ℝ")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.app `Fin [(num "1")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Fin
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `Fin [(num "1")]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `volume_preserving_fun_unique
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `volume_preserving_fun_unique
      [(Term.paren "(" (Term.app `Fin [(num "1")]) ")") (Data.Real.Basic.termℝ "ℝ")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      (Term.proj
       (Term.paren
        "("
        (Term.app
         `volume_preserving_fun_unique
         [(Term.paren "(" (Term.app `Fin [(num "1")]) ")") (Data.Real.Basic.termℝ "ℝ")])
        ")")
       "."
       `symm)
      [(Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Fin.prod_univ_one
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `deriv_circle_map
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `measure.restrict_congr_set [`Ioc_ae_eq_Icc])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Ioc_ae_eq_Icc
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `measure.restrict_congr_set
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `intervalIntegral.integral_of_le [`real.two_pi_pos.le])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `real.two_pi_pos.le
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `intervalIntegral.integral_of_le
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `circleIntegral
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `torusIntegral
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
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
            (Set.Data.Set.Image.«term_⁻¹'_»
             (Term.fun
              "fun"
              (Term.basicFun
               [(Term.typeAscription "(" (Term.app `x []) ":" [(Data.Real.Basic.termℝ "ℝ")] ")")
                (Term.typeAscription "(" (Term.app `b []) ":" [(Term.app `Fin [(num "1")])] ")")]
               []
               "=>"
               `x))
             " ⁻¹' "
             (Term.app
              `Icc
              [(num "0")
               (Term.fun
                "fun"
                (Term.basicFun
                 [(Term.hole "_")]
                 []
                 "=>"
                 («term_*_»
                  (num "2")
                  "*"
                  (Real.Analysis.SpecialFunctions.Trigonometric.Basic.real.pi "π"))))]))
            "="
            (Term.app
             `Icc
             [(num "0")
              («term_*_»
               (num "2")
               "*"
               (Real.Analysis.SpecialFunctions.Trigonometric.Basic.real.pi "π"))])))]
         ":="
         (Term.app
          (Term.proj
           (Term.proj
            (Term.app `OrderIso.funUnique [(Term.app `Fin [(num "1")]) (Data.Real.Basic.termℝ "ℝ")])
            "."
            `symm)
           "."
           `preimage_Icc)
          [(Term.hole "_") (Term.hole "_")]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (Term.proj
         (Term.app `OrderIso.funUnique [(Term.app `Fin [(num "1")]) (Data.Real.Basic.termℝ "ℝ")])
         "."
         `symm)
        "."
        `preimage_Icc)
       [(Term.hole "_") (Term.hole "_")])
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
      (Term.proj
       (Term.proj
        (Term.app `OrderIso.funUnique [(Term.app `Fin [(num "1")]) (Data.Real.Basic.termℝ "ℝ")])
        "."
        `symm)
       "."
       `preimage_Icc)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj
       (Term.app `OrderIso.funUnique [(Term.app `Fin [(num "1")]) (Data.Real.Basic.termℝ "ℝ")])
       "."
       `symm)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `OrderIso.funUnique [(Term.app `Fin [(num "1")]) (Data.Real.Basic.termℝ "ℝ")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Basic.termℝ', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Basic.termℝ', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Real.Basic.termℝ "ℝ")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.app `Fin [(num "1")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Fin
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `Fin [(num "1")]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `OrderIso.funUnique
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `OrderIso.funUnique
      [(Term.paren "(" (Term.app `Fin [(num "1")]) ")") (Data.Real.Basic.termℝ "ℝ")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Set.Data.Set.Image.«term_⁻¹'_»
        (Term.fun
         "fun"
         (Term.basicFun
          [(Term.typeAscription "(" (Term.app `x []) ":" [(Data.Real.Basic.termℝ "ℝ")] ")")
           (Term.typeAscription "(" (Term.app `b []) ":" [(Term.app `Fin [(num "1")])] ")")]
          []
          "=>"
          `x))
        " ⁻¹' "
        (Term.app
         `Icc
         [(num "0")
          (Term.fun
           "fun"
           (Term.basicFun
            [(Term.hole "_")]
            []
            "=>"
            («term_*_»
             (num "2")
             "*"
             (Real.Analysis.SpecialFunctions.Trigonometric.Basic.real.pi "π"))))]))
       "="
       (Term.app
        `Icc
        [(num "0")
         («term_*_»
          (num "2")
          "*"
          (Real.Analysis.SpecialFunctions.Trigonometric.Basic.real.pi "π"))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Icc
       [(num "0")
        («term_*_» (num "2") "*" (Real.Analysis.SpecialFunctions.Trigonometric.Basic.real.pi "π"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_*_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_*_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_» (num "2") "*" (Real.Analysis.SpecialFunctions.Trigonometric.Basic.real.pi "π"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Real.Analysis.SpecialFunctions.Trigonometric.Basic.real.pi "π")
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_*_» (num "2") "*" (Real.Analysis.SpecialFunctions.Trigonometric.Basic.real.pi "π"))
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Icc
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Set.Data.Set.Image.«term_⁻¹'_»
       (Term.fun
        "fun"
        (Term.basicFun
         [(Term.typeAscription "(" (Term.app `x []) ":" [(Data.Real.Basic.termℝ "ℝ")] ")")
          (Term.typeAscription "(" (Term.app `b []) ":" [(Term.app `Fin [(num "1")])] ")")]
         []
         "=>"
         `x))
       " ⁻¹' "
       (Term.app
        `Icc
        [(num "0")
         (Term.fun
          "fun"
          (Term.basicFun
           [(Term.hole "_")]
           []
           "=>"
           («term_*_»
            (num "2")
            "*"
            (Real.Analysis.SpecialFunctions.Trigonometric.Basic.real.pi "π"))))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Icc
       [(num "0")
        (Term.fun
         "fun"
         (Term.basicFun
          [(Term.hole "_")]
          []
          "=>"
          («term_*_»
           (num "2")
           "*"
           (Real.Analysis.SpecialFunctions.Trigonometric.Basic.real.pi "π"))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [(Term.hole "_")]
        []
        "=>"
        («term_*_» (num "2") "*" (Real.Analysis.SpecialFunctions.Trigonometric.Basic.real.pi "π"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_» (num "2") "*" (Real.Analysis.SpecialFunctions.Trigonometric.Basic.real.pi "π"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Real.Analysis.SpecialFunctions.Trigonometric.Basic.real.pi "π")
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Icc
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Term.fun
       "fun"
       (Term.basicFun
        [(Term.typeAscription "(" (Term.app `x []) ":" [(Data.Real.Basic.termℝ "ℝ")] ")")
         (Term.typeAscription "(" (Term.app `b []) ":" [(Term.app `Fin [(num "1")])] ")")]
        []
        "=>"
        `x))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription "(" (Term.app `b []) ":" [(Term.app `Fin [(num "1")])] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Fin [(num "1")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Fin
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `b [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `b
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1024, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.typeAscription "(" (Term.app `x []) ":" [(Data.Real.Basic.termℝ "ℝ")] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Real.Basic.termℝ "ℝ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `x [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1024, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (some 0, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.fun
      "fun"
      (Term.basicFun
       [(Term.typeAscription "(" (Term.app `x []) ":" [(Data.Real.Basic.termℝ "ℝ")] ")")
        (Term.typeAscription "(" (Term.app `b []) ":" [(Term.app `Fin [(num "1")])] ")")]
       []
       "=>"
       `x))
     ")")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 80, (some 0, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Set.Data.Set.Image.«term_⁻¹'_»
      (Term.paren
       "("
       (Term.fun
        "fun"
        (Term.basicFun
         [(Term.typeAscription "(" (Term.app `x []) ":" [(Data.Real.Basic.termℝ "ℝ")] ")")
          (Term.typeAscription "(" (Term.app `b []) ":" [(Term.app `Fin [(num "1")])] ")")]
         []
         "=>"
         `x))
       ")")
      " ⁻¹' "
      (Term.app
       `Icc
       [(num "0")
        (Term.fun
         "fun"
         (Term.basicFun
          [(Term.hole "_")]
          []
          "=>"
          («term_*_»
           (num "2")
           "*"
           (Real.Analysis.SpecialFunctions.Trigonometric.Basic.real.pi "π"))))]))
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (MeasureTheory.Integral.TorusIntegral.«term∯_inT(_,_),_»
        "∯"
        (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
        " in "
        "T("
        `c
        ", "
        `R
        ")"
        ", "
        (Term.app `f [`x]))
       "="
       (MeasureTheory.Integral.CircleIntegral.«term∮_inC(_,_),_»
        "∮"
        (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `z) []))
        " in "
        "C("
        (Term.app `c [(num "0")])
        ", "
        (Term.app `R [(num "0")])
        ")"
        ", "
        (Term.app `f [(Term.fun "fun" (Term.basicFun [(Term.hole "_")] [] "=>" `z))])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (MeasureTheory.Integral.CircleIntegral.«term∮_inC(_,_),_»
       "∮"
       (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `z) []))
       " in "
       "C("
       (Term.app `c [(num "0")])
       ", "
       (Term.app `R [(num "0")])
       ")"
       ", "
       (Term.app `f [(Term.fun "fun" (Term.basicFun [(Term.hole "_")] [] "=>" `z))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `f [(Term.fun "fun" (Term.basicFun [(Term.hole "_")] [] "=>" `z))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun "fun" (Term.basicFun [(Term.hole "_")] [] "=>" `z))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `z
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
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `R [(num "0")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `R
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
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
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (MeasureTheory.Integral.TorusIntegral.«term∯_inT(_,_),_»
       "∯"
       (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
       " in "
       "T("
       `c
       ", "
       `R
       ")"
       ", "
       (Term.app `f [`x]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `f [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `R
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `c
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 0, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (MeasureTheory.Integral.TorusIntegral.«term∯_inT(_,_),_»
      "∯"
      (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
      " in "
      "T("
      `c
      ", "
      `R
      ")"
      ", "
      (Term.app `f [`x]))
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 0, term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (MeasureTheory.Integral.TorusIntegral.«termℝ¹» "ℝ¹")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'MeasureTheory.Integral.TorusIntegral.«termℝ¹»', expected 'MeasureTheory.Integral.TorusIntegral.termℝ¹._@.MeasureTheory.Integral.TorusIntegral._hyg.84'
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
/--
    In dimension one, `torus_integral` is the same as `circle_integral`
    (up to the natural equivalence between `ℂ` and `fin 1 → ℂ`). -/
  theorem
    torus_integral_dim1
    ( f : ℂ¹ → E ) ( c : ℂ¹ ) ( R : ℝ¹ )
      : ∯ x in T( c , R ) , f x = ∮ z in C( c 0 , R 0 ) , f fun _ => z
    :=
      by
        have
            : fun ( x : ℝ ) ( b : Fin 1 ) => x ⁻¹' Icc 0 fun _ => 2 * π = Icc 0 2 * π
              :=
              OrderIso.funUnique Fin 1 ℝ . symm . preimage_Icc _ _
          simp
            only
            [
              torusIntegral
                ,
                circleIntegral
                ,
                intervalIntegral.integral_of_le real.two_pi_pos.le
                ,
                measure.restrict_congr_set Ioc_ae_eq_Icc
                ,
                deriv_circle_map
                ,
                Fin.prod_univ_one
                ,
                ←
                  volume_preserving_fun_unique Fin 1 ℝ . symm _ . set_integral_preimage_emb
                    MeasurableEquiv.measurable_embedding _
                ,
                this
                ,
                MeasurableEquiv.fun_unique_symm_apply
              ]
          simp only [ torusMap , circleMap , zero_add ]
          rcongr
#align torus_integral_dim1 torus_integral_dim1

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "Recurrent formula for `torus_integral`, see also `torus_integral_succ`. -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `torus_integral_succ_above [])
      (Command.declSig
       [(Term.implicitBinder
         "{"
         [`f]
         [":" (Term.arrow (MeasureTheory.Integral.TorusIntegral.«termℂⁿ⁺¹» "ℂⁿ⁺¹") "→" `E)]
         "}")
        (Term.implicitBinder
         "{"
         [`c]
         [":" (MeasureTheory.Integral.TorusIntegral.«termℂⁿ⁺¹» "ℂⁿ⁺¹")]
         "}")
        (Term.implicitBinder
         "{"
         [`R]
         [":" (MeasureTheory.Integral.TorusIntegral.«termℝⁿ⁺¹» "ℝⁿ⁺¹")]
         "}")
        (Term.explicitBinder "(" [`hf] [":" (Term.app `TorusIntegrable [`f `c `R])] [] ")")
        (Term.explicitBinder "(" [`i] [":" (Term.app `Fin [(«term_+_» `n "+" (num "1"))])] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (MeasureTheory.Integral.TorusIntegral.«term∯_inT(_,_),_»
          "∯"
          (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
          " in "
          "T("
          `c
          ", "
          `R
          ")"
          ", "
          (Term.app `f [`x]))
         "="
         (MeasureTheory.Integral.CircleIntegral.«term∮_inC(_,_),_»
          "∮"
          (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
          " in "
          "C("
          (Term.app `c [`i])
          ", "
          (Term.app `R [`i])
          ")"
          ", "
          (MeasureTheory.Integral.TorusIntegral.«term∯_inT(_,_),_»
           "∯"
           (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `y) []))
           " in "
           "T("
           («term_∘_» `c "∘" (Term.proj `i "." `succAbove))
           ", "
           («term_∘_» `R "∘" (Term.proj `i "." `succAbove))
           ")"
           ", "
           (Term.app `f [(Term.app (Term.proj `i "." `insertNth) [`x `y])]))))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Mathlib.Tactic.set
            "set"
            []
            (Mathlib.Tactic.setArgsRest
             `e
             [":"
              (MeasureTheory.MeasurableSpace.«term_≃ᵐ_»
               («term_×_»
                (Data.Real.Basic.termℝ "ℝ")
                "×"
                (MeasureTheory.Integral.TorusIntegral.«termℝⁿ» "ℝⁿ"))
               " ≃ᵐ "
               (MeasureTheory.Integral.TorusIntegral.«termℝⁿ⁺¹» "ℝⁿ⁺¹"))]
             ":="
             (Term.proj
              (Term.app
               `MeasurableEquiv.piFinSuccAboveEquiv
               [(Term.fun
                 "fun"
                 (Term.basicFun [(Term.hole "_")] [] "=>" (Data.Real.Basic.termℝ "ℝ")))
                `i])
              "."
              `symm)
             []))
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`hem []]
              [(Term.typeSpec ":" (Term.app `measure_preserving [`e]))]
              ":="
              (Term.app
               (Term.proj
                (Term.app
                 `volume_preserving_pi_fin_succ_above_equiv
                 [(Term.fun
                   "fun"
                   (Term.basicFun
                    [`j]
                    [(Term.typeSpec ":" (Term.app `Fin [(«term_+_» `n "+" (num "1"))]))]
                    "=>"
                    (Data.Real.Basic.termℝ "ℝ")))
                  `i])
                "."
                `symm)
               [(Term.hole "_")]))))
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`heπ []]
              [(Term.typeSpec
                ":"
                («term_=_»
                 (Set.Data.Set.Image.«term_⁻¹'_»
                  `e
                  " ⁻¹' "
                  (Term.app
                   `Icc
                   [(num "0")
                    (Term.fun
                     "fun"
                     (Term.basicFun
                      [(Term.hole "_")]
                      []
                      "=>"
                      («term_*_»
                       (num "2")
                       "*"
                       (Real.Analysis.SpecialFunctions.Trigonometric.Basic.real.pi "π"))))]))
                 "="
                 (LowerSet.Order.UpperLower.lower_set.prod
                  (Term.app
                   `Icc
                   [(num "0")
                    («term_*_»
                     (num "2")
                     "*"
                     (Real.Analysis.SpecialFunctions.Trigonometric.Basic.real.pi "π"))])
                  " ×ˢ "
                  (Term.app
                   `Icc
                   [(Term.typeAscription
                     "("
                     (num "0")
                     ":"
                     [(MeasureTheory.Integral.TorusIntegral.«termℝⁿ» "ℝⁿ")]
                     ")")
                    (Term.fun
                     "fun"
                     (Term.basicFun
                      [(Term.hole "_")]
                      []
                      "=>"
                      («term_*_»
                       (num "2")
                       "*"
                       (Real.Analysis.SpecialFunctions.Trigonometric.Basic.real.pi "π"))))]))))]
              ":="
              (Term.app
               (Term.proj
                (Term.app
                 (Term.proj
                  (Term.proj
                   (Term.app
                    `OrderIso.piFinSuccAboveIso
                    [(Term.fun
                      "fun"
                      (Term.basicFun [(Term.hole "_")] [] "=>" (Data.Real.Basic.termℝ "ℝ")))
                     `i])
                   "."
                   `symm)
                  "."
                  `preimage_Icc)
                 [(Term.hole "_") (Term.hole "_")])
                "."
                `trans)
               [(Term.app `Icc_prod_eq [(Term.hole "_") (Term.hole "_")])]))))
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [] `torusIntegral)
              ","
              (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `hem.map_eq)
              ","
              (Tactic.rwRule [] `set_integral_map_equiv)
              ","
              (Tactic.rwRule [] `heπ)
              ","
              (Tactic.rwRule [] `measure.volume_eq_prod)
              ","
              (Tactic.rwRule [] `set_integral_prod)
              ","
              (Tactic.rwRule [] `circle_integral_def_Icc)]
             "]")
            [])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.refine'
              "refine'"
              (Term.app
               `set_integral_congr
               [`measurable_set_Icc
                (Term.fun "fun" (Term.basicFun [`θ `hθ] [] "=>" (Term.hole "_")))]))
             []
             (Tactic.simp
              "simp"
              []
              []
              ["only"]
              ["["
               [(Tactic.simpLemma [] [] `torusIntegral)
                ","
                (Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `integral_smul)
                ","
                (Tactic.simpLemma [] [] `deriv_circle_map)
                ","
                (Tactic.simpLemma [] [] (Term.app `i.prod_univ_succ_above [(Term.hole "_")]))
                ","
                (Tactic.simpLemma [] [] `smul_smul)
                ","
                (Tactic.simpLemma [] [] `torusMap)
                ","
                (Tactic.simpLemma [] [] `circle_map_zero)]
               "]"]
              [])
             []
             (Tactic.refine'
              "refine'"
              (Term.app
               `set_integral_congr
               [`measurable_set_Icc
                (Term.fun "fun" (Term.basicFun [`Θ `hΘ] [] "=>" (Term.hole "_")))]))
             []
             (Tactic.simp
              "simp"
              []
              []
              ["only"]
              ["["
               [(Tactic.simpLemma [] [] `MeasurableEquiv.pi_fin_succ_above_equiv_symm_apply)
                ","
                (Tactic.simpLemma [] [] `i.insert_nth_apply_same)
                ","
                (Tactic.simpLemma [] [] `i.insert_nth_apply_succ_above)
                ","
                (Tactic.simpLemma
                 []
                 []
                 (Term.paren "(" («term_∘_» (Term.cdot "·") "∘" (Term.cdot "·")) ")"))]
               "]"]
              [])
             []
             (Tactic.congr "congr" [(num "2")])
             []
             (Tactic.simp
              "simp"
              []
              []
              ["only"]
              ["["
               [(Tactic.simpLemma [] [] `funext_iff)
                ","
                (Tactic.simpLemma [] [] `i.forall_iff_succ_above)
                ","
                (Tactic.simpLemma [] [] `circleMap)
                ","
                (Tactic.simpLemma [] [] `Fin.insert_nth_apply_same)
                ","
                (Tactic.simpLemma [] [] `eq_self_iff_true)
                ","
                (Tactic.simpLemma [] [] `Fin.insert_nth_apply_succ_above)
                ","
                (Tactic.simpLemma [] [] `imp_true_iff)
                ","
                (Tactic.simpLemma [] [] `and_self_iff)]
               "]"]
              [])])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.tacticHave_
              "have"
              (Term.haveDecl (Term.haveIdDecl [] [] ":=" `hf.function_integrable)))
             []
             (Std.Tactic.tacticRwa__
              "rwa"
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule
                 [(patternIgnore (token.«← » "←"))]
                 (Term.app `hem.integrable_on_comp_preimage [`e.measurable_embedding]))
                ","
                (Tactic.rwRule [] `heπ)]
               "]")
              [(Tactic.location "at" (Tactic.locationHyp [`this] []))])])])))
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
         [(Mathlib.Tactic.set
           "set"
           []
           (Mathlib.Tactic.setArgsRest
            `e
            [":"
             (MeasureTheory.MeasurableSpace.«term_≃ᵐ_»
              («term_×_»
               (Data.Real.Basic.termℝ "ℝ")
               "×"
               (MeasureTheory.Integral.TorusIntegral.«termℝⁿ» "ℝⁿ"))
              " ≃ᵐ "
              (MeasureTheory.Integral.TorusIntegral.«termℝⁿ⁺¹» "ℝⁿ⁺¹"))]
            ":="
            (Term.proj
             (Term.app
              `MeasurableEquiv.piFinSuccAboveEquiv
              [(Term.fun
                "fun"
                (Term.basicFun [(Term.hole "_")] [] "=>" (Data.Real.Basic.termℝ "ℝ")))
               `i])
             "."
             `symm)
            []))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`hem []]
             [(Term.typeSpec ":" (Term.app `measure_preserving [`e]))]
             ":="
             (Term.app
              (Term.proj
               (Term.app
                `volume_preserving_pi_fin_succ_above_equiv
                [(Term.fun
                  "fun"
                  (Term.basicFun
                   [`j]
                   [(Term.typeSpec ":" (Term.app `Fin [(«term_+_» `n "+" (num "1"))]))]
                   "=>"
                   (Data.Real.Basic.termℝ "ℝ")))
                 `i])
               "."
               `symm)
              [(Term.hole "_")]))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`heπ []]
             [(Term.typeSpec
               ":"
               («term_=_»
                (Set.Data.Set.Image.«term_⁻¹'_»
                 `e
                 " ⁻¹' "
                 (Term.app
                  `Icc
                  [(num "0")
                   (Term.fun
                    "fun"
                    (Term.basicFun
                     [(Term.hole "_")]
                     []
                     "=>"
                     («term_*_»
                      (num "2")
                      "*"
                      (Real.Analysis.SpecialFunctions.Trigonometric.Basic.real.pi "π"))))]))
                "="
                (LowerSet.Order.UpperLower.lower_set.prod
                 (Term.app
                  `Icc
                  [(num "0")
                   («term_*_»
                    (num "2")
                    "*"
                    (Real.Analysis.SpecialFunctions.Trigonometric.Basic.real.pi "π"))])
                 " ×ˢ "
                 (Term.app
                  `Icc
                  [(Term.typeAscription
                    "("
                    (num "0")
                    ":"
                    [(MeasureTheory.Integral.TorusIntegral.«termℝⁿ» "ℝⁿ")]
                    ")")
                   (Term.fun
                    "fun"
                    (Term.basicFun
                     [(Term.hole "_")]
                     []
                     "=>"
                     («term_*_»
                      (num "2")
                      "*"
                      (Real.Analysis.SpecialFunctions.Trigonometric.Basic.real.pi "π"))))]))))]
             ":="
             (Term.app
              (Term.proj
               (Term.app
                (Term.proj
                 (Term.proj
                  (Term.app
                   `OrderIso.piFinSuccAboveIso
                   [(Term.fun
                     "fun"
                     (Term.basicFun [(Term.hole "_")] [] "=>" (Data.Real.Basic.termℝ "ℝ")))
                    `i])
                  "."
                  `symm)
                 "."
                 `preimage_Icc)
                [(Term.hole "_") (Term.hole "_")])
               "."
               `trans)
              [(Term.app `Icc_prod_eq [(Term.hole "_") (Term.hole "_")])]))))
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `torusIntegral)
             ","
             (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `hem.map_eq)
             ","
             (Tactic.rwRule [] `set_integral_map_equiv)
             ","
             (Tactic.rwRule [] `heπ)
             ","
             (Tactic.rwRule [] `measure.volume_eq_prod)
             ","
             (Tactic.rwRule [] `set_integral_prod)
             ","
             (Tactic.rwRule [] `circle_integral_def_Icc)]
            "]")
           [])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.refine'
             "refine'"
             (Term.app
              `set_integral_congr
              [`measurable_set_Icc
               (Term.fun "fun" (Term.basicFun [`θ `hθ] [] "=>" (Term.hole "_")))]))
            []
            (Tactic.simp
             "simp"
             []
             []
             ["only"]
             ["["
              [(Tactic.simpLemma [] [] `torusIntegral)
               ","
               (Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `integral_smul)
               ","
               (Tactic.simpLemma [] [] `deriv_circle_map)
               ","
               (Tactic.simpLemma [] [] (Term.app `i.prod_univ_succ_above [(Term.hole "_")]))
               ","
               (Tactic.simpLemma [] [] `smul_smul)
               ","
               (Tactic.simpLemma [] [] `torusMap)
               ","
               (Tactic.simpLemma [] [] `circle_map_zero)]
              "]"]
             [])
            []
            (Tactic.refine'
             "refine'"
             (Term.app
              `set_integral_congr
              [`measurable_set_Icc
               (Term.fun "fun" (Term.basicFun [`Θ `hΘ] [] "=>" (Term.hole "_")))]))
            []
            (Tactic.simp
             "simp"
             []
             []
             ["only"]
             ["["
              [(Tactic.simpLemma [] [] `MeasurableEquiv.pi_fin_succ_above_equiv_symm_apply)
               ","
               (Tactic.simpLemma [] [] `i.insert_nth_apply_same)
               ","
               (Tactic.simpLemma [] [] `i.insert_nth_apply_succ_above)
               ","
               (Tactic.simpLemma
                []
                []
                (Term.paren "(" («term_∘_» (Term.cdot "·") "∘" (Term.cdot "·")) ")"))]
              "]"]
             [])
            []
            (Tactic.congr "congr" [(num "2")])
            []
            (Tactic.simp
             "simp"
             []
             []
             ["only"]
             ["["
              [(Tactic.simpLemma [] [] `funext_iff)
               ","
               (Tactic.simpLemma [] [] `i.forall_iff_succ_above)
               ","
               (Tactic.simpLemma [] [] `circleMap)
               ","
               (Tactic.simpLemma [] [] `Fin.insert_nth_apply_same)
               ","
               (Tactic.simpLemma [] [] `eq_self_iff_true)
               ","
               (Tactic.simpLemma [] [] `Fin.insert_nth_apply_succ_above)
               ","
               (Tactic.simpLemma [] [] `imp_true_iff)
               ","
               (Tactic.simpLemma [] [] `and_self_iff)]
              "]"]
             [])])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.tacticHave_
             "have"
             (Term.haveDecl (Term.haveIdDecl [] [] ":=" `hf.function_integrable)))
            []
            (Std.Tactic.tacticRwa__
             "rwa"
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule
                [(patternIgnore (token.«← » "←"))]
                (Term.app `hem.integrable_on_comp_preimage [`e.measurable_embedding]))
               ","
               (Tactic.rwRule [] `heπ)]
              "]")
             [(Tactic.location "at" (Tactic.locationHyp [`this] []))])])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.tacticHave_
         "have"
         (Term.haveDecl (Term.haveIdDecl [] [] ":=" `hf.function_integrable)))
        []
        (Std.Tactic.tacticRwa__
         "rwa"
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule
            [(patternIgnore (token.«← » "←"))]
            (Term.app `hem.integrable_on_comp_preimage [`e.measurable_embedding]))
           ","
           (Tactic.rwRule [] `heπ)]
          "]")
         [(Tactic.location "at" (Tactic.locationHyp [`this] []))])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.tacticRwa__
       "rwa"
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule
          [(patternIgnore (token.«← » "←"))]
          (Term.app `hem.integrable_on_comp_preimage [`e.measurable_embedding]))
         ","
         (Tactic.rwRule [] `heπ)]
        "]")
       [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `this
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `heπ
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `hem.integrable_on_comp_preimage [`e.measurable_embedding])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `e.measurable_embedding
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `hem.integrable_on_comp_preimage
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl (Term.haveIdDecl [] [] ":=" `hf.function_integrable)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hf.function_integrable
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.refine'
         "refine'"
         (Term.app
          `set_integral_congr
          [`measurable_set_Icc (Term.fun "fun" (Term.basicFun [`θ `hθ] [] "=>" (Term.hole "_")))]))
        []
        (Tactic.simp
         "simp"
         []
         []
         ["only"]
         ["["
          [(Tactic.simpLemma [] [] `torusIntegral)
           ","
           (Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `integral_smul)
           ","
           (Tactic.simpLemma [] [] `deriv_circle_map)
           ","
           (Tactic.simpLemma [] [] (Term.app `i.prod_univ_succ_above [(Term.hole "_")]))
           ","
           (Tactic.simpLemma [] [] `smul_smul)
           ","
           (Tactic.simpLemma [] [] `torusMap)
           ","
           (Tactic.simpLemma [] [] `circle_map_zero)]
          "]"]
         [])
        []
        (Tactic.refine'
         "refine'"
         (Term.app
          `set_integral_congr
          [`measurable_set_Icc (Term.fun "fun" (Term.basicFun [`Θ `hΘ] [] "=>" (Term.hole "_")))]))
        []
        (Tactic.simp
         "simp"
         []
         []
         ["only"]
         ["["
          [(Tactic.simpLemma [] [] `MeasurableEquiv.pi_fin_succ_above_equiv_symm_apply)
           ","
           (Tactic.simpLemma [] [] `i.insert_nth_apply_same)
           ","
           (Tactic.simpLemma [] [] `i.insert_nth_apply_succ_above)
           ","
           (Tactic.simpLemma
            []
            []
            (Term.paren "(" («term_∘_» (Term.cdot "·") "∘" (Term.cdot "·")) ")"))]
          "]"]
         [])
        []
        (Tactic.congr "congr" [(num "2")])
        []
        (Tactic.simp
         "simp"
         []
         []
         ["only"]
         ["["
          [(Tactic.simpLemma [] [] `funext_iff)
           ","
           (Tactic.simpLemma [] [] `i.forall_iff_succ_above)
           ","
           (Tactic.simpLemma [] [] `circleMap)
           ","
           (Tactic.simpLemma [] [] `Fin.insert_nth_apply_same)
           ","
           (Tactic.simpLemma [] [] `eq_self_iff_true)
           ","
           (Tactic.simpLemma [] [] `Fin.insert_nth_apply_succ_above)
           ","
           (Tactic.simpLemma [] [] `imp_true_iff)
           ","
           (Tactic.simpLemma [] [] `and_self_iff)]
          "]"]
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["["
        [(Tactic.simpLemma [] [] `funext_iff)
         ","
         (Tactic.simpLemma [] [] `i.forall_iff_succ_above)
         ","
         (Tactic.simpLemma [] [] `circleMap)
         ","
         (Tactic.simpLemma [] [] `Fin.insert_nth_apply_same)
         ","
         (Tactic.simpLemma [] [] `eq_self_iff_true)
         ","
         (Tactic.simpLemma [] [] `Fin.insert_nth_apply_succ_above)
         ","
         (Tactic.simpLemma [] [] `imp_true_iff)
         ","
         (Tactic.simpLemma [] [] `and_self_iff)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `and_self_iff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `imp_true_iff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Fin.insert_nth_apply_succ_above
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `eq_self_iff_true
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Fin.insert_nth_apply_same
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `circleMap
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i.forall_iff_succ_above
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `funext_iff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.congr "congr" [(num "2")])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["["
        [(Tactic.simpLemma [] [] `MeasurableEquiv.pi_fin_succ_above_equiv_symm_apply)
         ","
         (Tactic.simpLemma [] [] `i.insert_nth_apply_same)
         ","
         (Tactic.simpLemma [] [] `i.insert_nth_apply_succ_above)
         ","
         (Tactic.simpLemma
          []
          []
          (Term.paren "(" («term_∘_» (Term.cdot "·") "∘" (Term.cdot "·")) ")"))]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.paren "(" («term_∘_» (Term.cdot "·") "∘" (Term.cdot "·")) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∘_» (Term.cdot "·") "∘" (Term.cdot "·"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.cdot "·")
[PrettyPrinter.parenthesize] ...precedences are 90 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 90, term))
      (Term.cdot "·")
[PrettyPrinter.parenthesize] ...precedences are 91 >? 1024, (none, [anonymous]) <=? (some 90, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 90, (some 90, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i.insert_nth_apply_succ_above
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i.insert_nth_apply_same
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `MeasurableEquiv.pi_fin_succ_above_equiv_symm_apply
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine'
       "refine'"
       (Term.app
        `set_integral_congr
        [`measurable_set_Icc (Term.fun "fun" (Term.basicFun [`Θ `hΘ] [] "=>" (Term.hole "_")))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `set_integral_congr
       [`measurable_set_Icc (Term.fun "fun" (Term.basicFun [`Θ `hΘ] [] "=>" (Term.hole "_")))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun "fun" (Term.basicFun [`Θ `hΘ] [] "=>" (Term.hole "_")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hΘ
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `Θ
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      `measurable_set_Icc
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `set_integral_congr
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["["
        [(Tactic.simpLemma [] [] `torusIntegral)
         ","
         (Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `integral_smul)
         ","
         (Tactic.simpLemma [] [] `deriv_circle_map)
         ","
         (Tactic.simpLemma [] [] (Term.app `i.prod_univ_succ_above [(Term.hole "_")]))
         ","
         (Tactic.simpLemma [] [] `smul_smul)
         ","
         (Tactic.simpLemma [] [] `torusMap)
         ","
         (Tactic.simpLemma [] [] `circle_map_zero)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `circle_map_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `torusMap
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `smul_smul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `i.prod_univ_succ_above [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `i.prod_univ_succ_above
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `deriv_circle_map
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `integral_smul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `torusIntegral
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine'
       "refine'"
       (Term.app
        `set_integral_congr
        [`measurable_set_Icc (Term.fun "fun" (Term.basicFun [`θ `hθ] [] "=>" (Term.hole "_")))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `set_integral_congr
       [`measurable_set_Icc (Term.fun "fun" (Term.basicFun [`θ `hθ] [] "=>" (Term.hole "_")))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun "fun" (Term.basicFun [`θ `hθ] [] "=>" (Term.hole "_")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hθ
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `θ
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      `measurable_set_Icc
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `set_integral_congr
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `torusIntegral)
         ","
         (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `hem.map_eq)
         ","
         (Tactic.rwRule [] `set_integral_map_equiv)
         ","
         (Tactic.rwRule [] `heπ)
         ","
         (Tactic.rwRule [] `measure.volume_eq_prod)
         ","
         (Tactic.rwRule [] `set_integral_prod)
         ","
         (Tactic.rwRule [] `circle_integral_def_Icc)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `circle_integral_def_Icc
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `set_integral_prod
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `measure.volume_eq_prod
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `heπ
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `set_integral_map_equiv
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hem.map_eq
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `torusIntegral
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`heπ []]
         [(Term.typeSpec
           ":"
           («term_=_»
            (Set.Data.Set.Image.«term_⁻¹'_»
             `e
             " ⁻¹' "
             (Term.app
              `Icc
              [(num "0")
               (Term.fun
                "fun"
                (Term.basicFun
                 [(Term.hole "_")]
                 []
                 "=>"
                 («term_*_»
                  (num "2")
                  "*"
                  (Real.Analysis.SpecialFunctions.Trigonometric.Basic.real.pi "π"))))]))
            "="
            (LowerSet.Order.UpperLower.lower_set.prod
             (Term.app
              `Icc
              [(num "0")
               («term_*_»
                (num "2")
                "*"
                (Real.Analysis.SpecialFunctions.Trigonometric.Basic.real.pi "π"))])
             " ×ˢ "
             (Term.app
              `Icc
              [(Term.typeAscription
                "("
                (num "0")
                ":"
                [(MeasureTheory.Integral.TorusIntegral.«termℝⁿ» "ℝⁿ")]
                ")")
               (Term.fun
                "fun"
                (Term.basicFun
                 [(Term.hole "_")]
                 []
                 "=>"
                 («term_*_»
                  (num "2")
                  "*"
                  (Real.Analysis.SpecialFunctions.Trigonometric.Basic.real.pi "π"))))]))))]
         ":="
         (Term.app
          (Term.proj
           (Term.app
            (Term.proj
             (Term.proj
              (Term.app
               `OrderIso.piFinSuccAboveIso
               [(Term.fun
                 "fun"
                 (Term.basicFun [(Term.hole "_")] [] "=>" (Data.Real.Basic.termℝ "ℝ")))
                `i])
              "."
              `symm)
             "."
             `preimage_Icc)
            [(Term.hole "_") (Term.hole "_")])
           "."
           `trans)
          [(Term.app `Icc_prod_eq [(Term.hole "_") (Term.hole "_")])]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (Term.app
         (Term.proj
          (Term.proj
           (Term.app
            `OrderIso.piFinSuccAboveIso
            [(Term.fun "fun" (Term.basicFun [(Term.hole "_")] [] "=>" (Data.Real.Basic.termℝ "ℝ")))
             `i])
           "."
           `symm)
          "."
          `preimage_Icc)
         [(Term.hole "_") (Term.hole "_")])
        "."
        `trans)
       [(Term.app `Icc_prod_eq [(Term.hole "_") (Term.hole "_")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Icc_prod_eq [(Term.hole "_") (Term.hole "_")])
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
      `Icc_prod_eq
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `Icc_prod_eq [(Term.hole "_") (Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (Term.app
        (Term.proj
         (Term.proj
          (Term.app
           `OrderIso.piFinSuccAboveIso
           [(Term.fun "fun" (Term.basicFun [(Term.hole "_")] [] "=>" (Data.Real.Basic.termℝ "ℝ")))
            `i])
          "."
          `symm)
         "."
         `preimage_Icc)
        [(Term.hole "_") (Term.hole "_")])
       "."
       `trans)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       (Term.proj
        (Term.proj
         (Term.app
          `OrderIso.piFinSuccAboveIso
          [(Term.fun "fun" (Term.basicFun [(Term.hole "_")] [] "=>" (Data.Real.Basic.termℝ "ℝ")))
           `i])
         "."
         `symm)
        "."
        `preimage_Icc)
       [(Term.hole "_") (Term.hole "_")])
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
      (Term.proj
       (Term.proj
        (Term.app
         `OrderIso.piFinSuccAboveIso
         [(Term.fun "fun" (Term.basicFun [(Term.hole "_")] [] "=>" (Data.Real.Basic.termℝ "ℝ")))
          `i])
        "."
        `symm)
       "."
       `preimage_Icc)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj
       (Term.app
        `OrderIso.piFinSuccAboveIso
        [(Term.fun "fun" (Term.basicFun [(Term.hole "_")] [] "=>" (Data.Real.Basic.termℝ "ℝ"))) `i])
       "."
       `symm)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       `OrderIso.piFinSuccAboveIso
       [(Term.fun "fun" (Term.basicFun [(Term.hole "_")] [] "=>" (Data.Real.Basic.termℝ "ℝ"))) `i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.fun "fun" (Term.basicFun [(Term.hole "_")] [] "=>" (Data.Real.Basic.termℝ "ℝ")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Real.Basic.termℝ "ℝ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.fun "fun" (Term.basicFun [(Term.hole "_")] [] "=>" (Data.Real.Basic.termℝ "ℝ")))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `OrderIso.piFinSuccAboveIso
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `OrderIso.piFinSuccAboveIso
      [(Term.paren
        "("
        (Term.fun "fun" (Term.basicFun [(Term.hole "_")] [] "=>" (Data.Real.Basic.termℝ "ℝ")))
        ")")
       `i])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      (Term.proj
       (Term.proj
        (Term.paren
         "("
         (Term.app
          `OrderIso.piFinSuccAboveIso
          [(Term.paren
            "("
            (Term.fun "fun" (Term.basicFun [(Term.hole "_")] [] "=>" (Data.Real.Basic.termℝ "ℝ")))
            ")")
           `i])
         ")")
        "."
        `symm)
       "."
       `preimage_Icc)
      [(Term.hole "_") (Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Set.Data.Set.Image.«term_⁻¹'_»
        `e
        " ⁻¹' "
        (Term.app
         `Icc
         [(num "0")
          (Term.fun
           "fun"
           (Term.basicFun
            [(Term.hole "_")]
            []
            "=>"
            («term_*_»
             (num "2")
             "*"
             (Real.Analysis.SpecialFunctions.Trigonometric.Basic.real.pi "π"))))]))
       "="
       (LowerSet.Order.UpperLower.lower_set.prod
        (Term.app
         `Icc
         [(num "0")
          («term_*_»
           (num "2")
           "*"
           (Real.Analysis.SpecialFunctions.Trigonometric.Basic.real.pi "π"))])
        " ×ˢ "
        (Term.app
         `Icc
         [(Term.typeAscription
           "("
           (num "0")
           ":"
           [(MeasureTheory.Integral.TorusIntegral.«termℝⁿ» "ℝⁿ")]
           ")")
          (Term.fun
           "fun"
           (Term.basicFun
            [(Term.hole "_")]
            []
            "=>"
            («term_*_»
             (num "2")
             "*"
             (Real.Analysis.SpecialFunctions.Trigonometric.Basic.real.pi "π"))))])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (LowerSet.Order.UpperLower.lower_set.prod
       (Term.app
        `Icc
        [(num "0")
         («term_*_»
          (num "2")
          "*"
          (Real.Analysis.SpecialFunctions.Trigonometric.Basic.real.pi "π"))])
       " ×ˢ "
       (Term.app
        `Icc
        [(Term.typeAscription
          "("
          (num "0")
          ":"
          [(MeasureTheory.Integral.TorusIntegral.«termℝⁿ» "ℝⁿ")]
          ")")
         (Term.fun
          "fun"
          (Term.basicFun
           [(Term.hole "_")]
           []
           "=>"
           («term_*_»
            (num "2")
            "*"
            (Real.Analysis.SpecialFunctions.Trigonometric.Basic.real.pi "π"))))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Icc
       [(Term.typeAscription
         "("
         (num "0")
         ":"
         [(MeasureTheory.Integral.TorusIntegral.«termℝⁿ» "ℝⁿ")]
         ")")
        (Term.fun
         "fun"
         (Term.basicFun
          [(Term.hole "_")]
          []
          "=>"
          («term_*_»
           (num "2")
           "*"
           (Real.Analysis.SpecialFunctions.Trigonometric.Basic.real.pi "π"))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [(Term.hole "_")]
        []
        "=>"
        («term_*_» (num "2") "*" (Real.Analysis.SpecialFunctions.Trigonometric.Basic.real.pi "π"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_» (num "2") "*" (Real.Analysis.SpecialFunctions.Trigonometric.Basic.real.pi "π"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Real.Analysis.SpecialFunctions.Trigonometric.Basic.real.pi "π")
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.typeAscription
       "("
       (num "0")
       ":"
       [(MeasureTheory.Integral.TorusIntegral.«termℝⁿ» "ℝⁿ")]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (MeasureTheory.Integral.TorusIntegral.«termℝⁿ» "ℝⁿ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'MeasureTheory.Integral.TorusIntegral.«termℝⁿ»', expected 'MeasureTheory.Integral.TorusIntegral.termℝⁿ._@.MeasureTheory.Integral.TorusIntegral._hyg.158'
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
/-- Recurrent formula for `torus_integral`, see also `torus_integral_succ`. -/
  theorem
    torus_integral_succ_above
    { f : ℂⁿ⁺¹ → E } { c : ℂⁿ⁺¹ } { R : ℝⁿ⁺¹ } ( hf : TorusIntegrable f c R ) ( i : Fin n + 1 )
      :
        ∯ x in T( c , R ) , f x
          =
          ∮
            x
            in
            C(
            c i
            ,
            R i
            )
            ,
            ∯ y in T( c ∘ i . succAbove , R ∘ i . succAbove ) , f i . insertNth x y
    :=
      by
        set e : ℝ × ℝⁿ ≃ᵐ ℝⁿ⁺¹ := MeasurableEquiv.piFinSuccAboveEquiv fun _ => ℝ i . symm
          have
            hem
              : measure_preserving e
              :=
              volume_preserving_pi_fin_succ_above_equiv fun j : Fin n + 1 => ℝ i . symm _
          have
            heπ
              : e ⁻¹' Icc 0 fun _ => 2 * π = Icc 0 2 * π ×ˢ Icc ( 0 : ℝⁿ ) fun _ => 2 * π
              :=
              OrderIso.piFinSuccAboveIso fun _ => ℝ i . symm . preimage_Icc _ _ . trans
                Icc_prod_eq _ _
          rw
            [
              torusIntegral
                ,
                ← hem.map_eq
                ,
                set_integral_map_equiv
                ,
                heπ
                ,
                measure.volume_eq_prod
                ,
                set_integral_prod
                ,
                circle_integral_def_Icc
              ]
          ·
            refine' set_integral_congr measurable_set_Icc fun θ hθ => _
              simp
                only
                [
                  torusIntegral
                    ,
                    ← integral_smul
                    ,
                    deriv_circle_map
                    ,
                    i.prod_univ_succ_above _
                    ,
                    smul_smul
                    ,
                    torusMap
                    ,
                    circle_map_zero
                  ]
              refine' set_integral_congr measurable_set_Icc fun Θ hΘ => _
              simp
                only
                [
                  MeasurableEquiv.pi_fin_succ_above_equiv_symm_apply
                    ,
                    i.insert_nth_apply_same
                    ,
                    i.insert_nth_apply_succ_above
                    ,
                    ( · ∘ · )
                  ]
              congr 2
              simp
                only
                [
                  funext_iff
                    ,
                    i.forall_iff_succ_above
                    ,
                    circleMap
                    ,
                    Fin.insert_nth_apply_same
                    ,
                    eq_self_iff_true
                    ,
                    Fin.insert_nth_apply_succ_above
                    ,
                    imp_true_iff
                    ,
                    and_self_iff
                  ]
          ·
            have := hf.function_integrable
              rwa [ ← hem.integrable_on_comp_preimage e.measurable_embedding , heπ ] at this
#align torus_integral_succ_above torus_integral_succ_above

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "Recurrent formula for `torus_integral`, see also `torus_integral_succ_above`. -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `torus_integral_succ [])
      (Command.declSig
       [(Term.implicitBinder
         "{"
         [`f]
         [":" (Term.arrow (MeasureTheory.Integral.TorusIntegral.«termℂⁿ⁺¹» "ℂⁿ⁺¹") "→" `E)]
         "}")
        (Term.implicitBinder
         "{"
         [`c]
         [":" (MeasureTheory.Integral.TorusIntegral.«termℂⁿ⁺¹» "ℂⁿ⁺¹")]
         "}")
        (Term.implicitBinder
         "{"
         [`R]
         [":" (MeasureTheory.Integral.TorusIntegral.«termℝⁿ⁺¹» "ℝⁿ⁺¹")]
         "}")
        (Term.explicitBinder "(" [`hf] [":" (Term.app `TorusIntegrable [`f `c `R])] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (MeasureTheory.Integral.TorusIntegral.«term∯_inT(_,_),_»
          "∯"
          (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
          " in "
          "T("
          `c
          ", "
          `R
          ")"
          ", "
          (Term.app `f [`x]))
         "="
         (MeasureTheory.Integral.CircleIntegral.«term∮_inC(_,_),_»
          "∮"
          (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
          " in "
          "C("
          (Term.app `c [(num "0")])
          ", "
          (Term.app `R [(num "0")])
          ")"
          ", "
          (MeasureTheory.Integral.TorusIntegral.«term∯_inT(_,_),_»
           "∯"
           (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `y) []))
           " in "
           "T("
           («term_∘_» `c "∘" `Fin.succ)
           ", "
           («term_∘_» `R "∘" `Fin.succ)
           ")"
           ", "
           (Term.app `f [(Term.app `Fin.cons [`x `y])]))))))
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
             ["using" (Term.app `torus_integral_succ_above [`hf (num "0")])]))])))
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
            ["using" (Term.app `torus_integral_succ_above [`hf (num "0")])]))])))
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
        ["using" (Term.app `torus_integral_succ_above [`hf (num "0")])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `torus_integral_succ_above [`hf (num "0")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hf
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `torus_integral_succ_above
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (MeasureTheory.Integral.TorusIntegral.«term∯_inT(_,_),_»
        "∯"
        (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
        " in "
        "T("
        `c
        ", "
        `R
        ")"
        ", "
        (Term.app `f [`x]))
       "="
       (MeasureTheory.Integral.CircleIntegral.«term∮_inC(_,_),_»
        "∮"
        (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
        " in "
        "C("
        (Term.app `c [(num "0")])
        ", "
        (Term.app `R [(num "0")])
        ")"
        ", "
        (MeasureTheory.Integral.TorusIntegral.«term∯_inT(_,_),_»
         "∯"
         (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `y) []))
         " in "
         "T("
         («term_∘_» `c "∘" `Fin.succ)
         ", "
         («term_∘_» `R "∘" `Fin.succ)
         ")"
         ", "
         (Term.app `f [(Term.app `Fin.cons [`x `y])]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (MeasureTheory.Integral.CircleIntegral.«term∮_inC(_,_),_»
       "∮"
       (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
       " in "
       "C("
       (Term.app `c [(num "0")])
       ", "
       (Term.app `R [(num "0")])
       ")"
       ", "
       (MeasureTheory.Integral.TorusIntegral.«term∯_inT(_,_),_»
        "∯"
        (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `y) []))
        " in "
        "T("
        («term_∘_» `c "∘" `Fin.succ)
        ", "
        («term_∘_» `R "∘" `Fin.succ)
        ")"
        ", "
        (Term.app `f [(Term.app `Fin.cons [`x `y])])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (MeasureTheory.Integral.TorusIntegral.«term∯_inT(_,_),_»
       "∯"
       (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `y) []))
       " in "
       "T("
       («term_∘_» `c "∘" `Fin.succ)
       ", "
       («term_∘_» `R "∘" `Fin.succ)
       ")"
       ", "
       (Term.app `f [(Term.app `Fin.cons [`x `y])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `f [(Term.app `Fin.cons [`x `y])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Fin.cons [`x `y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Fin.cons
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `Fin.cons [`x `y]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∘_» `R "∘" `Fin.succ)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Fin.succ
[PrettyPrinter.parenthesize] ...precedences are 90 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 90, term))
      `R
[PrettyPrinter.parenthesize] ...precedences are 91 >? 1024, (none, [anonymous]) <=? (some 90, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 90, (some 90, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∘_» `c "∘" `Fin.succ)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Fin.succ
[PrettyPrinter.parenthesize] ...precedences are 90 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 90, term))
      `c
[PrettyPrinter.parenthesize] ...precedences are 91 >? 1024, (none, [anonymous]) <=? (some 90, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 90, (some 90, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `R [(num "0")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `R
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
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
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (MeasureTheory.Integral.TorusIntegral.«term∯_inT(_,_),_»
       "∯"
       (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
       " in "
       "T("
       `c
       ", "
       `R
       ")"
       ", "
       (Term.app `f [`x]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `f [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `R
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `c
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 0, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (MeasureTheory.Integral.TorusIntegral.«term∯_inT(_,_),_»
      "∯"
      (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
      " in "
      "T("
      `c
      ", "
      `R
      ")"
      ", "
      (Term.app `f [`x]))
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 0, term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `TorusIntegrable [`f `c `R])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `R
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `c
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `TorusIntegrable
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.implicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.implicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.implicitBinder', expected 'Lean.Parser.Term.explicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.implicitBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (MeasureTheory.Integral.TorusIntegral.«termℝⁿ⁺¹» "ℝⁿ⁺¹")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'MeasureTheory.Integral.TorusIntegral.«termℝⁿ⁺¹»', expected 'MeasureTheory.Integral.TorusIntegral.termℝⁿ⁺¹._@.MeasureTheory.Integral.TorusIntegral._hyg.232'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.implicitBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/-- Recurrent formula for `torus_integral`, see also `torus_integral_succ_above`. -/
  theorem
    torus_integral_succ
    { f : ℂⁿ⁺¹ → E } { c : ℂⁿ⁺¹ } { R : ℝⁿ⁺¹ } ( hf : TorusIntegrable f c R )
      :
        ∯ x in T( c , R ) , f x
          =
          ∮ x in C( c 0 , R 0 ) , ∯ y in T( c ∘ Fin.succ , R ∘ Fin.succ ) , f Fin.cons x y
    := by simpa using torus_integral_succ_above hf 0
#align torus_integral_succ torus_integral_succ

