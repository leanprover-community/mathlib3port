/-
Copyright (c) 2022 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov

! This file was ported from Lean 3 source module analysis.complex.abs_max
! leanprover-community/mathlib commit 6d0adfa76594f304b4650d098273d4366edeb61b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.Complex.CauchyIntegral
import Mathbin.Analysis.NormedSpace.Completion
import Mathbin.Analysis.NormedSpace.Extr
import Mathbin.Topology.Algebra.Order.ExtrClosure

/-!
# Maximum modulus principle

In this file we prove several versions of the maximum modulus principle. There are several
statements that can be called "the maximum modulus principle" for maps between normed complex
spaces. They differ by assumptions on the domain (any space, a nontrivial space, a finite
dimensional space), assumptions on the codomain (any space, a strictly convex space), and by
conclusion (either equality of norms or of the values of the function).

## Main results

### Theorems for any codomain

Consider a function `f : E → F` that is complex differentiable on a set `s`, is continuous on its
closure, and `‖f x‖` has a maximum on `s` at `c`. We prove the following theorems.

- `complex.norm_eq_on_closed_ball_of_is_max_on`: if `s = metric.ball c r`, then `‖f x‖ = ‖f c‖` for
  any `x` from the corresponding closed ball;

- `complex.norm_eq_norm_of_is_max_on_of_ball_subset`: if `metric.ball c (dist w c) ⊆ s`, then
  `‖f w‖ = ‖f c‖`;

- `complex.norm_eq_on_of_is_preconnected_of_is_max_on`: if `U` is an open (pre)connected set, `f` is
  complex differentiable on `U`, and `‖f x‖` has a maximum on `U` at `c ∈ U`, then `‖f x‖ = ‖f c‖`
  for all `x ∈ U`;

- `complex.norm_eq_on_closure_of_is_preconnected_of_is_max_on`: if `s` is open and (pre)connected
  and `c ∈ s`, then `‖f x‖ = ‖f c‖` for all `x ∈ closure s`;

- `complex.norm_eventually_eq_of_is_local_max`: if `f` is complex differentiable in a neighborhood
  of `c` and `‖f x‖` has a local maximum at `c`, then `‖f x‖` is locally a constant in a
  neighborhood of `c`.

### Theorems for a strictly convex codomain

If the codomain `F` is a strictly convex space, then in the lemmas from the previous section we can
prove `f w = f c` instead of `‖f w‖ = ‖f c‖`, see
`complex.eq_on_of_is_preconnected_of_is_max_on_norm`,
`complex.eq_on_closure_of_is_preconnected_of_is_max_on_norm`,
`complex.eq_of_is_max_on_of_ball_subset`, `complex.eq_on_closed_ball_of_is_max_on_norm`, and
`complex.eventually_eq_of_is_local_max_norm`.

### Values on the frontier

Finally, we prove some corollaries that relate the (norm of the) values of a function on a set to
its values on the frontier of the set. All these lemmas assume that `E` is a nontrivial space.  In
this section `f g : E → F` are functions that are complex differentiable on a bounded set `s` and
are continuous on its closure. We prove the following theorems.

- `complex.exists_mem_frontier_is_max_on_norm`: If `E` is a finite dimensional space and `s` is a
  nonempty bounded set, then there exists a point `z ∈ frontier s` such that `λ z, ‖f z‖` takes it
  maximum value on `closure s` at `z`.

- `complex.norm_le_of_forall_mem_frontier_norm_le`: if `‖f z‖ ≤ C` for all `z ∈ frontier s`, then
  `‖f z‖ ≤ C` for all `z ∈ s`; note that this theorem does not require `E` to be a finite
  dimensional space.

- `complex.eq_on_closure_of_eq_on_frontier`: if `f x = g x` on the frontier of `s`, then `f x = g x`
  on `closure s`;

- `complex.eq_on_of_eq_on_frontier`: if `f x = g x` on the frontier of `s`, then `f x = g x`
  on `s`.

## Tags

maximum modulus principle, complex analysis
-/


open TopologicalSpace Metric Set Filter Asymptotics Function MeasureTheory AffineMap

open TopologicalSpace Filter Nnreal Real

universe u v w

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E] {F : Type v} [NormedAddCommGroup F]
  [NormedSpace ℂ F]

-- mathport name: «expr ̂»
local postfix:100 "̂" => UniformSpace.Completion

namespace Complex

/-!
### Auxiliary lemmas

We split the proof into a series of lemmas. First we prove the principle for a function `f : ℂ → F`
with an additional assumption that `F` is a complete space, then drop unneeded assumptions one by
one.

The lemmas with names `*_auxₙ` are considered to be private and should not be used outside of this
file.
-/


theorem norm_max_aux₁ [CompleteSpace F] {f : ℂ → F} {z w : ℂ}
    (hd : DiffContOnCl ℂ f (ball z (dist w z)))
    (hz : IsMaxOn (norm ∘ f) (closedBall z (dist w z)) z) : ‖f w‖ = ‖f z‖ :=
  by
  -- Consider a circle of radius `r = dist w z`.
  set r : ℝ := dist w z
  have hw : w ∈ closed_ball z r := mem_closed_ball.2 le_rfl
  -- Assume the converse. Since `‖f w‖ ≤ ‖f z‖`, we have `‖f w‖ < ‖f z‖`.
  refine' (is_max_on_iff.1 hz _ hw).antisymm (not_lt.1 _)
  rintro hw_lt : ‖f w‖ < ‖f z‖
  have hr : 0 < r := dist_pos.2 (ne_of_apply_ne (norm ∘ f) hw_lt.ne)
  -- Due to Cauchy integral formula, it suffices to prove the following inequality.
  suffices ‖∮ ζ in C(z, r), (ζ - z)⁻¹ • f ζ‖ < 2 * π * ‖f z‖
    by
    refine' this.ne _
    have A : (∮ ζ in C(z, r), (ζ - z)⁻¹ • f ζ) = (2 * π * I : ℂ) • f z :=
      hd.circle_integral_sub_inv_smul (mem_ball_self hr)
    simp [A, norm_smul, real.pi_pos.le]
  suffices ‖∮ ζ in C(z, r), (ζ - z)⁻¹ • f ζ‖ < 2 * π * r * (‖f z‖ / r) by
    rwa [mul_assoc, mul_div_cancel' _ hr.ne'] at this
  /- This inequality is true because `‖(ζ - z)⁻¹ • f ζ‖ ≤ ‖f z‖ / r` for all `ζ` on the circle and
    this inequality is strict at `ζ = w`. -/
  have hsub : sphere z r ⊆ closed_ball z r := sphere_subset_closed_ball
  refine' circleIntegral.norm_integral_lt_of_norm_le_const_of_lt hr _ _ ⟨w, rfl, _⟩
  show ContinuousOn (fun ζ : ℂ => (ζ - z)⁻¹ • f ζ) (sphere z r)
  · refine'
      ((continuous_on_id.sub continuous_on_const).inv₀ _).smul (hd.continuous_on_ball.mono hsub)
    exact fun ζ hζ => sub_ne_zero.2 (ne_of_mem_sphere hζ hr.ne')
  show ∀ ζ ∈ sphere z r, ‖(ζ - z)⁻¹ • f ζ‖ ≤ ‖f z‖ / r
  · rintro ζ (hζ : abs (ζ - z) = r)
    rw [le_div_iff hr, norm_smul, norm_inv, norm_eq_abs, hζ, mul_comm, mul_inv_cancel_left₀ hr.ne']
    exact hz (hsub hζ)
  show ‖(w - z)⁻¹ • f w‖ < ‖f z‖ / r
  · rw [norm_smul, norm_inv, norm_eq_abs, ← div_eq_inv_mul]
    exact (div_lt_div_right hr).2 hw_lt
#align complex.norm_max_aux₁ Complex.norm_max_aux₁

/-!
Now we drop the assumption `complete_space F` by embedding `F` into its completion.
-/


/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `norm_max_aux₂ [])
      (Command.declSig
       [(Term.implicitBinder "{" [`f] [":" (Term.arrow (Data.Complex.Basic.termℂ "ℂ") "→" `F)] "}")
        (Term.implicitBinder "{" [`z `w] [":" (Data.Complex.Basic.termℂ "ℂ")] "}")
        (Term.explicitBinder
         "("
         [`hd]
         [":"
          (Term.app
           `DiffContOnCl
           [(Data.Complex.Basic.termℂ "ℂ") `f (Term.app `ball [`z (Term.app `dist [`w `z])])])]
         []
         ")")
        (Term.explicitBinder
         "("
         [`hz]
         [":"
          (Term.app
           `IsMaxOn
           [(«term_∘_» `norm "∘" `f) (Term.app `closedBall [`z (Term.app `dist [`w `z])]) `z])]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Analysis.Normed.Group.Basic.«term‖_‖» "‖" (Term.app `f [`w]) "‖")
         "="
         (Analysis.Normed.Group.Basic.«term‖_‖» "‖" (Term.app `f [`z]) "‖"))))
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
              (Topology.Algebra.Module.Basic.«term_→L[_]_»
               `F
               " →L["
               (Data.Complex.Basic.termℂ "ℂ")
               "] "
               (Analysis.Complex.AbsMax.«term_̂» `F "̂"))]
             ":="
             `UniformSpace.Completion.toComplL
             []))
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`he []]
              [(Term.typeSpec
                ":"
                (Term.forall
                 "∀"
                 [`x]
                 []
                 ","
                 («term_=_»
                  (Analysis.Normed.Group.Basic.«term‖_‖» "‖" (Term.app `e [`x]) "‖")
                  "="
                  (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖"))))]
              ":="
              `UniformSpace.Completion.norm_coe)))
           []
           (Mathlib.Tactic.replace'
            "replace"
            [`hz []]
            [(Term.typeSpec
              ":"
              (Term.app
               `IsMaxOn
               [(«term_∘_» `norm "∘" («term_∘_» `e "∘" `f))
                (Term.app `closed_ball [`z (Term.app `dist [`w `z])])
                `z]))])
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
               ["only"]
               [(Tactic.simpArgs
                 "["
                 [(Tactic.simpLemma [] [] `IsMaxOn)
                  ","
                  (Tactic.simpLemma
                   []
                   []
                   (Term.paren "(" («term_∘_» (Term.cdot "·") "∘" (Term.cdot "·")) ")"))
                  ","
                  (Tactic.simpLemma [] [] `he)]
                 "]")]
               ["using" `hz]))])
           []
           (Std.Tactic.Simpa.simpa
            "simpa"
            []
            []
            (Std.Tactic.Simpa.simpaArgsRest
             []
             []
             ["only"]
             [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `he)] "]")]
             ["using"
              (Term.app
               `norm_max_aux₁
               [(Term.app `e.differentiable.comp_diff_cont_on_cl [`hd]) `hz])]))])))
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
             (Topology.Algebra.Module.Basic.«term_→L[_]_»
              `F
              " →L["
              (Data.Complex.Basic.termℂ "ℂ")
              "] "
              (Analysis.Complex.AbsMax.«term_̂» `F "̂"))]
            ":="
            `UniformSpace.Completion.toComplL
            []))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`he []]
             [(Term.typeSpec
               ":"
               (Term.forall
                "∀"
                [`x]
                []
                ","
                («term_=_»
                 (Analysis.Normed.Group.Basic.«term‖_‖» "‖" (Term.app `e [`x]) "‖")
                 "="
                 (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖"))))]
             ":="
             `UniformSpace.Completion.norm_coe)))
          []
          (Mathlib.Tactic.replace'
           "replace"
           [`hz []]
           [(Term.typeSpec
             ":"
             (Term.app
              `IsMaxOn
              [(«term_∘_» `norm "∘" («term_∘_» `e "∘" `f))
               (Term.app `closed_ball [`z (Term.app `dist [`w `z])])
               `z]))])
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
              ["only"]
              [(Tactic.simpArgs
                "["
                [(Tactic.simpLemma [] [] `IsMaxOn)
                 ","
                 (Tactic.simpLemma
                  []
                  []
                  (Term.paren "(" («term_∘_» (Term.cdot "·") "∘" (Term.cdot "·")) ")"))
                 ","
                 (Tactic.simpLemma [] [] `he)]
                "]")]
              ["using" `hz]))])
          []
          (Std.Tactic.Simpa.simpa
           "simpa"
           []
           []
           (Std.Tactic.Simpa.simpaArgsRest
            []
            []
            ["only"]
            [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `he)] "]")]
            ["using"
             (Term.app
              `norm_max_aux₁
              [(Term.app `e.differentiable.comp_diff_cont_on_cl [`hd]) `hz])]))])))
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
        [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `he)] "]")]
        ["using"
         (Term.app `norm_max_aux₁ [(Term.app `e.differentiable.comp_diff_cont_on_cl [`hd]) `hz])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `norm_max_aux₁ [(Term.app `e.differentiable.comp_diff_cont_on_cl [`hd]) `hz])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hz
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `e.differentiable.comp_diff_cont_on_cl [`hd])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hd
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `e.differentiable.comp_diff_cont_on_cl
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `e.differentiable.comp_diff_cont_on_cl [`hd])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `norm_max_aux₁
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `he
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
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
          ["only"]
          [(Tactic.simpArgs
            "["
            [(Tactic.simpLemma [] [] `IsMaxOn)
             ","
             (Tactic.simpLemma
              []
              []
              (Term.paren "(" («term_∘_» (Term.cdot "·") "∘" (Term.cdot "·")) ")"))
             ","
             (Tactic.simpLemma [] [] `he)]
            "]")]
          ["using" `hz]))])
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
          [(Tactic.simpLemma [] [] `IsMaxOn)
           ","
           (Tactic.simpLemma
            []
            []
            (Term.paren "(" («term_∘_» (Term.cdot "·") "∘" (Term.cdot "·")) ")"))
           ","
           (Tactic.simpLemma [] [] `he)]
          "]")]
        ["using" `hz]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hz
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `he
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
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
      `IsMaxOn
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.replace'
       "replace"
       [`hz []]
       [(Term.typeSpec
         ":"
         (Term.app
          `IsMaxOn
          [(«term_∘_» `norm "∘" («term_∘_» `e "∘" `f))
           (Term.app `closed_ball [`z (Term.app `dist [`w `z])])
           `z]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `IsMaxOn
       [(«term_∘_» `norm "∘" («term_∘_» `e "∘" `f))
        (Term.app `closed_ball [`z (Term.app `dist [`w `z])])
        `z])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `z
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `closed_ball [`z (Term.app `dist [`w `z])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `dist [`w `z])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `z
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `w
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `dist
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `dist [`w `z]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `z
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `closed_ball
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `closed_ball [`z (Term.paren "(" (Term.app `dist [`w `z]) ")")])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_∘_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_∘_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      («term_∘_» `norm "∘" («term_∘_» `e "∘" `f))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∘_» `e "∘" `f)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 90 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 90, term))
      `e
[PrettyPrinter.parenthesize] ...precedences are 91 >? 1024, (none, [anonymous]) <=? (some 90, term)
[PrettyPrinter.parenthesize] ...precedences are 90 >? 90, (some 90, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 90, term))
      `norm
[PrettyPrinter.parenthesize] ...precedences are 91 >? 1024, (none, [anonymous]) <=? (some 90, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 90, (some 90, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_∘_» `norm "∘" («term_∘_» `e "∘" `f))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `IsMaxOn
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`he []]
         [(Term.typeSpec
           ":"
           (Term.forall
            "∀"
            [`x]
            []
            ","
            («term_=_»
             (Analysis.Normed.Group.Basic.«term‖_‖» "‖" (Term.app `e [`x]) "‖")
             "="
             (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖"))))]
         ":="
         `UniformSpace.Completion.norm_coe)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `UniformSpace.Completion.norm_coe
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.forall
       "∀"
       [`x]
       []
       ","
       («term_=_»
        (Analysis.Normed.Group.Basic.«term‖_‖» "‖" (Term.app `e [`x]) "‖")
        "="
        (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Analysis.Normed.Group.Basic.«term‖_‖» "‖" (Term.app `e [`x]) "‖")
       "="
       (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Analysis.Normed.Group.Basic.«term‖_‖» "‖" (Term.app `e [`x]) "‖")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `e [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `e
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.set
       "set"
       []
       (Mathlib.Tactic.setArgsRest
        `e
        [":"
         (Topology.Algebra.Module.Basic.«term_→L[_]_»
          `F
          " →L["
          (Data.Complex.Basic.termℂ "ℂ")
          "] "
          (Analysis.Complex.AbsMax.«term_̂» `F "̂"))]
        ":="
        `UniformSpace.Completion.toComplL
        []))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `UniformSpace.Completion.toComplL
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Topology.Algebra.Module.Basic.«term_→L[_]_»
       `F
       " →L["
       (Data.Complex.Basic.termℂ "ℂ")
       "] "
       (Analysis.Complex.AbsMax.«term_̂» `F "̂"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.Complex.AbsMax.«term_̂» `F "̂")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.Complex.AbsMax.«term_̂»', expected 'Analysis.Complex.AbsMax.term_̂._@.Analysis.Complex.AbsMax._hyg.8'
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
  norm_max_aux₂
  { f : ℂ → F }
      { z w : ℂ }
      ( hd : DiffContOnCl ℂ f ball z dist w z )
      ( hz : IsMaxOn norm ∘ f closedBall z dist w z z )
    : ‖ f w ‖ = ‖ f z ‖
  :=
    by
      set e : F →L[ ℂ ] F ̂ := UniformSpace.Completion.toComplL
        have he : ∀ x , ‖ e x ‖ = ‖ x ‖ := UniformSpace.Completion.norm_coe
        replace hz : IsMaxOn norm ∘ e ∘ f closed_ball z dist w z z
        · simpa only [ IsMaxOn , ( · ∘ · ) , he ] using hz
        simpa only [ he ] using norm_max_aux₁ e.differentiable.comp_diff_cont_on_cl hd hz
#align complex.norm_max_aux₂ Complex.norm_max_aux₂

/-!
Then we replace the assumption `is_max_on (norm ∘ f) (closed_ball z r) z` with a seemingly weaker
assumption `is_max_on (norm ∘ f) (ball z r) z`.
-/


theorem norm_max_aux₃ {f : ℂ → F} {z w : ℂ} {r : ℝ} (hr : dist w z = r)
    (hd : DiffContOnCl ℂ f (ball z r)) (hz : IsMaxOn (norm ∘ f) (ball z r) z) : ‖f w‖ = ‖f z‖ :=
  by
  subst r
  rcases eq_or_ne w z with (rfl | hne); · rfl
  rw [← dist_ne_zero] at hne
  exact norm_max_aux₂ hd (closure_ball z hne ▸ hz.closure hd.continuous_on.norm)
#align complex.norm_max_aux₃ Complex.norm_max_aux₃

/-!
### Maximum modulus principle for any codomain

If we do not assume that the codomain is a strictly convex space, then we can only claim that the
**norm** `‖f x‖` is locally constant.
-/


/-!
Finally, we generalize the theorem from a disk in `ℂ` to a closed ball in any normed space.
-/


/-- **Maximum modulus principle** on a closed ball: if `f : E → F` is continuous on a closed ball,
is complex differentiable on the corresponding open ball, and the norm `‖f w‖` takes its maximum
value on the open ball at its center, then the norm `‖f w‖` is constant on the closed ball.  -/
theorem norm_eq_on_closed_ball_of_is_max_on {f : E → F} {z : E} {r : ℝ}
    (hd : DiffContOnCl ℂ f (ball z r)) (hz : IsMaxOn (norm ∘ f) (ball z r) z) :
    EqOn (norm ∘ f) (const E ‖f z‖) (closedBall z r) :=
  by
  intro w hw
  rw [mem_closed_ball, dist_comm] at hw
  rcases eq_or_ne z w with (rfl | hne)
  · rfl
  set e : ℂ → E := line_map z w
  have hde : Differentiable ℂ e := (differentiable_id.smul_const (w - z)).AddConst z
  suffices ‖(f ∘ e) (1 : ℂ)‖ = ‖(f ∘ e) (0 : ℂ)‖ by simpa [e]
  have hr : dist (1 : ℂ) 0 = 1 := by simp
  have hball : maps_to e (ball 0 1) (ball z r) :=
    by
    refine'
      ((lipschitz_with_line_map z w).maps_to_ball (mt nndist_eq_zero.1 hne) 0 1).mono subset.rfl _
    simpa only [line_map_apply_zero, mul_one, coe_nndist] using ball_subset_ball hw
  exact
    norm_max_aux₃ hr (hd.comp hde.diff_cont_on_cl hball)
      (hz.comp_maps_to hball (line_map_apply_zero z w))
#align complex.norm_eq_on_closed_ball_of_is_max_on Complex.norm_eq_on_closed_ball_of_is_max_on

/-- **Maximum modulus principle**: if `f : E → F` is complex differentiable on a set `s`, the norm
of `f` takes it maximum on `s` at `z`, and `w` is a point such that the closed ball with center `z`
and radius `dist w z` is included in `s`, then `‖f w‖ = ‖f z‖`. -/
theorem norm_eq_norm_of_is_max_on_of_ball_subset {f : E → F} {s : Set E} {z w : E}
    (hd : DiffContOnCl ℂ f s) (hz : IsMaxOn (norm ∘ f) s z) (hsub : ball z (dist w z) ⊆ s) :
    ‖f w‖ = ‖f z‖ :=
  norm_eq_on_closed_ball_of_is_max_on (hd.mono hsub) (hz.on_subset hsub) (mem_closed_ball.2 le_rfl)
#align
  complex.norm_eq_norm_of_is_max_on_of_ball_subset Complex.norm_eq_norm_of_is_max_on_of_ball_subset

/-- **Maximum modulus principle**: if `f : E → F` is complex differentiable in a neighborhood of `c`
and the norm `‖f z‖` has a local maximum at `c`, then `‖f z‖` is locally constant in a neighborhood
of `c`. -/
theorem norm_eventually_eq_of_is_local_max {f : E → F} {c : E}
    (hd : ∀ᶠ z in 𝓝 c, DifferentiableAt ℂ f z) (hc : IsLocalMax (norm ∘ f) c) :
    ∀ᶠ y in 𝓝 c, ‖f y‖ = ‖f c‖ :=
  by
  rcases nhds_basis_closed_ball.eventually_iff.1 (hd.and hc) with ⟨r, hr₀, hr⟩
  exact
    nhds_basis_closed_ball.eventually_iff.2
      ⟨r, hr₀,
        norm_eq_on_closed_ball_of_is_max_on
          (DifferentiableOn.diff_cont_on_cl fun x hx =>
            (hr <| closure_ball_subset_closed_ball hx).1.DifferentiableWithinAt)
          fun x hx => (hr <| ball_subset_closed_ball hx).2⟩
#align complex.norm_eventually_eq_of_is_local_max Complex.norm_eventually_eq_of_is_local_max

theorem is_open_set_of_mem_nhds_and_is_max_on_norm {f : E → F} {s : Set E}
    (hd : DifferentiableOn ℂ f s) : IsOpen { z | s ∈ 𝓝 z ∧ IsMaxOn (norm ∘ f) s z } :=
  by
  refine' is_open_iff_mem_nhds.2 fun z hz => (eventually_eventually_nhds.2 hz.1).And _
  replace hd : ∀ᶠ w in 𝓝 z, DifferentiableAt ℂ f w; exact hd.eventually_differentiable_at hz.1
  exact
    (norm_eventually_eq_of_is_local_max hd <| hz.2.IsLocalMax hz.1).mono fun x hx y hy =>
      le_trans (hz.2 hy) hx.ge
#align
  complex.is_open_set_of_mem_nhds_and_is_max_on_norm Complex.is_open_set_of_mem_nhds_and_is_max_on_norm

/-- **Maximum modulus principle** on a connected set. Let `U` be a (pre)connected open set in a
complex normed space. Let `f : E → F` be a function that is complex differentiable on `U`. Suppose
that `‖f x‖` takes its maximum value on `U` at `c ∈ U`. Then `‖f x‖ = ‖f c‖` for all `x ∈ U`. -/
theorem norm_eq_on_of_is_preconnected_of_is_max_on {f : E → F} {U : Set E} {c : E}
    (hc : IsPreconnected U) (ho : IsOpen U) (hd : DifferentiableOn ℂ f U) (hcU : c ∈ U)
    (hm : IsMaxOn (norm ∘ f) U c) : EqOn (norm ∘ f) (const E ‖f c‖) U :=
  by
  set V := U ∩ { z | IsMaxOn (norm ∘ f) U z }
  have hV : ∀ x ∈ V, ‖f x‖ = ‖f c‖ := fun x hx => le_antisymm (hm hx.1) (hx.2 hcU)
  suffices : U ⊆ V
  exact fun x hx => hV x (this hx)
  have hVo : IsOpen V := by
    simpa only [ho.mem_nhds_iff, set_of_and, set_of_mem_eq] using
      is_open_set_of_mem_nhds_and_is_max_on_norm hd
  have hVne : (U ∩ V).Nonempty := ⟨c, hcU, hcU, hm⟩
  set W := U ∩ { z | ‖f z‖ ≠ ‖f c‖ }
  have hWo : IsOpen W := hd.continuous_on.norm.preimage_open_of_open ho is_open_ne
  have hdVW : Disjoint V W := disjoint_left.mpr fun x hxV hxW => hxW.2 (hV x hxV)
  have hUVW : U ⊆ V ∪ W := fun x hx =>
    (eq_or_ne ‖f x‖ ‖f c‖).imp (fun h => ⟨hx, fun y hy => (hm hy).out.trans_eq h.symm⟩)
      (And.intro hx)
  exact hc.subset_left_of_subset_union hVo hWo hdVW hUVW hVne
#align
  complex.norm_eq_on_of_is_preconnected_of_is_max_on Complex.norm_eq_on_of_is_preconnected_of_is_max_on

/-- **Maximum modulus principle** on a connected set. Let `U` be a (pre)connected open set in a
complex normed space.  Let `f : E → F` be a function that is complex differentiable on `U` and is
continuous on its closure. Suppose that `‖f x‖` takes its maximum value on `U` at `c ∈ U`. Then
`‖f x‖ = ‖f c‖` for all `x ∈ closure U`. -/
theorem norm_eq_on_closure_of_is_preconnected_of_is_max_on {f : E → F} {U : Set E} {c : E}
    (hc : IsPreconnected U) (ho : IsOpen U) (hd : DiffContOnCl ℂ f U) (hcU : c ∈ U)
    (hm : IsMaxOn (norm ∘ f) U c) : EqOn (norm ∘ f) (const E ‖f c‖) (closure U) :=
  (norm_eq_on_of_is_preconnected_of_is_max_on hc ho hd.DifferentiableOn hcU hm).of_subset_closure
    hd.ContinuousOn.norm continuous_on_const subset_closure Subset.rfl
#align
  complex.norm_eq_on_closure_of_is_preconnected_of_is_max_on Complex.norm_eq_on_closure_of_is_preconnected_of_is_max_on

section StrictConvex

/-!
### The case of a strictly convex codomain

If the codomain `F` is a strictly convex space, then we can claim equalities like `f w = f z`
instead of `‖f w‖ = ‖f z‖`.

Instead of repeating the proof starting with lemmas about integrals, we apply a corresponding lemma
above twice: for `f` and for `λ x, f x + f c`.  Then we have `‖f w‖ = ‖f z‖` and
`‖f w + f z‖ = ‖f z + f z‖`, thus `‖f w + f z‖ = ‖f w‖ + ‖f z‖`. This is only possible if
`f w = f z`, see `eq_of_norm_eq_of_norm_add_eq`.
-/


variable [StrictConvexSpace ℝ F]

/-- **Maximum modulus principle** on a connected set. Let `U` be a (pre)connected open set in a
complex normed space.  Let `f : E → F` be a function that is complex differentiable on `U`. Suppose
that `‖f x‖` takes its maximum value on `U` at `c ∈ U`. Then `f x = f c` for all `x ∈ U`.

TODO: change assumption from `is_max_on` to `is_local_max`. -/
theorem eq_on_of_is_preconnected_of_is_max_on_norm {f : E → F} {U : Set E} {c : E}
    (hc : IsPreconnected U) (ho : IsOpen U) (hd : DifferentiableOn ℂ f U) (hcU : c ∈ U)
    (hm : IsMaxOn (norm ∘ f) U c) : EqOn f (const E (f c)) U := fun x hx =>
  have H₁ : ‖f x‖ = ‖f c‖ := norm_eq_on_of_is_preconnected_of_is_max_on hc ho hd hcU hm hx
  have H₂ : ‖f x + f c‖ = ‖f c + f c‖ :=
    norm_eq_on_of_is_preconnected_of_is_max_on hc ho (hd.AddConst _) hcU hm.norm_add_self hx
  eq_of_norm_eq_of_norm_add_eq H₁ <| by simp only [H₂, same_ray.rfl.norm_add, H₁]
#align
  complex.eq_on_of_is_preconnected_of_is_max_on_norm Complex.eq_on_of_is_preconnected_of_is_max_on_norm

/-- **Maximum modulus principle** on a connected set. Let `U` be a (pre)connected open set in a
complex normed space.  Let `f : E → F` be a function that is complex differentiable on `U` and is
continuous on its closure. Suppose that `‖f x‖` takes its maximum value on `U` at `c ∈ U`. Then
`f x = f c` for all `x ∈ closure U`. -/
theorem eq_on_closure_of_is_preconnected_of_is_max_on_norm {f : E → F} {U : Set E} {c : E}
    (hc : IsPreconnected U) (ho : IsOpen U) (hd : DiffContOnCl ℂ f U) (hcU : c ∈ U)
    (hm : IsMaxOn (norm ∘ f) U c) : EqOn f (const E (f c)) (closure U) :=
  (eq_on_of_is_preconnected_of_is_max_on_norm hc ho hd.DifferentiableOn hcU hm).of_subset_closure
    hd.ContinuousOn continuous_on_const subset_closure Subset.rfl
#align
  complex.eq_on_closure_of_is_preconnected_of_is_max_on_norm Complex.eq_on_closure_of_is_preconnected_of_is_max_on_norm

/-- **Maximum modulus principle**. Let `f : E → F` be a function between complex normed spaces.
Suppose that the codomain `F` is a strictly convex space, `f` is complex differentiable on a set
`s`, `f` is continuous on the closure of `s`, the norm of `f` takes it maximum on `s` at `z`, and
`w` is a point such that the closed ball with center `z` and radius `dist w z` is included in `s`,
then `f w = f z`. -/
theorem eq_of_is_max_on_of_ball_subset {f : E → F} {s : Set E} {z w : E} (hd : DiffContOnCl ℂ f s)
    (hz : IsMaxOn (norm ∘ f) s z) (hsub : ball z (dist w z) ⊆ s) : f w = f z :=
  have H₁ : ‖f w‖ = ‖f z‖ := norm_eq_norm_of_is_max_on_of_ball_subset hd hz hsub
  have H₂ : ‖f w + f z‖ = ‖f z + f z‖ :=
    norm_eq_norm_of_is_max_on_of_ball_subset (hd.AddConst _) hz.norm_add_self hsub
  eq_of_norm_eq_of_norm_add_eq H₁ <| by simp only [H₂, same_ray.rfl.norm_add, H₁]
#align complex.eq_of_is_max_on_of_ball_subset Complex.eq_of_is_max_on_of_ball_subset

/-- **Maximum modulus principle** on a closed ball. Suppose that a function `f : E → F` from a
normed complex space to a strictly convex normed complex space has the following properties:

- it is continuous on a closed ball `metric.closed_ball z r`,
- it is complex differentiable on the corresponding open ball;
- the norm `‖f w‖` takes its maximum value on the open ball at its center.

Then `f` is a constant on the closed ball.  -/
theorem eq_on_closed_ball_of_is_max_on_norm {f : E → F} {z : E} {r : ℝ}
    (hd : DiffContOnCl ℂ f (ball z r)) (hz : IsMaxOn (norm ∘ f) (ball z r) z) :
    EqOn f (const E (f z)) (closedBall z r) := fun x hx =>
  eq_of_is_max_on_of_ball_subset hd hz <| ball_subset_ball hx
#align complex.eq_on_closed_ball_of_is_max_on_norm Complex.eq_on_closed_ball_of_is_max_on_norm

/-- **Maximum modulus principle**: if `f : E → F` is complex differentiable in a neighborhood of `c`
and the norm `‖f z‖` has a local maximum at `c`, then `f` is locally constant in a neighborhood
of `c`. -/
theorem eventually_eq_of_is_local_max_norm {f : E → F} {c : E}
    (hd : ∀ᶠ z in 𝓝 c, DifferentiableAt ℂ f z) (hc : IsLocalMax (norm ∘ f) c) :
    ∀ᶠ y in 𝓝 c, f y = f c :=
  by
  rcases nhds_basis_closed_ball.eventually_iff.1 (hd.and hc) with ⟨r, hr₀, hr⟩
  exact
    nhds_basis_closed_ball.eventually_iff.2
      ⟨r, hr₀,
        eq_on_closed_ball_of_is_max_on_norm
          (DifferentiableOn.diff_cont_on_cl fun x hx =>
            (hr <| closure_ball_subset_closed_ball hx).1.DifferentiableWithinAt)
          fun x hx => (hr <| ball_subset_closed_ball hx).2⟩
#align complex.eventually_eq_of_is_local_max_norm Complex.eventually_eq_of_is_local_max_norm

theorem eventually_eq_or_eq_zero_of_is_local_min_norm {f : E → ℂ} {c : E}
    (hf : ∀ᶠ z in 𝓝 c, DifferentiableAt ℂ f z) (hc : IsLocalMin (norm ∘ f) c) :
    (∀ᶠ z in 𝓝 c, f z = f c) ∨ f c = 0 :=
  by
  refine' or_iff_not_imp_right.mpr fun h => _
  have h1 : ∀ᶠ z in 𝓝 c, f z ≠ 0 := hf.self_of_nhds.continuous_at.eventually_ne h
  have h2 : IsLocalMax (norm ∘ f)⁻¹ c := hc.inv (h1.mono fun z => norm_pos_iff.mpr)
  have h3 : IsLocalMax (norm ∘ f⁻¹) c := by refine' h2.congr (eventually_of_forall _) <;> simp
  have h4 : ∀ᶠ z in 𝓝 c, DifferentiableAt ℂ f⁻¹ z := by filter_upwards [hf, h1] with z h using h.inv
  filter_upwards [eventually_eq_of_is_local_max_norm h4 h3] with z using inv_inj.mp
#align
  complex.eventually_eq_or_eq_zero_of_is_local_min_norm Complex.eventually_eq_or_eq_zero_of_is_local_min_norm

end StrictConvex

/-!
### Maximum on a set vs maximum on its frontier

In this section we prove corollaries of the maximum modulus principle that relate the values of a
function on a set to its values on the frontier of this set.
-/


variable [Nontrivial E]

/-- **Maximum modulus principle**: if `f : E → F` is complex differentiable on a nonempty bounded
set `U` and is continuous on its closure, then there exists a point `z ∈ frontier U` such that
`λ z, ‖f z‖` takes it maximum value on `closure U` at `z`. -/
theorem exists_mem_frontier_is_max_on_norm [FiniteDimensional ℂ E] {f : E → F} {U : Set E}
    (hb : Bounded U) (hne : U.Nonempty) (hd : DiffContOnCl ℂ f U) :
    ∃ z ∈ frontier U, IsMaxOn (norm ∘ f) (closure U) z :=
  by
  have hc : IsCompact (closure U) := hb.is_compact_closure
  obtain ⟨w, hwU, hle⟩ : ∃ w ∈ closure U, IsMaxOn (norm ∘ f) (closure U) w
  exact hc.exists_forall_ge hne.closure hd.continuous_on.norm
  rw [closure_eq_interior_union_frontier, mem_union] at hwU
  cases hwU
  rotate_left
  · exact ⟨w, hwU, hle⟩
  have : interior U ≠ univ := ne_top_of_le_ne_top hc.ne_univ interior_subset_closure
  rcases exists_mem_frontier_inf_dist_compl_eq_dist hwU this with ⟨z, hzU, hzw⟩
  refine' ⟨z, frontier_interior_subset hzU, fun x hx => (mem_set_of_eq.mp <| hle hx).trans_eq _⟩
  refine' (norm_eq_norm_of_is_max_on_of_ball_subset hd (hle.on_subset subset_closure) _).symm
  rw [dist_comm, ← hzw]
  exact ball_inf_dist_compl_subset.trans interior_subset
#align complex.exists_mem_frontier_is_max_on_norm Complex.exists_mem_frontier_is_max_on_norm

/-- **Maximum modulus principle**: if `f : E → F` is complex differentiable on a bounded set `U` and
`‖f z‖ ≤ C` for any `z ∈ frontier U`, then the same is true for any `z ∈ closure U`. -/
theorem norm_le_of_forall_mem_frontier_norm_le {f : E → F} {U : Set E} (hU : Bounded U)
    (hd : DiffContOnCl ℂ f U) {C : ℝ} (hC : ∀ z ∈ frontier U, ‖f z‖ ≤ C) {z : E}
    (hz : z ∈ closure U) : ‖f z‖ ≤ C :=
  by
  rw [closure_eq_self_union_frontier, union_comm, mem_union] at hz
  cases hz
  · exact hC z hz
  /- In case of a finite dimensional domain, one can just apply
    `complex.exists_mem_frontier_is_max_on_norm`. To make it work in any Banach space, we restrict
    the function to a line first. -/
  rcases exists_ne z with ⟨w, hne⟩
  set e : ℂ → E := line_map z w
  have hde : Differentiable ℂ e := (differentiable_id.smul_const (w - z)).AddConst z
  have hL : AntilipschitzWith (nndist z w)⁻¹ e := antilipschitz_with_line_map hne.symm
  replace hd : DiffContOnCl ℂ (f ∘ e) (e ⁻¹' U)
  exact hd.comp hde.diff_cont_on_cl (maps_to_preimage _ _)
  have h₀ : (0 : ℂ) ∈ e ⁻¹' U := by simpa only [e, mem_preimage, line_map_apply_zero]
  rcases exists_mem_frontier_is_max_on_norm (hL.bounded_preimage hU) ⟨0, h₀⟩ hd with ⟨ζ, hζU, hζ⟩
  calc
    ‖f z‖ = ‖f (e 0)‖ := by simp only [e, line_map_apply_zero]
    _ ≤ ‖f (e ζ)‖ := hζ (subset_closure h₀)
    _ ≤ C := hC _ (hde.continuous.frontier_preimage_subset _ hζU)
    
#align complex.norm_le_of_forall_mem_frontier_norm_le Complex.norm_le_of_forall_mem_frontier_norm_le

/-- If two complex differentiable functions `f g : E → F` are equal on the boundary of a bounded set
`U`, then they are equal on `closure U`. -/
theorem eq_on_closure_of_eq_on_frontier {f g : E → F} {U : Set E} (hU : Bounded U)
    (hf : DiffContOnCl ℂ f U) (hg : DiffContOnCl ℂ g U) (hfg : EqOn f g (frontier U)) :
    EqOn f g (closure U) :=
  by
  suffices H : ∀ z ∈ closure U, ‖(f - g) z‖ ≤ 0; · simpa [sub_eq_zero] using H
  refine' fun z hz => norm_le_of_forall_mem_frontier_norm_le hU (hf.sub hg) (fun w hw => _) hz
  simp [hfg hw]
#align complex.eq_on_closure_of_eq_on_frontier Complex.eq_on_closure_of_eq_on_frontier

/-- If two complex differentiable functions `f g : E → F` are equal on the boundary of a bounded set
`U`, then they are equal on `U`. -/
theorem eq_on_of_eq_on_frontier {f g : E → F} {U : Set E} (hU : Bounded U) (hf : DiffContOnCl ℂ f U)
    (hg : DiffContOnCl ℂ g U) (hfg : EqOn f g (frontier U)) : EqOn f g U :=
  (eq_on_closure_of_eq_on_frontier hU hf hg hfg).mono subset_closure
#align complex.eq_on_of_eq_on_frontier Complex.eq_on_of_eq_on_frontier

end Complex

