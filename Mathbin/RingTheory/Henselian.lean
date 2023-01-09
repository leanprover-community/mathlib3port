/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin

! This file was ported from Lean 3 source module ring_theory.henselian
! leanprover-community/mathlib commit 247a102b14f3cebfee126293341af5f6bed00237
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Polynomial.Taylor
import Mathbin.RingTheory.Ideal.LocalRing
import Mathbin.LinearAlgebra.AdicCompletion

/-!
# Henselian rings

In this file we set up the basic theory of Henselian (local) rings.
A ring `R` is *Henselian* at an ideal `I` if the following conditions hold:
* `I` is contained in the Jacobson radical of `R`
* for every polynomial `f` over `R`, with a *simple* root `a₀` over the quotient ring `R/I`,
  there exists a lift `a : R` of `a₀` that is a root of `f`.

(Here, saying that a root `b` of a polynomial `g` is *simple* means that `g.derivative.eval b` is a
unit. Warning: if `R/I` is not a field then it is not enough to assume that `g` has a factorization
into monic linear factors in which `X - b` shows up only once; for example `1` is not a simple root
of `X^2-1` over `ℤ/4ℤ`.)

A local ring `R` is *Henselian* if it is Henselian at its maximal ideal.
In this case the first condition is automatic, and in the second condition we may ask for
`f.derivative.eval a ≠ 0`, since the quotient ring `R/I` is a field in this case.

## Main declarations

* `henselian_ring`: a typeclass on commutative rings,
  asserting that the ring is Henselian at the ideal `I`.
* `henselian_local_ring`: a typeclass on commutative rings,
   asserting that the ring is local Henselian.
* `field.henselian`: fields are Henselian local rings
* `henselian.tfae`: equivalent ways of expressing the Henselian property for local rings
* `is_adic_complete.henselian`:
  a ring `R` with ideal `I` that is `I`-adically complete is Henselian at `I`

## References

https://stacks.math.columbia.edu/tag/04GE

## Todo

After a good API for etale ring homomorphisms has been developed,
we can give more equivalent characterization os Henselian rings.

In particular, this can give a proof that factorizations into coprime polynomials can be lifted
from the residue field to the Henselian ring.

The following gist contains some code sketches in that direction.
https://gist.github.com/jcommelin/47d94e4af092641017a97f7f02bf9598

-/


noncomputable section

universe u v

open BigOperators Polynomial

open LocalRing Polynomial Function

theorem is_local_ring_hom_of_le_jacobson_bot {R : Type _} [CommRing R] (I : Ideal R)
    (h : I ≤ Ideal.jacobson ⊥) : IsLocalRingHom (Ideal.Quotient.mk I) :=
  by
  constructor
  intro a h
  have : IsUnit (Ideal.Quotient.mk (Ideal.jacobson ⊥) a) :=
    by
    rw [isUnit_iff_exists_inv] at *
    obtain ⟨b, hb⟩ := h
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    use Ideal.Quotient.mk _ b
    rw [← (Ideal.Quotient.mk _).map_one, ← (Ideal.Quotient.mk _).map_mul, Ideal.Quotient.eq] at hb⊢
    exact h hb
  obtain ⟨⟨x, y, h1, h2⟩, rfl : x = _⟩ := this
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [← (Ideal.Quotient.mk _).map_mul, ← (Ideal.Quotient.mk _).map_one, Ideal.Quotient.eq,
    Ideal.mem_jacobson_bot] at h1 h2
  specialize h1 1
  simp at h1
  exact h1.1
#align is_local_ring_hom_of_le_jacobson_bot is_local_ring_hom_of_le_jacobson_bot

/-- A ring `R` is *Henselian* at an ideal `I` if the following condition holds:
for every polynomial `f` over `R`, with a *simple* root `a₀` over the quotient ring `R/I`,
there exists a lift `a : R` of `a₀` that is a root of `f`.

(Here, saying that a root `b` of a polynomial `g` is *simple* means that `g.derivative.eval b` is a
unit. Warning: if `R/I` is not a field then it is not enough to assume that `g` has a factorization
into monic linear factors in which `X - b` shows up only once; for example `1` is not a simple root
of `X^2-1` over `ℤ/4ℤ`.) -/
class HenselianRing (R : Type _) [CommRing R] (I : Ideal R) : Prop where
  jac : I ≤ Ideal.jacobson ⊥
  is_henselian :
    ∀ (f : R[X]) (hf : f.Monic) (a₀ : R) (h₁ : f.eval a₀ ∈ I)
      (h₂ : IsUnit (Ideal.Quotient.mk I (f.derivative.eval a₀))), ∃ a : R, f.IsRoot a ∧ a - a₀ ∈ I
#align henselian_ring HenselianRing

/-- A local ring `R` is *Henselian* if the following condition holds:
for every polynomial `f` over `R`, with a *simple* root `a₀` over the residue field,
there exists a lift `a : R` of `a₀` that is a root of `f`.
(Recall that a root `b` of a polynomial `g` is *simple* if it is not a double root, so if
`g.derivative.eval b ≠ 0`.)

In other words, `R` is local Henselian if it is Henselian at the ideal `I`,
in the sense of `henselian_ring`. -/
class HenselianLocalRing (R : Type _) [CommRing R] extends LocalRing R : Prop where
  is_henselian :
    ∀ (f : R[X]) (hf : f.Monic) (a₀ : R) (h₁ : f.eval a₀ ∈ maximalIdeal R)
      (h₂ : IsUnit (f.derivative.eval a₀)), ∃ a : R, f.IsRoot a ∧ a - a₀ ∈ maximalIdeal R
#align henselian_local_ring HenselianLocalRing

-- see Note [lower instance priority]
instance (priority := 100) Field.henselian (K : Type _) [Field K] : HenselianLocalRing K
    where is_henselian f hf a₀ h₁ h₂ :=
    by
    refine' ⟨a₀, _, _⟩ <;> rwa [(maximal_ideal K).eq_bot_of_prime, Ideal.mem_bot] at *
    rw [sub_self]
#align field.henselian Field.henselian

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `HenselianLocalRing.tfae [])
      (Command.declSig
       [(Term.explicitBinder "(" [`R] [":" (Term.type "Type" [`u])] [] ")")
        (Term.instBinder "[" [] (Term.app `CommRing [`R]) "]")
        (Term.instBinder "[" [] (Term.app `LocalRing [`R]) "]")]
       (Term.typeSpec
        ":"
        (Term.app
         `TFAE
         [(«term[_]»
           "["
           [(Term.app `HenselianLocalRing [`R])
            ","
            (Term.forall
             "∀"
             [(Term.explicitBinder
               "("
               [`f]
               [":" (Polynomial.Data.Polynomial.Basic.polynomial `R "[X]")]
               []
               ")")
              (Term.explicitBinder "(" [`hf] [":" (Term.proj `f "." `Monic)] [] ")")
              (Term.explicitBinder "(" [`a₀] [":" (Term.app `ResidueField [`R])] [] ")")
              (Term.explicitBinder
               "("
               [`h₁]
               [":" («term_=_» (Term.app `aeval [`a₀ `f]) "=" (num "0"))]
               []
               ")")
              (Term.explicitBinder
               "("
               [`h₂]
               [":"
                («term_≠_» (Term.app `aeval [`a₀ (Term.proj `f "." `derivative)]) "≠" (num "0"))]
               []
               ")")]
             []
             ","
             («term∃_,_»
              "∃"
              (Lean.explicitBinders
               (Lean.unbracketedExplicitBinders [(Lean.binderIdent `a)] [":" `R]))
              ","
              («term_∧_»
               (Term.app (Term.proj `f "." `IsRoot) [`a])
               "∧"
               («term_=_» (Term.app `residue [`R `a]) "=" `a₀))))
            ","
            (Term.forall
             "∀"
             [(Term.implicitBinder "{" [`K] [":" (Term.type "Type" [`u])] "}")
              (Term.instBinder "[" [] (Term.app `Field [`K]) "]")]
             []
             ","
             (Term.forall
              "∀"
              [(Term.explicitBinder
                "("
                [`φ]
                [":" (Algebra.Hom.Ring.«term_→+*_» `R " →+* " `K)]
                []
                ")")
               (Term.explicitBinder "(" [`hφ] [":" (Term.app `surjective [`φ])] [] ")")
               (Term.explicitBinder
                "("
                [`f]
                [":" (Polynomial.Data.Polynomial.Basic.polynomial `R "[X]")]
                []
                ")")
               (Term.explicitBinder "(" [`hf] [":" (Term.proj `f "." `Monic)] [] ")")
               (Term.explicitBinder "(" [`a₀] [":" `K] [] ")")
               (Term.explicitBinder
                "("
                [`h₁]
                [":" («term_=_» (Term.app (Term.proj `f "." `eval₂) [`φ `a₀]) "=" (num "0"))]
                []
                ")")
               (Term.explicitBinder
                "("
                [`h₂]
                [":" («term_≠_» (Term.app `f.derivative.eval₂ [`φ `a₀]) "≠" (num "0"))]
                []
                ")")]
              []
              ","
              («term∃_,_»
               "∃"
               (Lean.explicitBinders
                (Lean.unbracketedExplicitBinders [(Lean.binderIdent `a)] [":" `R]))
               ","
               («term_∧_»
                (Term.app (Term.proj `f "." `IsRoot) [`a])
                "∧"
                («term_=_» (Term.app `φ [`a]) "=" `a₀)))))]
           "]")])))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.tfaeHave "tfae_have" [`_3_2 ":"] (num "3") "→" (num "2"))
           ";"
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.intro "intro" [`H])
             []
             (Tactic.exact
              "exact"
              (Term.app `H [(Term.app `residue [`R]) `Ideal.Quotient.mk_surjective]))])
           []
           (Tactic.tfaeHave "tfae_have" [`_2_1 ":"] (num "2") "→" (num "1"))
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.intro "intro" [`H])
             []
             (Tactic.constructor "constructor")
             []
             (Tactic.intro "intro" [`f `hf `a₀ `h₁ `h₂])
             []
             (Tactic.specialize "specialize" (Term.app `H [`f `hf (Term.app `residue [`R `a₀])]))
             []
             (Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl [`aux []] [] ":=" (Term.app `flip [`mem_nonunits_iff.mp `h₂]))))
             []
             (Tactic.simp
              "simp"
              []
              []
              ["only"]
              ["["
               [(Tactic.simpLemma [] [] `aeval_def)
                ","
                (Tactic.simpLemma [] [] `residue_field.algebra_map_eq)
                ","
                (Tactic.simpLemma [] [] `eval₂_at_apply)
                ","
                (Tactic.simpLemma
                 []
                 [(patternIgnore (token.«← » "←"))]
                 `Ideal.Quotient.eq_zero_iff_mem)
                ","
                (Tactic.simpLemma
                 []
                 [(patternIgnore (token.«← » "←"))]
                 `LocalRing.mem_maximal_ideal)]
               "]"]
              [(Tactic.location "at" (Tactic.locationHyp [`H `h₁ `aux] []))])
             []
             (Std.Tactic.obtain
              "obtain"
              [(Std.Tactic.RCases.rcasesPatMed
                [(Std.Tactic.RCases.rcasesPat.tuple
                  "⟨"
                  [(Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `a)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `ha₁)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `ha₂)])
                    [])]
                  "⟩")])]
              []
              [":=" [(Term.app `H [`h₁ `aux])]])
             []
             (Tactic.refine'
              "refine'"
              (Term.anonymousCtor "⟨" [`a "," `ha₁ "," (Term.hole "_")] "⟩"))
             []
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Ideal.Quotient.eq_zero_iff_mem)]
               "]")
              [])
             []
             (Std.Tactic.tacticRwa__
              "rwa"
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `sub_eq_zero)
                ","
                (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `RingHom.map_sub)]
               "]")
              [(Tactic.location "at" (Tactic.locationHyp [`ha₂] []))])])
           []
           (Tactic.tfaeHave "tfae_have" [`_1_3 ":"] (num "1") "→" (num "3"))
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.intro "intro" [`hR `K `_K `φ `hφ `f `hf `a₀ `h₁ `h₂])
             []
             (Std.Tactic.obtain
              "obtain"
              [(Std.Tactic.RCases.rcasesPatMed
                [(Std.Tactic.RCases.rcasesPat.tuple
                  "⟨"
                  [(Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `a₀)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                    [])]
                  "⟩")])]
              []
              [":=" [(Term.app `hφ [`a₀])]])
             []
             (Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                [`H []]
                []
                ":="
                (Term.app `HenselianLocalRing.is_henselian [`f `hf `a₀]))))
             []
             (Tactic.simp
              "simp"
              []
              []
              ["only"]
              ["["
               [(Tactic.simpLemma
                 []
                 [(patternIgnore (token.«← » "←"))]
                 (Term.app `ker_eq_maximal_ideal [`φ `hφ]))
                ","
                (Tactic.simpLemma [] [] `eval₂_at_apply)
                ","
                (Tactic.simpLemma [] [] `φ.mem_ker)]
               "]"]
              [(Tactic.location "at" (Tactic.locationHyp [`H `h₁ `h₂] []))])
             []
             (Std.Tactic.obtain
              "obtain"
              [(Std.Tactic.RCases.rcasesPatMed
                [(Std.Tactic.RCases.rcasesPat.tuple
                  "⟨"
                  [(Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `a)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `ha₁)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `ha₂)])
                    [])]
                  "⟩")])]
              []
              [":=" [(Term.app `H [`h₁ (Term.hole "_")])]])
             []
             (tactic__
              (cdotTk (patternIgnore (token.«· » "·")))
              [(Tactic.refine'
                "refine'"
                (Term.anonymousCtor "⟨" [`a "," `ha₁ "," (Term.hole "_")] "⟩"))
               []
               (Std.Tactic.tacticRwa__
                "rwa"
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule [] `φ.map_sub) "," (Tactic.rwRule [] `sub_eq_zero)]
                 "]")
                [(Tactic.location "at" (Tactic.locationHyp [`ha₂] []))])])
             []
             (tactic__
              (cdotTk (patternIgnore (token.«· » "·")))
              [(Mathlib.Tactic.Contrapose.contrapose! "contrapose!" [`h₂ []])
               []
               (Std.Tactic.tacticRwa__
                "rwa"
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `mem_nonunits_iff)
                  ","
                  (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `LocalRing.mem_maximal_ideal)
                  ","
                  (Tactic.rwRule
                   [(patternIgnore (token.«← » "←"))]
                   (Term.app `LocalRing.ker_eq_maximal_ideal [`φ `hφ]))
                  ","
                  (Tactic.rwRule [] `φ.mem_ker)]
                 "]")
                [(Tactic.location "at" (Tactic.locationHyp [`h₂] []))])])])
           []
           (Tactic.tfaeFinish "tfae_finish")])))
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
         [(Tactic.tfaeHave "tfae_have" [`_3_2 ":"] (num "3") "→" (num "2"))
          ";"
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.intro "intro" [`H])
            []
            (Tactic.exact
             "exact"
             (Term.app `H [(Term.app `residue [`R]) `Ideal.Quotient.mk_surjective]))])
          []
          (Tactic.tfaeHave "tfae_have" [`_2_1 ":"] (num "2") "→" (num "1"))
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.intro "intro" [`H])
            []
            (Tactic.constructor "constructor")
            []
            (Tactic.intro "intro" [`f `hf `a₀ `h₁ `h₂])
            []
            (Tactic.specialize "specialize" (Term.app `H [`f `hf (Term.app `residue [`R `a₀])]))
            []
            (Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl [`aux []] [] ":=" (Term.app `flip [`mem_nonunits_iff.mp `h₂]))))
            []
            (Tactic.simp
             "simp"
             []
             []
             ["only"]
             ["["
              [(Tactic.simpLemma [] [] `aeval_def)
               ","
               (Tactic.simpLemma [] [] `residue_field.algebra_map_eq)
               ","
               (Tactic.simpLemma [] [] `eval₂_at_apply)
               ","
               (Tactic.simpLemma
                []
                [(patternIgnore (token.«← » "←"))]
                `Ideal.Quotient.eq_zero_iff_mem)
               ","
               (Tactic.simpLemma
                []
                [(patternIgnore (token.«← » "←"))]
                `LocalRing.mem_maximal_ideal)]
              "]"]
             [(Tactic.location "at" (Tactic.locationHyp [`H `h₁ `aux] []))])
            []
            (Std.Tactic.obtain
             "obtain"
             [(Std.Tactic.RCases.rcasesPatMed
               [(Std.Tactic.RCases.rcasesPat.tuple
                 "⟨"
                 [(Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `a)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `ha₁)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `ha₂)])
                   [])]
                 "⟩")])]
             []
             [":=" [(Term.app `H [`h₁ `aux])]])
            []
            (Tactic.refine'
             "refine'"
             (Term.anonymousCtor "⟨" [`a "," `ha₁ "," (Term.hole "_")] "⟩"))
            []
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Ideal.Quotient.eq_zero_iff_mem)]
              "]")
             [])
            []
            (Std.Tactic.tacticRwa__
             "rwa"
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `sub_eq_zero)
               ","
               (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `RingHom.map_sub)]
              "]")
             [(Tactic.location "at" (Tactic.locationHyp [`ha₂] []))])])
          []
          (Tactic.tfaeHave "tfae_have" [`_1_3 ":"] (num "1") "→" (num "3"))
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.intro "intro" [`hR `K `_K `φ `hφ `f `hf `a₀ `h₁ `h₂])
            []
            (Std.Tactic.obtain
             "obtain"
             [(Std.Tactic.RCases.rcasesPatMed
               [(Std.Tactic.RCases.rcasesPat.tuple
                 "⟨"
                 [(Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `a₀)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                   [])]
                 "⟩")])]
             []
             [":=" [(Term.app `hφ [`a₀])]])
            []
            (Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               [`H []]
               []
               ":="
               (Term.app `HenselianLocalRing.is_henselian [`f `hf `a₀]))))
            []
            (Tactic.simp
             "simp"
             []
             []
             ["only"]
             ["["
              [(Tactic.simpLemma
                []
                [(patternIgnore (token.«← » "←"))]
                (Term.app `ker_eq_maximal_ideal [`φ `hφ]))
               ","
               (Tactic.simpLemma [] [] `eval₂_at_apply)
               ","
               (Tactic.simpLemma [] [] `φ.mem_ker)]
              "]"]
             [(Tactic.location "at" (Tactic.locationHyp [`H `h₁ `h₂] []))])
            []
            (Std.Tactic.obtain
             "obtain"
             [(Std.Tactic.RCases.rcasesPatMed
               [(Std.Tactic.RCases.rcasesPat.tuple
                 "⟨"
                 [(Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `a)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `ha₁)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `ha₂)])
                   [])]
                 "⟩")])]
             []
             [":=" [(Term.app `H [`h₁ (Term.hole "_")])]])
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(Tactic.refine'
               "refine'"
               (Term.anonymousCtor "⟨" [`a "," `ha₁ "," (Term.hole "_")] "⟩"))
              []
              (Std.Tactic.tacticRwa__
               "rwa"
               (Tactic.rwRuleSeq
                "["
                [(Tactic.rwRule [] `φ.map_sub) "," (Tactic.rwRule [] `sub_eq_zero)]
                "]")
               [(Tactic.location "at" (Tactic.locationHyp [`ha₂] []))])])
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(Mathlib.Tactic.Contrapose.contrapose! "contrapose!" [`h₂ []])
              []
              (Std.Tactic.tacticRwa__
               "rwa"
               (Tactic.rwRuleSeq
                "["
                [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `mem_nonunits_iff)
                 ","
                 (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `LocalRing.mem_maximal_ideal)
                 ","
                 (Tactic.rwRule
                  [(patternIgnore (token.«← » "←"))]
                  (Term.app `LocalRing.ker_eq_maximal_ideal [`φ `hφ]))
                 ","
                 (Tactic.rwRule [] `φ.mem_ker)]
                "]")
               [(Tactic.location "at" (Tactic.locationHyp [`h₂] []))])])])
          []
          (Tactic.tfaeFinish "tfae_finish")])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tfaeFinish "tfae_finish")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.intro "intro" [`hR `K `_K `φ `hφ `f `hf `a₀ `h₁ `h₂])
        []
        (Std.Tactic.obtain
         "obtain"
         [(Std.Tactic.RCases.rcasesPatMed
           [(Std.Tactic.RCases.rcasesPat.tuple
             "⟨"
             [(Std.Tactic.RCases.rcasesPatLo
               (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `a₀)])
               [])
              ","
              (Std.Tactic.RCases.rcasesPatLo
               (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
               [])]
             "⟩")])]
         []
         [":=" [(Term.app `hφ [`a₀])]])
        []
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`H []]
           []
           ":="
           (Term.app `HenselianLocalRing.is_henselian [`f `hf `a₀]))))
        []
        (Tactic.simp
         "simp"
         []
         []
         ["only"]
         ["["
          [(Tactic.simpLemma
            []
            [(patternIgnore (token.«← » "←"))]
            (Term.app `ker_eq_maximal_ideal [`φ `hφ]))
           ","
           (Tactic.simpLemma [] [] `eval₂_at_apply)
           ","
           (Tactic.simpLemma [] [] `φ.mem_ker)]
          "]"]
         [(Tactic.location "at" (Tactic.locationHyp [`H `h₁ `h₂] []))])
        []
        (Std.Tactic.obtain
         "obtain"
         [(Std.Tactic.RCases.rcasesPatMed
           [(Std.Tactic.RCases.rcasesPat.tuple
             "⟨"
             [(Std.Tactic.RCases.rcasesPatLo
               (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `a)])
               [])
              ","
              (Std.Tactic.RCases.rcasesPatLo
               (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `ha₁)])
               [])
              ","
              (Std.Tactic.RCases.rcasesPatLo
               (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `ha₂)])
               [])]
             "⟩")])]
         []
         [":=" [(Term.app `H [`h₁ (Term.hole "_")])]])
        []
        (tactic__
         (cdotTk (patternIgnore (token.«· » "·")))
         [(Tactic.refine' "refine'" (Term.anonymousCtor "⟨" [`a "," `ha₁ "," (Term.hole "_")] "⟩"))
          []
          (Std.Tactic.tacticRwa__
           "rwa"
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `φ.map_sub) "," (Tactic.rwRule [] `sub_eq_zero)]
            "]")
           [(Tactic.location "at" (Tactic.locationHyp [`ha₂] []))])])
        []
        (tactic__
         (cdotTk (patternIgnore (token.«· » "·")))
         [(Mathlib.Tactic.Contrapose.contrapose! "contrapose!" [`h₂ []])
          []
          (Std.Tactic.tacticRwa__
           "rwa"
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `mem_nonunits_iff)
             ","
             (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `LocalRing.mem_maximal_ideal)
             ","
             (Tactic.rwRule
              [(patternIgnore (token.«← » "←"))]
              (Term.app `LocalRing.ker_eq_maximal_ideal [`φ `hφ]))
             ","
             (Tactic.rwRule [] `φ.mem_ker)]
            "]")
           [(Tactic.location "at" (Tactic.locationHyp [`h₂] []))])])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Mathlib.Tactic.Contrapose.contrapose! "contrapose!" [`h₂ []])
        []
        (Std.Tactic.tacticRwa__
         "rwa"
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `mem_nonunits_iff)
           ","
           (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `LocalRing.mem_maximal_ideal)
           ","
           (Tactic.rwRule
            [(patternIgnore (token.«← » "←"))]
            (Term.app `LocalRing.ker_eq_maximal_ideal [`φ `hφ]))
           ","
           (Tactic.rwRule [] `φ.mem_ker)]
          "]")
         [(Tactic.location "at" (Tactic.locationHyp [`h₂] []))])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.tacticRwa__
       "rwa"
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `mem_nonunits_iff)
         ","
         (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `LocalRing.mem_maximal_ideal)
         ","
         (Tactic.rwRule
          [(patternIgnore (token.«← » "←"))]
          (Term.app `LocalRing.ker_eq_maximal_ideal [`φ `hφ]))
         ","
         (Tactic.rwRule [] `φ.mem_ker)]
        "]")
       [(Tactic.location "at" (Tactic.locationHyp [`h₂] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h₂
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `φ.mem_ker
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `LocalRing.ker_eq_maximal_ideal [`φ `hφ])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hφ
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `φ
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `LocalRing.ker_eq_maximal_ideal
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `LocalRing.mem_maximal_ideal
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mem_nonunits_iff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.Contrapose.contrapose! "contrapose!" [`h₂ []])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.refine' "refine'" (Term.anonymousCtor "⟨" [`a "," `ha₁ "," (Term.hole "_")] "⟩"))
        []
        (Std.Tactic.tacticRwa__
         "rwa"
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule [] `φ.map_sub) "," (Tactic.rwRule [] `sub_eq_zero)]
          "]")
         [(Tactic.location "at" (Tactic.locationHyp [`ha₂] []))])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.tacticRwa__
       "rwa"
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `φ.map_sub) "," (Tactic.rwRule [] `sub_eq_zero)]
        "]")
       [(Tactic.location "at" (Tactic.locationHyp [`ha₂] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ha₂
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `sub_eq_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `φ.map_sub
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine' "refine'" (Term.anonymousCtor "⟨" [`a "," `ha₁ "," (Term.hole "_")] "⟩"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [`a "," `ha₁ "," (Term.hole "_")] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ha₁
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.obtain
       "obtain"
       [(Std.Tactic.RCases.rcasesPatMed
         [(Std.Tactic.RCases.rcasesPat.tuple
           "⟨"
           [(Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `a)])
             [])
            ","
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `ha₁)])
             [])
            ","
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `ha₂)])
             [])]
           "⟩")])]
       []
       [":=" [(Term.app `H [`h₁ (Term.hole "_")])]])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `H [`h₁ (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      `h₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `H
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["["
        [(Tactic.simpLemma
          []
          [(patternIgnore (token.«← » "←"))]
          (Term.app `ker_eq_maximal_ideal [`φ `hφ]))
         ","
         (Tactic.simpLemma [] [] `eval₂_at_apply)
         ","
         (Tactic.simpLemma [] [] `φ.mem_ker)]
        "]"]
       [(Tactic.location "at" (Tactic.locationHyp [`H `h₁ `h₂] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h₂
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `h₁
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `H
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `φ.mem_ker
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `eval₂_at_apply
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `ker_eq_maximal_ideal [`φ `hφ])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hφ
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `φ
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `ker_eq_maximal_ideal
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl [`H []] [] ":=" (Term.app `HenselianLocalRing.is_henselian [`f `hf `a₀]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `HenselianLocalRing.is_henselian [`f `hf `a₀])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a₀
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hf
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `HenselianLocalRing.is_henselian
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
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `a₀)])
             [])
            ","
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
             [])]
           "⟩")])]
       []
       [":=" [(Term.app `hφ [`a₀])]])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `hφ [`a₀])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a₀
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `hφ
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.intro "intro" [`hR `K `_K `φ `hφ `f `hf `a₀ `h₁ `h₂])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h₂
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `h₁
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a₀
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hf
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hφ
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `φ
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `_K
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `K
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hR
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tfaeHave "tfae_have" [`_1_3 ":"] (num "1") "→" (num "3"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«→»', expected 'token.« → »'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«→»', expected 'token.« ↔ »'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«→»', expected 'token.« ← »'
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
  HenselianLocalRing.tfae
  ( R : Type u ) [ CommRing R ] [ LocalRing R ]
    :
      TFAE
        [
          HenselianLocalRing R
            ,
            ∀
              ( f : R [X] )
                ( hf : f . Monic )
                ( a₀ : ResidueField R )
                ( h₁ : aeval a₀ f = 0 )
                ( h₂ : aeval a₀ f . derivative ≠ 0 )
              ,
              ∃ a : R , f . IsRoot a ∧ residue R a = a₀
            ,
            ∀
              { K : Type u } [ Field K ]
              ,
              ∀
                ( φ : R →+* K )
                  ( hφ : surjective φ )
                  ( f : R [X] )
                  ( hf : f . Monic )
                  ( a₀ : K )
                  ( h₁ : f . eval₂ φ a₀ = 0 )
                  ( h₂ : f.derivative.eval₂ φ a₀ ≠ 0 )
                ,
                ∃ a : R , f . IsRoot a ∧ φ a = a₀
          ]
  :=
    by
      tfae_have _3_2 : 3 → 2
        ;
        · intro H exact H residue R Ideal.Quotient.mk_surjective
        tfae_have _2_1 : 2 → 1
        ·
          intro H
            constructor
            intro f hf a₀ h₁ h₂
            specialize H f hf residue R a₀
            have aux := flip mem_nonunits_iff.mp h₂
            simp
              only
              [
                aeval_def
                  ,
                  residue_field.algebra_map_eq
                  ,
                  eval₂_at_apply
                  ,
                  ← Ideal.Quotient.eq_zero_iff_mem
                  ,
                  ← LocalRing.mem_maximal_ideal
                ]
              at H h₁ aux
            obtain ⟨ a , ha₁ , ha₂ ⟩ := H h₁ aux
            refine' ⟨ a , ha₁ , _ ⟩
            rw [ ← Ideal.Quotient.eq_zero_iff_mem ]
            rwa [ ← sub_eq_zero , ← RingHom.map_sub ] at ha₂
        tfae_have _1_3 : 1 → 3
        ·
          intro hR K _K φ hφ f hf a₀ h₁ h₂
            obtain ⟨ a₀ , rfl ⟩ := hφ a₀
            have H := HenselianLocalRing.is_henselian f hf a₀
            simp only [ ← ker_eq_maximal_ideal φ hφ , eval₂_at_apply , φ.mem_ker ] at H h₁ h₂
            obtain ⟨ a , ha₁ , ha₂ ⟩ := H h₁ _
            · refine' ⟨ a , ha₁ , _ ⟩ rwa [ φ.map_sub , sub_eq_zero ] at ha₂
            ·
              contrapose! h₂
                rwa
                  [
                    ← mem_nonunits_iff
                      ,
                      ← LocalRing.mem_maximal_ideal
                      ,
                      ← LocalRing.ker_eq_maximal_ideal φ hφ
                      ,
                      φ.mem_ker
                    ]
                  at h₂
        tfae_finish
#align henselian_local_ring.tfae HenselianLocalRing.tfae

instance (R : Type _) [CommRing R] [hR : HenselianLocalRing R] : HenselianRing R (maximalIdeal R)
    where
  jac := by
    rw [Ideal.jacobson, le_infₛ_iff]
    rintro I ⟨-, hI⟩
    exact (eq_maximal_ideal hI).ge
  is_henselian := by
    intro f hf a₀ h₁ h₂
    refine' HenselianLocalRing.is_henselian f hf a₀ h₁ _
    contrapose! h₂
    rw [← mem_nonunits_iff, ← LocalRing.mem_maximal_ideal, ← Ideal.Quotient.eq_zero_iff_mem] at h₂
    rw [h₂]
    exact not_isUnit_zero

-- see Note [lower instance priority]
/-- A ring `R` that is `I`-adically complete is Henselian at `I`. -/
instance (priority := 100) IsAdicComplete.henselianRing (R : Type _) [CommRing R] (I : Ideal R)
    [IsAdicComplete I R] : HenselianRing R I
    where
  jac := IsAdicComplete.le_jacobson_bot _
  is_henselian := by
    intro f hf a₀ h₁ h₂
    classical
      let f' := f.derivative
      -- we define a sequence `c n` by starting at `a₀` and then continually
      -- applying the function sending `b` to `b - f(b)/f'(b)` (Newton's method).
      -- Note that `f'.eval b` is a unit, because `b` has the same residue as `a₀` modulo `I`.
      let c : ℕ → R := fun n => Nat.recOn n a₀ fun _ b => b - f.eval b * Ring.inverse (f'.eval b)
      have hc : ∀ n, c (n + 1) = c n - f.eval (c n) * Ring.inverse (f'.eval (c n)) :=
        by
        intro n
        dsimp only [c, Nat.rec_add_one]
        rfl
      -- we now spend some time determining properties of the sequence `c : ℕ → R`
      -- `hc_mod`: for every `n`, we have `c n ≡ a₀ [SMOD I]`
      -- `hf'c`  : for every `n`, `f'.eval (c n)` is a unit
      -- `hfcI`  : for every `n`, `f.eval (c n)` is contained in `I ^ (n+1)`
      have hc_mod : ∀ n, c n ≡ a₀ [SMOD I] := by
        intro n
        induction' n with n ih
        · rfl
        rw [Nat.succ_eq_add_one, hc, sub_eq_add_neg, ← add_zero a₀]
        refine' ih.add _
        rw [Smodeq.zero, Ideal.neg_mem_iff]
        refine' I.mul_mem_right _ _
        rw [← Smodeq.zero] at h₁⊢
        exact (ih.eval f).trans h₁
      have hf'c : ∀ n, IsUnit (f'.eval (c n)) := by
        intro n
        haveI := is_local_ring_hom_of_le_jacobson_bot I (IsAdicComplete.le_jacobson_bot I)
        apply is_unit_of_map_unit (Ideal.Quotient.mk I)
        convert h₂ using 1
        exact smodeq.def.mp ((hc_mod n).eval _)
      have hfcI : ∀ n, f.eval (c n) ∈ I ^ (n + 1) :=
        by
        intro n
        induction' n with n ih
        · simpa only [pow_one]
        simp only [Nat.succ_eq_add_one]
        rw [← taylor_eval_sub (c n), hc]
        simp only [sub_eq_add_neg, add_neg_cancel_comm]
        rw [eval_eq_sum, sum_over_range' _ _ _ (lt_add_of_pos_right _ zero_lt_two), ←
          Finset.sum_range_add_sum_Ico _ (Nat.le_add_left _ _)]
        swap
        · intro i
          rw [zero_mul]
        refine' Ideal.add_mem _ _ _
        · simp only [Finset.sum_range_succ, taylor_coeff_one, mul_one, pow_one, taylor_coeff_zero,
            mul_neg, Finset.sum_singleton, Finset.range_one, pow_zero]
          rw [mul_left_comm, Ring.mul_inverse_cancel _ (hf'c n), mul_one, add_neg_self]
          exact Ideal.zero_mem _
        · refine' Submodule.sum_mem _ _
          simp only [Finset.mem_Ico]
          rintro i ⟨h2i, hi⟩
          have aux : n + 2 ≤ i * (n + 1) := by trans 2 * (n + 1) <;> nlinarith only [h2i]
          refine' Ideal.mul_mem_left _ _ (Ideal.pow_le_pow aux _)
          rw [pow_mul']
          refine' Ideal.pow_mem_pow ((Ideal.neg_mem_iff _).2 <| Ideal.mul_mem_right _ _ ih) _
      -- we are now in the position to show that `c : ℕ → R` is a Cauchy sequence
      have aux : ∀ m n, m ≤ n → c m ≡ c n [SMOD (I ^ m • ⊤ : Ideal R)] :=
        by
        intro m n hmn
        rw [← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one]
        obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
        clear hmn
        induction' k with k ih
        · rw [add_zero]
        rw [Nat.succ_eq_add_one, ← add_assoc, hc, ← add_zero (c m), sub_eq_add_neg]
        refine' ih.add _
        symm
        rw [Smodeq.zero, Ideal.neg_mem_iff]
        refine' Ideal.mul_mem_right _ _ (Ideal.pow_le_pow _ (hfcI _))
        rw [add_assoc]
        exact le_self_add
      -- hence the sequence converges to some limit point `a`, which is the `a` we are looking for
      obtain ⟨a, ha⟩ := IsPrecomplete.prec' c aux
      refine' ⟨a, _, _⟩
      · show f.is_root a
        suffices ∀ n, f.eval a ≡ 0 [SMOD (I ^ n • ⊤ : Ideal R)] by exact IsHausdorff.haus' _ this
        intro n
        specialize ha n
        rw [← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one] at ha⊢
        refine' (ha.symm.eval f).trans _
        rw [Smodeq.zero]
        exact Ideal.pow_le_pow le_self_add (hfcI _)
      · show a - a₀ ∈ I
        specialize ha 1
        rw [hc, pow_one, ← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one, sub_eq_add_neg] at ha
        rw [← Smodeq.sub_mem, ← add_zero a₀]
        refine' ha.symm.trans (smodeq.rfl.add _)
        rw [Smodeq.zero, Ideal.neg_mem_iff]
        exact Ideal.mul_mem_right _ _ h₁
#align is_adic_complete.henselian_ring IsAdicComplete.henselianRing

