/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin

! This file was ported from Lean 3 source module ring_theory.witt_vector.frobenius
! leanprover-community/mathlib commit 6afc9b06856ad973f6a2619e3e8a0a8d537a58f2
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Nat.Multiplicity
import Mathbin.Data.Zmod.Algebra
import Mathbin.RingTheory.WittVector.Basic
import Mathbin.RingTheory.WittVector.IsPoly
import Mathbin.FieldTheory.PerfectClosure

/-!
## The Frobenius operator

If `R` has characteristic `p`, then there is a ring endomorphism `frobenius R p`
that raises `r : R` to the power `p`.
By applying `witt_vector.map` to `frobenius R p`, we obtain a ring endomorphism `𝕎 R →+* 𝕎 R`.
It turns out that this endomorphism can be described by polynomials over `ℤ`
that do not depend on `R` or the fact that it has characteristic `p`.
In this way, we obtain a Frobenius endomorphism `witt_vector.frobenius_fun : 𝕎 R → 𝕎 R`
for every commutative ring `R`.

Unfortunately, the aforementioned polynomials can not be obtained using the machinery
of `witt_structure_int` that was developed in `structure_polynomial.lean`.
We therefore have to define the polynomials by hand, and check that they have the required property.

In case `R` has characteristic `p`, we show in `frobenius_fun_eq_map_frobenius`
that `witt_vector.frobenius_fun` is equal to `witt_vector.map (frobenius R p)`.

### Main definitions and results

* `frobenius_poly`: the polynomials that describe the coefficients of `frobenius_fun`;
* `frobenius_fun`: the Frobenius endomorphism on Witt vectors;
* `frobenius_fun_is_poly`: the tautological assertion that Frobenius is a polynomial function;
* `frobenius_fun_eq_map_frobenius`: the fact that in characteristic `p`, Frobenius is equal to
  `witt_vector.map (frobenius R p)`.

TODO: Show that `witt_vector.frobenius_fun` is a ring homomorphism,
and bundle it into `witt_vector.frobenius`.

## References

* [Hazewinkel, *Witt Vectors*][Haze09]

* [Commelin and Lewis, *Formalizing the Ring of Witt Vectors*][CL21]
-/


namespace WittVector

variable {p : ℕ} {R S : Type _} [hp : Fact p.Prime] [CommRing R] [CommRing S]

-- mathport name: expr𝕎
local notation "𝕎" => WittVector p

-- type as `\bbW`
noncomputable section

open MvPolynomial Finset

open BigOperators

variable (p)

include hp

/-- The rational polynomials that give the coefficients of `frobenius x`,
in terms of the coefficients of `x`.
These polynomials actually have integral coefficients,
see `frobenius_poly` and `map_frobenius_poly`. -/
def frobeniusPolyRat (n : ℕ) : MvPolynomial ℕ ℚ :=
  bind₁ (wittPolynomial p ℚ ∘ fun n => n + 1) (xInTermsOfW p ℚ n)
#align witt_vector.frobenius_poly_rat WittVector.frobeniusPolyRat

theorem bind₁_frobenius_poly_rat_witt_polynomial (n : ℕ) :
    bind₁ (frobeniusPolyRat p) (wittPolynomial p ℚ n) = wittPolynomial p ℚ (n + 1) :=
  by
  delta frobenius_poly_rat
  rw [← bind₁_bind₁, bind₁_X_in_terms_of_W_witt_polynomial, bind₁_X_right]
#align
  witt_vector.bind₁_frobenius_poly_rat_witt_polynomial WittVector.bind₁_frobenius_poly_rat_witt_polynomial

/-- An auxiliary definition, to avoid an excessive amount of finiteness proofs
for `multiplicity p n`. -/
private def pnat_multiplicity (n : ℕ+) : ℕ :=
  (multiplicity p n).get <| multiplicity.finite_nat_iff.mpr <| ⟨ne_of_gt hp.1.one_lt, n.2⟩
#align witt_vector.pnat_multiplicity witt_vector.pnat_multiplicity

-- mathport name: exprv
local notation "v" => pnatMultiplicity

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "An auxiliary polynomial over the integers, that satisfies\n`p * (frobenius_poly_aux p n) + X n ^ p = frobenius_poly p n`.\nThis makes it easy to show that `frobenius_poly p n` is congruent to `X n ^ p`\nmodulo `p`. -/")]
      []
      []
      [(Command.noncomputable "noncomputable")]
      []
      [])
     (Command.def
      "def"
      (Command.declId `frobeniusPolyAux [])
      (Command.optDeclSig
       []
       [(Term.typeSpec
         ":"
         (Term.arrow (termℕ "ℕ") "→" (Term.app `MvPolynomial [(termℕ "ℕ") (termℤ "ℤ")])))])
      (Command.declValEqns
       (Term.matchAltsWhereDecls
        (Term.matchAlts
         [(Term.matchAlt
           "|"
           [[`n]]
           "=>"
           («term_-_»
            (Term.app `x [(«term_+_» `n "+" (num "1"))])
            "-"
            (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
             "∑"
             (Std.ExtendedBinder.extBinders
              (Std.ExtendedBinder.extBinder
               (Lean.binderIdent `i)
               [(group ":" (Term.app `Fin [`n]))]))
             ", "
             (Term.have
              "have"
              (Term.haveDecl (Term.haveIdDecl [] [] ":=" (Term.proj `i "." `is_lt)))
              []
              (BigOperators.Algebra.BigOperators.Basic.finset.sum
               "∑"
               (Std.ExtendedBinder.extBinders
                (Std.ExtendedBinder.extBinder (Lean.binderIdent `j) []))
               " in "
               (Term.app `range [(«term_^_» `p "^" («term_-_» `n "-" `i))])
               ", "
               («term_*_»
                («term_*_»
                 («term_^_»
                  («term_^_» (Term.app `x [`i]) "^" `p)
                  "^"
                  («term_-_»
                   («term_^_» `p "^" («term_-_» `n "-" `i))
                   "-"
                   («term_+_» `j "+" (num "1"))))
                 "*"
                 («term_^_» (Term.app `frobenius_poly_aux [`i]) "^" («term_+_» `j "+" (num "1"))))
                "*"
                (Term.app
                 `c
                 [(coeNotation
                   "↑"
                   (Term.typeAscription
                    "("
                    («term_*_»
                     («term_/_»
                      (Term.app
                       (Term.proj («term_^_» `p "^" («term_-_» `n "-" `i)) "." `choose)
                       [(«term_+_» `j "+" (num "1"))])
                      "/"
                      («term_^_»
                       `p
                       "^"
                       («term_-_»
                        («term_-_» `n "-" `i)
                        "-"
                        (Term.app
                         (WittVector.RingTheory.WittVector.Frobenius.termv "v")
                         [`p
                          (Term.anonymousCtor
                           "⟨"
                           [(«term_+_» `j "+" (num "1")) "," (Term.app `Nat.succ_pos [`j])]
                           "⟩")]))))
                     "*"
                     («term_^_»
                      (coeNotation "↑" `p)
                      "^"
                      («term_-_»
                       `j
                       "-"
                       (Term.app
                        (WittVector.RingTheory.WittVector.Frobenius.termv "v")
                        [`p
                         (Term.anonymousCtor
                          "⟨"
                          [(«term_+_» `j "+" (num "1")) "," (Term.app `Nat.succ_pos [`j])]
                          "⟩")]))))
                    ":"
                    [(termℕ "ℕ")]
                    ")"))])))))))])
        []))
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValEqns', expected 'Lean.Parser.Command.declValSimple'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_-_»
       (Term.app `x [(«term_+_» `n "+" (num "1"))])
       "-"
       (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
        "∑"
        (Std.ExtendedBinder.extBinders
         (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) [(group ":" (Term.app `Fin [`n]))]))
        ", "
        (Term.have
         "have"
         (Term.haveDecl (Term.haveIdDecl [] [] ":=" (Term.proj `i "." `is_lt)))
         []
         (BigOperators.Algebra.BigOperators.Basic.finset.sum
          "∑"
          (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `j) []))
          " in "
          (Term.app `range [(«term_^_» `p "^" («term_-_» `n "-" `i))])
          ", "
          («term_*_»
           («term_*_»
            («term_^_»
             («term_^_» (Term.app `x [`i]) "^" `p)
             "^"
             («term_-_» («term_^_» `p "^" («term_-_» `n "-" `i)) "-" («term_+_» `j "+" (num "1"))))
            "*"
            («term_^_» (Term.app `frobenius_poly_aux [`i]) "^" («term_+_» `j "+" (num "1"))))
           "*"
           (Term.app
            `c
            [(coeNotation
              "↑"
              (Term.typeAscription
               "("
               («term_*_»
                («term_/_»
                 (Term.app
                  (Term.proj («term_^_» `p "^" («term_-_» `n "-" `i)) "." `choose)
                  [(«term_+_» `j "+" (num "1"))])
                 "/"
                 («term_^_»
                  `p
                  "^"
                  («term_-_»
                   («term_-_» `n "-" `i)
                   "-"
                   (Term.app
                    (WittVector.RingTheory.WittVector.Frobenius.termv "v")
                    [`p
                     (Term.anonymousCtor
                      "⟨"
                      [(«term_+_» `j "+" (num "1")) "," (Term.app `Nat.succ_pos [`j])]
                      "⟩")]))))
                "*"
                («term_^_»
                 (coeNotation "↑" `p)
                 "^"
                 («term_-_»
                  `j
                  "-"
                  (Term.app
                   (WittVector.RingTheory.WittVector.Frobenius.termv "v")
                   [`p
                    (Term.anonymousCtor
                     "⟨"
                     [(«term_+_» `j "+" (num "1")) "," (Term.app `Nat.succ_pos [`j])]
                     "⟩")]))))
               ":"
               [(termℕ "ℕ")]
               ")"))]))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
       "∑"
       (Std.ExtendedBinder.extBinders
        (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) [(group ":" (Term.app `Fin [`n]))]))
       ", "
       (Term.have
        "have"
        (Term.haveDecl (Term.haveIdDecl [] [] ":=" (Term.proj `i "." `is_lt)))
        []
        (BigOperators.Algebra.BigOperators.Basic.finset.sum
         "∑"
         (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `j) []))
         " in "
         (Term.app `range [(«term_^_» `p "^" («term_-_» `n "-" `i))])
         ", "
         («term_*_»
          («term_*_»
           («term_^_»
            («term_^_» (Term.app `x [`i]) "^" `p)
            "^"
            («term_-_» («term_^_» `p "^" («term_-_» `n "-" `i)) "-" («term_+_» `j "+" (num "1"))))
           "*"
           («term_^_» (Term.app `frobenius_poly_aux [`i]) "^" («term_+_» `j "+" (num "1"))))
          "*"
          (Term.app
           `c
           [(coeNotation
             "↑"
             (Term.typeAscription
              "("
              («term_*_»
               («term_/_»
                (Term.app
                 (Term.proj («term_^_» `p "^" («term_-_» `n "-" `i)) "." `choose)
                 [(«term_+_» `j "+" (num "1"))])
                "/"
                («term_^_»
                 `p
                 "^"
                 («term_-_»
                  («term_-_» `n "-" `i)
                  "-"
                  (Term.app
                   (WittVector.RingTheory.WittVector.Frobenius.termv "v")
                   [`p
                    (Term.anonymousCtor
                     "⟨"
                     [(«term_+_» `j "+" (num "1")) "," (Term.app `Nat.succ_pos [`j])]
                     "⟩")]))))
               "*"
               («term_^_»
                (coeNotation "↑" `p)
                "^"
                («term_-_»
                 `j
                 "-"
                 (Term.app
                  (WittVector.RingTheory.WittVector.Frobenius.termv "v")
                  [`p
                   (Term.anonymousCtor
                    "⟨"
                    [(«term_+_» `j "+" (num "1")) "," (Term.app `Nat.succ_pos [`j])]
                    "⟩")]))))
              ":"
              [(termℕ "ℕ")]
              ")"))])))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.have
       "have"
       (Term.haveDecl (Term.haveIdDecl [] [] ":=" (Term.proj `i "." `is_lt)))
       []
       (BigOperators.Algebra.BigOperators.Basic.finset.sum
        "∑"
        (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `j) []))
        " in "
        (Term.app `range [(«term_^_» `p "^" («term_-_» `n "-" `i))])
        ", "
        («term_*_»
         («term_*_»
          («term_^_»
           («term_^_» (Term.app `x [`i]) "^" `p)
           "^"
           («term_-_» («term_^_» `p "^" («term_-_» `n "-" `i)) "-" («term_+_» `j "+" (num "1"))))
          "*"
          («term_^_» (Term.app `frobenius_poly_aux [`i]) "^" («term_+_» `j "+" (num "1"))))
         "*"
         (Term.app
          `c
          [(coeNotation
            "↑"
            (Term.typeAscription
             "("
             («term_*_»
              («term_/_»
               (Term.app
                (Term.proj («term_^_» `p "^" («term_-_» `n "-" `i)) "." `choose)
                [(«term_+_» `j "+" (num "1"))])
               "/"
               («term_^_»
                `p
                "^"
                («term_-_»
                 («term_-_» `n "-" `i)
                 "-"
                 (Term.app
                  (WittVector.RingTheory.WittVector.Frobenius.termv "v")
                  [`p
                   (Term.anonymousCtor
                    "⟨"
                    [(«term_+_» `j "+" (num "1")) "," (Term.app `Nat.succ_pos [`j])]
                    "⟩")]))))
              "*"
              («term_^_»
               (coeNotation "↑" `p)
               "^"
               («term_-_»
                `j
                "-"
                (Term.app
                 (WittVector.RingTheory.WittVector.Frobenius.termv "v")
                 [`p
                  (Term.anonymousCtor
                   "⟨"
                   [(«term_+_» `j "+" (num "1")) "," (Term.app `Nat.succ_pos [`j])]
                   "⟩")]))))
             ":"
             [(termℕ "ℕ")]
             ")"))]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (BigOperators.Algebra.BigOperators.Basic.finset.sum
       "∑"
       (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `j) []))
       " in "
       (Term.app `range [(«term_^_» `p "^" («term_-_» `n "-" `i))])
       ", "
       («term_*_»
        («term_*_»
         («term_^_»
          («term_^_» (Term.app `x [`i]) "^" `p)
          "^"
          («term_-_» («term_^_» `p "^" («term_-_» `n "-" `i)) "-" («term_+_» `j "+" (num "1"))))
         "*"
         («term_^_» (Term.app `frobenius_poly_aux [`i]) "^" («term_+_» `j "+" (num "1"))))
        "*"
        (Term.app
         `c
         [(coeNotation
           "↑"
           (Term.typeAscription
            "("
            («term_*_»
             («term_/_»
              (Term.app
               (Term.proj («term_^_» `p "^" («term_-_» `n "-" `i)) "." `choose)
               [(«term_+_» `j "+" (num "1"))])
              "/"
              («term_^_»
               `p
               "^"
               («term_-_»
                («term_-_» `n "-" `i)
                "-"
                (Term.app
                 (WittVector.RingTheory.WittVector.Frobenius.termv "v")
                 [`p
                  (Term.anonymousCtor
                   "⟨"
                   [(«term_+_» `j "+" (num "1")) "," (Term.app `Nat.succ_pos [`j])]
                   "⟩")]))))
             "*"
             («term_^_»
              (coeNotation "↑" `p)
              "^"
              («term_-_»
               `j
               "-"
               (Term.app
                (WittVector.RingTheory.WittVector.Frobenius.termv "v")
                [`p
                 (Term.anonymousCtor
                  "⟨"
                  [(«term_+_» `j "+" (num "1")) "," (Term.app `Nat.succ_pos [`j])]
                  "⟩")]))))
            ":"
            [(termℕ "ℕ")]
            ")"))])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_»
       («term_*_»
        («term_^_»
         («term_^_» (Term.app `x [`i]) "^" `p)
         "^"
         («term_-_» («term_^_» `p "^" («term_-_» `n "-" `i)) "-" («term_+_» `j "+" (num "1"))))
        "*"
        («term_^_» (Term.app `frobenius_poly_aux [`i]) "^" («term_+_» `j "+" (num "1"))))
       "*"
       (Term.app
        `c
        [(coeNotation
          "↑"
          (Term.typeAscription
           "("
           («term_*_»
            («term_/_»
             (Term.app
              (Term.proj («term_^_» `p "^" («term_-_» `n "-" `i)) "." `choose)
              [(«term_+_» `j "+" (num "1"))])
             "/"
             («term_^_»
              `p
              "^"
              («term_-_»
               («term_-_» `n "-" `i)
               "-"
               (Term.app
                (WittVector.RingTheory.WittVector.Frobenius.termv "v")
                [`p
                 (Term.anonymousCtor
                  "⟨"
                  [(«term_+_» `j "+" (num "1")) "," (Term.app `Nat.succ_pos [`j])]
                  "⟩")]))))
            "*"
            («term_^_»
             (coeNotation "↑" `p)
             "^"
             («term_-_»
              `j
              "-"
              (Term.app
               (WittVector.RingTheory.WittVector.Frobenius.termv "v")
               [`p
                (Term.anonymousCtor
                 "⟨"
                 [(«term_+_» `j "+" (num "1")) "," (Term.app `Nat.succ_pos [`j])]
                 "⟩")]))))
           ":"
           [(termℕ "ℕ")]
           ")"))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `c
       [(coeNotation
         "↑"
         (Term.typeAscription
          "("
          («term_*_»
           («term_/_»
            (Term.app
             (Term.proj («term_^_» `p "^" («term_-_» `n "-" `i)) "." `choose)
             [(«term_+_» `j "+" (num "1"))])
            "/"
            («term_^_»
             `p
             "^"
             («term_-_»
              («term_-_» `n "-" `i)
              "-"
              (Term.app
               (WittVector.RingTheory.WittVector.Frobenius.termv "v")
               [`p
                (Term.anonymousCtor
                 "⟨"
                 [(«term_+_» `j "+" (num "1")) "," (Term.app `Nat.succ_pos [`j])]
                 "⟩")]))))
           "*"
           («term_^_»
            (coeNotation "↑" `p)
            "^"
            («term_-_»
             `j
             "-"
             (Term.app
              (WittVector.RingTheory.WittVector.Frobenius.termv "v")
              [`p
               (Term.anonymousCtor
                "⟨"
                [(«term_+_» `j "+" (num "1")) "," (Term.app `Nat.succ_pos [`j])]
                "⟩")]))))
          ":"
          [(termℕ "ℕ")]
          ")"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'coeNotation', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'coeNotation', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (coeNotation
       "↑"
       (Term.typeAscription
        "("
        («term_*_»
         («term_/_»
          (Term.app
           (Term.proj («term_^_» `p "^" («term_-_» `n "-" `i)) "." `choose)
           [(«term_+_» `j "+" (num "1"))])
          "/"
          («term_^_»
           `p
           "^"
           («term_-_»
            («term_-_» `n "-" `i)
            "-"
            (Term.app
             (WittVector.RingTheory.WittVector.Frobenius.termv "v")
             [`p
              (Term.anonymousCtor
               "⟨"
               [(«term_+_» `j "+" (num "1")) "," (Term.app `Nat.succ_pos [`j])]
               "⟩")]))))
         "*"
         («term_^_»
          (coeNotation "↑" `p)
          "^"
          («term_-_»
           `j
           "-"
           (Term.app
            (WittVector.RingTheory.WittVector.Frobenius.termv "v")
            [`p
             (Term.anonymousCtor
              "⟨"
              [(«term_+_» `j "+" (num "1")) "," (Term.app `Nat.succ_pos [`j])]
              "⟩")]))))
        ":"
        [(termℕ "ℕ")]
        ")"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription
       "("
       («term_*_»
        («term_/_»
         (Term.app
          (Term.proj («term_^_» `p "^" («term_-_» `n "-" `i)) "." `choose)
          [(«term_+_» `j "+" (num "1"))])
         "/"
         («term_^_»
          `p
          "^"
          («term_-_»
           («term_-_» `n "-" `i)
           "-"
           (Term.app
            (WittVector.RingTheory.WittVector.Frobenius.termv "v")
            [`p
             (Term.anonymousCtor
              "⟨"
              [(«term_+_» `j "+" (num "1")) "," (Term.app `Nat.succ_pos [`j])]
              "⟩")]))))
        "*"
        («term_^_»
         (coeNotation "↑" `p)
         "^"
         («term_-_»
          `j
          "-"
          (Term.app
           (WittVector.RingTheory.WittVector.Frobenius.termv "v")
           [`p
            (Term.anonymousCtor
             "⟨"
             [(«term_+_» `j "+" (num "1")) "," (Term.app `Nat.succ_pos [`j])]
             "⟩")]))))
       ":"
       [(termℕ "ℕ")]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (termℕ "ℕ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_»
       («term_/_»
        (Term.app
         (Term.proj («term_^_» `p "^" («term_-_» `n "-" `i)) "." `choose)
         [(«term_+_» `j "+" (num "1"))])
        "/"
        («term_^_»
         `p
         "^"
         («term_-_»
          («term_-_» `n "-" `i)
          "-"
          (Term.app
           (WittVector.RingTheory.WittVector.Frobenius.termv "v")
           [`p
            (Term.anonymousCtor
             "⟨"
             [(«term_+_» `j "+" (num "1")) "," (Term.app `Nat.succ_pos [`j])]
             "⟩")]))))
       "*"
       («term_^_»
        (coeNotation "↑" `p)
        "^"
        («term_-_»
         `j
         "-"
         (Term.app
          (WittVector.RingTheory.WittVector.Frobenius.termv "v")
          [`p
           (Term.anonymousCtor
            "⟨"
            [(«term_+_» `j "+" (num "1")) "," (Term.app `Nat.succ_pos [`j])]
            "⟩")]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_»
       (coeNotation "↑" `p)
       "^"
       («term_-_»
        `j
        "-"
        (Term.app
         (WittVector.RingTheory.WittVector.Frobenius.termv "v")
         [`p
          (Term.anonymousCtor
           "⟨"
           [(«term_+_» `j "+" (num "1")) "," (Term.app `Nat.succ_pos [`j])]
           "⟩")])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_-_»
       `j
       "-"
       (Term.app
        (WittVector.RingTheory.WittVector.Frobenius.termv "v")
        [`p
         (Term.anonymousCtor
          "⟨"
          [(«term_+_» `j "+" (num "1")) "," (Term.app `Nat.succ_pos [`j])]
          "⟩")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (WittVector.RingTheory.WittVector.Frobenius.termv "v")
       [`p
        (Term.anonymousCtor
         "⟨"
         [(«term_+_» `j "+" (num "1")) "," (Term.app `Nat.succ_pos [`j])]
         "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [(«term_+_» `j "+" (num "1")) "," (Term.app `Nat.succ_pos [`j])] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Nat.succ_pos [`j])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `j
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Nat.succ_pos
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_» `j "+" (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `j
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (WittVector.RingTheory.WittVector.Frobenius.termv "v")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'WittVector.RingTheory.WittVector.Frobenius.termv', expected 'WittVector.RingTheory.WittVector.Frobenius.termv._@.RingTheory.WittVector.Frobenius._hyg.519'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValEqns', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
      An auxiliary polynomial over the integers, that satisfies
      `p * (frobenius_poly_aux p n) + X n ^ p = frobenius_poly p n`.
      This makes it easy to show that `frobenius_poly p n` is congruent to `X n ^ p`
      modulo `p`. -/
    noncomputable
  def
    frobeniusPolyAux
    : ℕ → MvPolynomial ℕ ℤ
    |
      n
      =>
      x n + 1
        -
        ∑
          i : Fin n
          ,
          have
            := i . is_lt
            ∑
              j
              in
              range p ^ n - i
              ,
              x i ^ p ^ p ^ n - i - j + 1 * frobenius_poly_aux i ^ j + 1
                *
                c
                  ↑
                    (
                      p ^ n - i . choose j + 1 / p ^ n - i - v p ⟨ j + 1 , Nat.succ_pos j ⟩
                        *
                        ↑ p ^ j - v p ⟨ j + 1 , Nat.succ_pos j ⟩
                      :
                      ℕ
                      )
#align witt_vector.frobenius_poly_aux WittVector.frobeniusPolyAux

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `frobenius_poly_aux_eq [])
      (Command.declSig
       [(Term.explicitBinder "(" [`n] [":" (termℕ "ℕ")] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app `frobeniusPolyAux [`p `n])
         "="
         («term_-_»
          (Term.app `x [(«term_+_» `n "+" (num "1"))])
          "-"
          (BigOperators.Algebra.BigOperators.Basic.finset.sum
           "∑"
           (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
           " in "
           (Term.app `range [`n])
           ", "
           (BigOperators.Algebra.BigOperators.Basic.finset.sum
            "∑"
            (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `j) []))
            " in "
            (Term.app `range [(«term_^_» `p "^" («term_-_» `n "-" `i))])
            ", "
            («term_*_»
             («term_*_»
              («term_^_»
               («term_^_» (Term.app `x [`i]) "^" `p)
               "^"
               («term_-_»
                («term_^_» `p "^" («term_-_» `n "-" `i))
                "-"
                («term_+_» `j "+" (num "1"))))
              "*"
              («term_^_» (Term.app `frobeniusPolyAux [`p `i]) "^" («term_+_» `j "+" (num "1"))))
             "*"
             (Term.app
              `c
              [(coeNotation
                "↑"
                (Term.typeAscription
                 "("
                 («term_*_»
                  («term_/_»
                   (Term.app
                    (Term.proj («term_^_» `p "^" («term_-_» `n "-" `i)) "." `choose)
                    [(«term_+_» `j "+" (num "1"))])
                   "/"
                   («term_^_»
                    `p
                    "^"
                    («term_-_»
                     («term_-_» `n "-" `i)
                     "-"
                     (Term.app
                      (WittVector.RingTheory.WittVector.Frobenius.termv "v")
                      [`p
                       (Term.anonymousCtor
                        "⟨"
                        [(«term_+_» `j "+" (num "1")) "," (Term.app `Nat.succ_pos [`j])]
                        "⟩")]))))
                  "*"
                  («term_^_»
                   (coeNotation "↑" `p)
                   "^"
                   («term_-_»
                    `j
                    "-"
                    (Term.app
                     (WittVector.RingTheory.WittVector.Frobenius.termv "v")
                     [`p
                      (Term.anonymousCtor
                       "⟨"
                       [(«term_+_» `j "+" (num "1")) "," (Term.app `Nat.succ_pos [`j])]
                       "⟩")]))))
                 ":"
                 [(termℕ "ℕ")]
                 ")"))]))))))))
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
             [(Tactic.rwRule [] `frobenius_poly_aux)
              ","
              (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Fin.sum_univ_eq_sum_range)]
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
         [(Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `frobenius_poly_aux)
             ","
             (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Fin.sum_univ_eq_sum_range)]
            "]")
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `frobenius_poly_aux)
         ","
         (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Fin.sum_univ_eq_sum_range)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Fin.sum_univ_eq_sum_range
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `frobenius_poly_aux
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app `frobeniusPolyAux [`p `n])
       "="
       («term_-_»
        (Term.app `x [(«term_+_» `n "+" (num "1"))])
        "-"
        (BigOperators.Algebra.BigOperators.Basic.finset.sum
         "∑"
         (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
         " in "
         (Term.app `range [`n])
         ", "
         (BigOperators.Algebra.BigOperators.Basic.finset.sum
          "∑"
          (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `j) []))
          " in "
          (Term.app `range [(«term_^_» `p "^" («term_-_» `n "-" `i))])
          ", "
          («term_*_»
           («term_*_»
            («term_^_»
             («term_^_» (Term.app `x [`i]) "^" `p)
             "^"
             («term_-_» («term_^_» `p "^" («term_-_» `n "-" `i)) "-" («term_+_» `j "+" (num "1"))))
            "*"
            («term_^_» (Term.app `frobeniusPolyAux [`p `i]) "^" («term_+_» `j "+" (num "1"))))
           "*"
           (Term.app
            `c
            [(coeNotation
              "↑"
              (Term.typeAscription
               "("
               («term_*_»
                («term_/_»
                 (Term.app
                  (Term.proj («term_^_» `p "^" («term_-_» `n "-" `i)) "." `choose)
                  [(«term_+_» `j "+" (num "1"))])
                 "/"
                 («term_^_»
                  `p
                  "^"
                  («term_-_»
                   («term_-_» `n "-" `i)
                   "-"
                   (Term.app
                    (WittVector.RingTheory.WittVector.Frobenius.termv "v")
                    [`p
                     (Term.anonymousCtor
                      "⟨"
                      [(«term_+_» `j "+" (num "1")) "," (Term.app `Nat.succ_pos [`j])]
                      "⟩")]))))
                "*"
                («term_^_»
                 (coeNotation "↑" `p)
                 "^"
                 («term_-_»
                  `j
                  "-"
                  (Term.app
                   (WittVector.RingTheory.WittVector.Frobenius.termv "v")
                   [`p
                    (Term.anonymousCtor
                     "⟨"
                     [(«term_+_» `j "+" (num "1")) "," (Term.app `Nat.succ_pos [`j])]
                     "⟩")]))))
               ":"
               [(termℕ "ℕ")]
               ")"))]))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_-_»
       (Term.app `x [(«term_+_» `n "+" (num "1"))])
       "-"
       (BigOperators.Algebra.BigOperators.Basic.finset.sum
        "∑"
        (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
        " in "
        (Term.app `range [`n])
        ", "
        (BigOperators.Algebra.BigOperators.Basic.finset.sum
         "∑"
         (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `j) []))
         " in "
         (Term.app `range [(«term_^_» `p "^" («term_-_» `n "-" `i))])
         ", "
         («term_*_»
          («term_*_»
           («term_^_»
            («term_^_» (Term.app `x [`i]) "^" `p)
            "^"
            («term_-_» («term_^_» `p "^" («term_-_» `n "-" `i)) "-" («term_+_» `j "+" (num "1"))))
           "*"
           («term_^_» (Term.app `frobeniusPolyAux [`p `i]) "^" («term_+_» `j "+" (num "1"))))
          "*"
          (Term.app
           `c
           [(coeNotation
             "↑"
             (Term.typeAscription
              "("
              («term_*_»
               («term_/_»
                (Term.app
                 (Term.proj («term_^_» `p "^" («term_-_» `n "-" `i)) "." `choose)
                 [(«term_+_» `j "+" (num "1"))])
                "/"
                («term_^_»
                 `p
                 "^"
                 («term_-_»
                  («term_-_» `n "-" `i)
                  "-"
                  (Term.app
                   (WittVector.RingTheory.WittVector.Frobenius.termv "v")
                   [`p
                    (Term.anonymousCtor
                     "⟨"
                     [(«term_+_» `j "+" (num "1")) "," (Term.app `Nat.succ_pos [`j])]
                     "⟩")]))))
               "*"
               («term_^_»
                (coeNotation "↑" `p)
                "^"
                («term_-_»
                 `j
                 "-"
                 (Term.app
                  (WittVector.RingTheory.WittVector.Frobenius.termv "v")
                  [`p
                   (Term.anonymousCtor
                    "⟨"
                    [(«term_+_» `j "+" (num "1")) "," (Term.app `Nat.succ_pos [`j])]
                    "⟩")]))))
              ":"
              [(termℕ "ℕ")]
              ")"))])))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (BigOperators.Algebra.BigOperators.Basic.finset.sum
       "∑"
       (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
       " in "
       (Term.app `range [`n])
       ", "
       (BigOperators.Algebra.BigOperators.Basic.finset.sum
        "∑"
        (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `j) []))
        " in "
        (Term.app `range [(«term_^_» `p "^" («term_-_» `n "-" `i))])
        ", "
        («term_*_»
         («term_*_»
          («term_^_»
           («term_^_» (Term.app `x [`i]) "^" `p)
           "^"
           («term_-_» («term_^_» `p "^" («term_-_» `n "-" `i)) "-" («term_+_» `j "+" (num "1"))))
          "*"
          («term_^_» (Term.app `frobeniusPolyAux [`p `i]) "^" («term_+_» `j "+" (num "1"))))
         "*"
         (Term.app
          `c
          [(coeNotation
            "↑"
            (Term.typeAscription
             "("
             («term_*_»
              («term_/_»
               (Term.app
                (Term.proj («term_^_» `p "^" («term_-_» `n "-" `i)) "." `choose)
                [(«term_+_» `j "+" (num "1"))])
               "/"
               («term_^_»
                `p
                "^"
                («term_-_»
                 («term_-_» `n "-" `i)
                 "-"
                 (Term.app
                  (WittVector.RingTheory.WittVector.Frobenius.termv "v")
                  [`p
                   (Term.anonymousCtor
                    "⟨"
                    [(«term_+_» `j "+" (num "1")) "," (Term.app `Nat.succ_pos [`j])]
                    "⟩")]))))
              "*"
              («term_^_»
               (coeNotation "↑" `p)
               "^"
               («term_-_»
                `j
                "-"
                (Term.app
                 (WittVector.RingTheory.WittVector.Frobenius.termv "v")
                 [`p
                  (Term.anonymousCtor
                   "⟨"
                   [(«term_+_» `j "+" (num "1")) "," (Term.app `Nat.succ_pos [`j])]
                   "⟩")]))))
             ":"
             [(termℕ "ℕ")]
             ")"))]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (BigOperators.Algebra.BigOperators.Basic.finset.sum
       "∑"
       (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `j) []))
       " in "
       (Term.app `range [(«term_^_» `p "^" («term_-_» `n "-" `i))])
       ", "
       («term_*_»
        («term_*_»
         («term_^_»
          («term_^_» (Term.app `x [`i]) "^" `p)
          "^"
          («term_-_» («term_^_» `p "^" («term_-_» `n "-" `i)) "-" («term_+_» `j "+" (num "1"))))
         "*"
         («term_^_» (Term.app `frobeniusPolyAux [`p `i]) "^" («term_+_» `j "+" (num "1"))))
        "*"
        (Term.app
         `c
         [(coeNotation
           "↑"
           (Term.typeAscription
            "("
            («term_*_»
             («term_/_»
              (Term.app
               (Term.proj («term_^_» `p "^" («term_-_» `n "-" `i)) "." `choose)
               [(«term_+_» `j "+" (num "1"))])
              "/"
              («term_^_»
               `p
               "^"
               («term_-_»
                («term_-_» `n "-" `i)
                "-"
                (Term.app
                 (WittVector.RingTheory.WittVector.Frobenius.termv "v")
                 [`p
                  (Term.anonymousCtor
                   "⟨"
                   [(«term_+_» `j "+" (num "1")) "," (Term.app `Nat.succ_pos [`j])]
                   "⟩")]))))
             "*"
             («term_^_»
              (coeNotation "↑" `p)
              "^"
              («term_-_»
               `j
               "-"
               (Term.app
                (WittVector.RingTheory.WittVector.Frobenius.termv "v")
                [`p
                 (Term.anonymousCtor
                  "⟨"
                  [(«term_+_» `j "+" (num "1")) "," (Term.app `Nat.succ_pos [`j])]
                  "⟩")]))))
            ":"
            [(termℕ "ℕ")]
            ")"))])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_»
       («term_*_»
        («term_^_»
         («term_^_» (Term.app `x [`i]) "^" `p)
         "^"
         («term_-_» («term_^_» `p "^" («term_-_» `n "-" `i)) "-" («term_+_» `j "+" (num "1"))))
        "*"
        («term_^_» (Term.app `frobeniusPolyAux [`p `i]) "^" («term_+_» `j "+" (num "1"))))
       "*"
       (Term.app
        `c
        [(coeNotation
          "↑"
          (Term.typeAscription
           "("
           («term_*_»
            («term_/_»
             (Term.app
              (Term.proj («term_^_» `p "^" («term_-_» `n "-" `i)) "." `choose)
              [(«term_+_» `j "+" (num "1"))])
             "/"
             («term_^_»
              `p
              "^"
              («term_-_»
               («term_-_» `n "-" `i)
               "-"
               (Term.app
                (WittVector.RingTheory.WittVector.Frobenius.termv "v")
                [`p
                 (Term.anonymousCtor
                  "⟨"
                  [(«term_+_» `j "+" (num "1")) "," (Term.app `Nat.succ_pos [`j])]
                  "⟩")]))))
            "*"
            («term_^_»
             (coeNotation "↑" `p)
             "^"
             («term_-_»
              `j
              "-"
              (Term.app
               (WittVector.RingTheory.WittVector.Frobenius.termv "v")
               [`p
                (Term.anonymousCtor
                 "⟨"
                 [(«term_+_» `j "+" (num "1")) "," (Term.app `Nat.succ_pos [`j])]
                 "⟩")]))))
           ":"
           [(termℕ "ℕ")]
           ")"))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `c
       [(coeNotation
         "↑"
         (Term.typeAscription
          "("
          («term_*_»
           («term_/_»
            (Term.app
             (Term.proj («term_^_» `p "^" («term_-_» `n "-" `i)) "." `choose)
             [(«term_+_» `j "+" (num "1"))])
            "/"
            («term_^_»
             `p
             "^"
             («term_-_»
              («term_-_» `n "-" `i)
              "-"
              (Term.app
               (WittVector.RingTheory.WittVector.Frobenius.termv "v")
               [`p
                (Term.anonymousCtor
                 "⟨"
                 [(«term_+_» `j "+" (num "1")) "," (Term.app `Nat.succ_pos [`j])]
                 "⟩")]))))
           "*"
           («term_^_»
            (coeNotation "↑" `p)
            "^"
            («term_-_»
             `j
             "-"
             (Term.app
              (WittVector.RingTheory.WittVector.Frobenius.termv "v")
              [`p
               (Term.anonymousCtor
                "⟨"
                [(«term_+_» `j "+" (num "1")) "," (Term.app `Nat.succ_pos [`j])]
                "⟩")]))))
          ":"
          [(termℕ "ℕ")]
          ")"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'coeNotation', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'coeNotation', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (coeNotation
       "↑"
       (Term.typeAscription
        "("
        («term_*_»
         («term_/_»
          (Term.app
           (Term.proj («term_^_» `p "^" («term_-_» `n "-" `i)) "." `choose)
           [(«term_+_» `j "+" (num "1"))])
          "/"
          («term_^_»
           `p
           "^"
           («term_-_»
            («term_-_» `n "-" `i)
            "-"
            (Term.app
             (WittVector.RingTheory.WittVector.Frobenius.termv "v")
             [`p
              (Term.anonymousCtor
               "⟨"
               [(«term_+_» `j "+" (num "1")) "," (Term.app `Nat.succ_pos [`j])]
               "⟩")]))))
         "*"
         («term_^_»
          (coeNotation "↑" `p)
          "^"
          («term_-_»
           `j
           "-"
           (Term.app
            (WittVector.RingTheory.WittVector.Frobenius.termv "v")
            [`p
             (Term.anonymousCtor
              "⟨"
              [(«term_+_» `j "+" (num "1")) "," (Term.app `Nat.succ_pos [`j])]
              "⟩")]))))
        ":"
        [(termℕ "ℕ")]
        ")"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription
       "("
       («term_*_»
        («term_/_»
         (Term.app
          (Term.proj («term_^_» `p "^" («term_-_» `n "-" `i)) "." `choose)
          [(«term_+_» `j "+" (num "1"))])
         "/"
         («term_^_»
          `p
          "^"
          («term_-_»
           («term_-_» `n "-" `i)
           "-"
           (Term.app
            (WittVector.RingTheory.WittVector.Frobenius.termv "v")
            [`p
             (Term.anonymousCtor
              "⟨"
              [(«term_+_» `j "+" (num "1")) "," (Term.app `Nat.succ_pos [`j])]
              "⟩")]))))
        "*"
        («term_^_»
         (coeNotation "↑" `p)
         "^"
         («term_-_»
          `j
          "-"
          (Term.app
           (WittVector.RingTheory.WittVector.Frobenius.termv "v")
           [`p
            (Term.anonymousCtor
             "⟨"
             [(«term_+_» `j "+" (num "1")) "," (Term.app `Nat.succ_pos [`j])]
             "⟩")]))))
       ":"
       [(termℕ "ℕ")]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (termℕ "ℕ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_»
       («term_/_»
        (Term.app
         (Term.proj («term_^_» `p "^" («term_-_» `n "-" `i)) "." `choose)
         [(«term_+_» `j "+" (num "1"))])
        "/"
        («term_^_»
         `p
         "^"
         («term_-_»
          («term_-_» `n "-" `i)
          "-"
          (Term.app
           (WittVector.RingTheory.WittVector.Frobenius.termv "v")
           [`p
            (Term.anonymousCtor
             "⟨"
             [(«term_+_» `j "+" (num "1")) "," (Term.app `Nat.succ_pos [`j])]
             "⟩")]))))
       "*"
       («term_^_»
        (coeNotation "↑" `p)
        "^"
        («term_-_»
         `j
         "-"
         (Term.app
          (WittVector.RingTheory.WittVector.Frobenius.termv "v")
          [`p
           (Term.anonymousCtor
            "⟨"
            [(«term_+_» `j "+" (num "1")) "," (Term.app `Nat.succ_pos [`j])]
            "⟩")]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_»
       (coeNotation "↑" `p)
       "^"
       («term_-_»
        `j
        "-"
        (Term.app
         (WittVector.RingTheory.WittVector.Frobenius.termv "v")
         [`p
          (Term.anonymousCtor
           "⟨"
           [(«term_+_» `j "+" (num "1")) "," (Term.app `Nat.succ_pos [`j])]
           "⟩")])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_-_»
       `j
       "-"
       (Term.app
        (WittVector.RingTheory.WittVector.Frobenius.termv "v")
        [`p
         (Term.anonymousCtor
          "⟨"
          [(«term_+_» `j "+" (num "1")) "," (Term.app `Nat.succ_pos [`j])]
          "⟩")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (WittVector.RingTheory.WittVector.Frobenius.termv "v")
       [`p
        (Term.anonymousCtor
         "⟨"
         [(«term_+_» `j "+" (num "1")) "," (Term.app `Nat.succ_pos [`j])]
         "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [(«term_+_» `j "+" (num "1")) "," (Term.app `Nat.succ_pos [`j])] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Nat.succ_pos [`j])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `j
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Nat.succ_pos
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_» `j "+" (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `j
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (WittVector.RingTheory.WittVector.Frobenius.termv "v")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'WittVector.RingTheory.WittVector.Frobenius.termv', expected 'WittVector.RingTheory.WittVector.Frobenius.termv._@.RingTheory.WittVector.Frobenius._hyg.519'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  frobenius_poly_aux_eq
  ( n : ℕ )
    :
      frobeniusPolyAux p n
        =
        x n + 1
          -
          ∑
            i
            in
            range n
            ,
            ∑
              j
              in
              range p ^ n - i
              ,
              x i ^ p ^ p ^ n - i - j + 1 * frobeniusPolyAux p i ^ j + 1
                *
                c
                  ↑
                    (
                      p ^ n - i . choose j + 1 / p ^ n - i - v p ⟨ j + 1 , Nat.succ_pos j ⟩
                        *
                        ↑ p ^ j - v p ⟨ j + 1 , Nat.succ_pos j ⟩
                      :
                      ℕ
                      )
  := by rw [ frobenius_poly_aux , ← Fin.sum_univ_eq_sum_range ]
#align witt_vector.frobenius_poly_aux_eq WittVector.frobenius_poly_aux_eq

/-- The polynomials that give the coefficients of `frobenius x`,
in terms of the coefficients of `x`. -/
def frobeniusPoly (n : ℕ) : MvPolynomial ℕ ℤ :=
  x n ^ p + c ↑p * frobeniusPolyAux p n
#align witt_vector.frobenius_poly WittVector.frobeniusPoly

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "A key divisibility fact for the proof of `witt_vector.map_frobenius_poly`. -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `MapFrobeniusPoly.key₁ [])
      (Command.declSig
       [(Term.explicitBinder "(" [`n `j] [":" (termℕ "ℕ")] [] ")")
        (Term.explicitBinder "(" [`hj] [":" («term_<_» `j "<" («term_^_» `p "^" `n))] [] ")")]
       (Term.typeSpec
        ":"
        («term_∣_»
         («term_^_»
          `p
          "^"
          («term_-_»
           `n
           "-"
           (Term.app
            (WittVector.RingTheory.WittVector.Frobenius.termv "v")
            [`p
             (Term.anonymousCtor
              "⟨"
              [(«term_+_» `j "+" (num "1")) "," (Term.proj `j "." `succ_pos)]
              "⟩")])))
         "∣"
         (Term.app (Term.proj («term_^_» `p "^" `n) "." `choose) [(«term_+_» `j "+" (num "1"))]))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.apply "apply" `multiplicity.pow_dvd_of_le_multiplicity)
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`aux []]
              [(Term.typeSpec
                ":"
                (Term.proj
                 (Term.app
                  `multiplicity
                  [`p
                   (Term.app
                    (Term.proj («term_^_» `p "^" `n) "." `choose)
                    [(«term_+_» `j "+" (num "1"))])])
                 "."
                 `Dom))]
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
                    [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `multiplicity.finite_iff_dom)
                     ","
                     (Tactic.rwRule [] `multiplicity.finite_nat_iff)]
                    "]")
                   [])
                  []
                  (Tactic.exact
                   "exact"
                   (Term.anonymousCtor
                    "⟨"
                    [(Term.proj (Term.proj `hp "." (fieldIdx "1")) "." `ne_one)
                     ","
                     (Term.app `Nat.choose_pos [`hj])]
                    "⟩"))]))))))
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] (Term.app `PartEnat.coe_get [`aux]))
              ","
              (Tactic.rwRule [] `PartEnat.coe_le_coe)
              ","
              (Tactic.rwRule [] `tsub_le_iff_left)
              ","
              (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `PartEnat.coe_le_coe)
              ","
              (Tactic.rwRule [] `Nat.cast_add)
              ","
              (Tactic.rwRule [] `pnat_multiplicity)
              ","
              (Tactic.rwRule [] `PartEnat.coe_get)
              ","
              (Tactic.rwRule [] `PartEnat.coe_get)
              ","
              (Tactic.rwRule [] `add_comm)]
             "]")
            [])
           []
           (Tactic.exact
            "exact"
            (Term.proj
             (Term.app
              (Term.proj (Term.proj `hp "." (fieldIdx "1")) "." `multiplicity_choose_prime_pow)
              [`hj `j.succ_pos])
             "."
             `ge))])))
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
         [(Tactic.apply "apply" `multiplicity.pow_dvd_of_le_multiplicity)
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`aux []]
             [(Term.typeSpec
               ":"
               (Term.proj
                (Term.app
                 `multiplicity
                 [`p
                  (Term.app
                   (Term.proj («term_^_» `p "^" `n) "." `choose)
                   [(«term_+_» `j "+" (num "1"))])])
                "."
                `Dom))]
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
                   [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `multiplicity.finite_iff_dom)
                    ","
                    (Tactic.rwRule [] `multiplicity.finite_nat_iff)]
                   "]")
                  [])
                 []
                 (Tactic.exact
                  "exact"
                  (Term.anonymousCtor
                   "⟨"
                   [(Term.proj (Term.proj `hp "." (fieldIdx "1")) "." `ne_one)
                    ","
                    (Term.app `Nat.choose_pos [`hj])]
                   "⟩"))]))))))
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] (Term.app `PartEnat.coe_get [`aux]))
             ","
             (Tactic.rwRule [] `PartEnat.coe_le_coe)
             ","
             (Tactic.rwRule [] `tsub_le_iff_left)
             ","
             (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `PartEnat.coe_le_coe)
             ","
             (Tactic.rwRule [] `Nat.cast_add)
             ","
             (Tactic.rwRule [] `pnat_multiplicity)
             ","
             (Tactic.rwRule [] `PartEnat.coe_get)
             ","
             (Tactic.rwRule [] `PartEnat.coe_get)
             ","
             (Tactic.rwRule [] `add_comm)]
            "]")
           [])
          []
          (Tactic.exact
           "exact"
           (Term.proj
            (Term.app
             (Term.proj (Term.proj `hp "." (fieldIdx "1")) "." `multiplicity_choose_prime_pow)
             [`hj `j.succ_pos])
            "."
            `ge))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.proj
        (Term.app
         (Term.proj (Term.proj `hp "." (fieldIdx "1")) "." `multiplicity_choose_prime_pow)
         [`hj `j.succ_pos])
        "."
        `ge))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj
       (Term.app
        (Term.proj (Term.proj `hp "." (fieldIdx "1")) "." `multiplicity_choose_prime_pow)
        [`hj `j.succ_pos])
       "."
       `ge)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       (Term.proj (Term.proj `hp "." (fieldIdx "1")) "." `multiplicity_choose_prime_pow)
       [`hj `j.succ_pos])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `j.succ_pos
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hj
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.proj `hp "." (fieldIdx "1")) "." `multiplicity_choose_prime_pow)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj `hp "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hp
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      (Term.proj (Term.proj `hp "." (fieldIdx "1")) "." `multiplicity_choose_prime_pow)
      [`hj `j.succ_pos])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] (Term.app `PartEnat.coe_get [`aux]))
         ","
         (Tactic.rwRule [] `PartEnat.coe_le_coe)
         ","
         (Tactic.rwRule [] `tsub_le_iff_left)
         ","
         (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `PartEnat.coe_le_coe)
         ","
         (Tactic.rwRule [] `Nat.cast_add)
         ","
         (Tactic.rwRule [] `pnat_multiplicity)
         ","
         (Tactic.rwRule [] `PartEnat.coe_get)
         ","
         (Tactic.rwRule [] `PartEnat.coe_get)
         ","
         (Tactic.rwRule [] `add_comm)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `add_comm
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `PartEnat.coe_get
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `PartEnat.coe_get
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `pnat_multiplicity
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Nat.cast_add
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `PartEnat.coe_le_coe
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `tsub_le_iff_left
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `PartEnat.coe_le_coe
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `PartEnat.coe_get [`aux])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `aux
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `PartEnat.coe_get
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`aux []]
         [(Term.typeSpec
           ":"
           (Term.proj
            (Term.app
             `multiplicity
             [`p
              (Term.app
               (Term.proj («term_^_» `p "^" `n) "." `choose)
               [(«term_+_» `j "+" (num "1"))])])
            "."
            `Dom))]
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
               [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `multiplicity.finite_iff_dom)
                ","
                (Tactic.rwRule [] `multiplicity.finite_nat_iff)]
               "]")
              [])
             []
             (Tactic.exact
              "exact"
              (Term.anonymousCtor
               "⟨"
               [(Term.proj (Term.proj `hp "." (fieldIdx "1")) "." `ne_one)
                ","
                (Term.app `Nat.choose_pos [`hj])]
               "⟩"))]))))))
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
            [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `multiplicity.finite_iff_dom)
             ","
             (Tactic.rwRule [] `multiplicity.finite_nat_iff)]
            "]")
           [])
          []
          (Tactic.exact
           "exact"
           (Term.anonymousCtor
            "⟨"
            [(Term.proj (Term.proj `hp "." (fieldIdx "1")) "." `ne_one)
             ","
             (Term.app `Nat.choose_pos [`hj])]
            "⟩"))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.anonymousCtor
        "⟨"
        [(Term.proj (Term.proj `hp "." (fieldIdx "1")) "." `ne_one)
         ","
         (Term.app `Nat.choose_pos [`hj])]
        "⟩"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.proj (Term.proj `hp "." (fieldIdx "1")) "." `ne_one)
        ","
        (Term.app `Nat.choose_pos [`hj])]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Nat.choose_pos [`hj])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hj
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Nat.choose_pos
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.proj `hp "." (fieldIdx "1")) "." `ne_one)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj `hp "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hp
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `multiplicity.finite_iff_dom)
         ","
         (Tactic.rwRule [] `multiplicity.finite_nat_iff)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `multiplicity.finite_nat_iff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `multiplicity.finite_iff_dom
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj
       (Term.app
        `multiplicity
        [`p
         (Term.app (Term.proj («term_^_» `p "^" `n) "." `choose) [(«term_+_» `j "+" (num "1"))])])
       "."
       `Dom)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       `multiplicity
       [`p (Term.app (Term.proj («term_^_» `p "^" `n) "." `choose) [(«term_+_» `j "+" (num "1"))])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj («term_^_» `p "^" `n) "." `choose) [(«term_+_» `j "+" (num "1"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_+_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_+_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_» `j "+" (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `j
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_+_» `j "+" (num "1")) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj («term_^_» `p "^" `n) "." `choose)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      («term_^_» `p "^" `n)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 80, (some 80, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_^_» `p "^" `n) ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      (Term.proj (Term.paren "(" («term_^_» `p "^" `n) ")") "." `choose)
      [(Term.paren "(" («term_+_» `j "+" (num "1")) ")")])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `multiplicity
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `multiplicity
      [`p
       (Term.paren
        "("
        (Term.app
         (Term.proj (Term.paren "(" («term_^_» `p "^" `n) ")") "." `choose)
         [(Term.paren "(" («term_+_» `j "+" (num "1")) ")")])
        ")")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.apply "apply" `multiplicity.pow_dvd_of_le_multiplicity)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `multiplicity.pow_dvd_of_le_multiplicity
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_∣_»
       («term_^_»
        `p
        "^"
        («term_-_»
         `n
         "-"
         (Term.app
          (WittVector.RingTheory.WittVector.Frobenius.termv "v")
          [`p
           (Term.anonymousCtor
            "⟨"
            [(«term_+_» `j "+" (num "1")) "," (Term.proj `j "." `succ_pos)]
            "⟩")])))
       "∣"
       (Term.app (Term.proj («term_^_» `p "^" `n) "." `choose) [(«term_+_» `j "+" (num "1"))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj («term_^_» `p "^" `n) "." `choose) [(«term_+_» `j "+" (num "1"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_+_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_+_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_» `j "+" (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `j
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_+_» `j "+" (num "1")) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj («term_^_» `p "^" `n) "." `choose)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      («term_^_» `p "^" `n)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 80, (some 80, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_^_» `p "^" `n) ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      («term_^_»
       `p
       "^"
       («term_-_»
        `n
        "-"
        (Term.app
         (WittVector.RingTheory.WittVector.Frobenius.termv "v")
         [`p
          (Term.anonymousCtor
           "⟨"
           [(«term_+_» `j "+" (num "1")) "," (Term.proj `j "." `succ_pos)]
           "⟩")])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_-_»
       `n
       "-"
       (Term.app
        (WittVector.RingTheory.WittVector.Frobenius.termv "v")
        [`p
         (Term.anonymousCtor
          "⟨"
          [(«term_+_» `j "+" (num "1")) "," (Term.proj `j "." `succ_pos)]
          "⟩")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (WittVector.RingTheory.WittVector.Frobenius.termv "v")
       [`p
        (Term.anonymousCtor
         "⟨"
         [(«term_+_» `j "+" (num "1")) "," (Term.proj `j "." `succ_pos)]
         "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [(«term_+_» `j "+" (num "1")) "," (Term.proj `j "." `succ_pos)] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `j "." `succ_pos)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `j
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_» `j "+" (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `j
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (WittVector.RingTheory.WittVector.Frobenius.termv "v")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'WittVector.RingTheory.WittVector.Frobenius.termv', expected 'WittVector.RingTheory.WittVector.Frobenius.termv._@.RingTheory.WittVector.Frobenius._hyg.519'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/-- A key divisibility fact for the proof of `witt_vector.map_frobenius_poly`. -/
  theorem
    MapFrobeniusPoly.key₁
    ( n j : ℕ ) ( hj : j < p ^ n ) : p ^ n - v p ⟨ j + 1 , j . succ_pos ⟩ ∣ p ^ n . choose j + 1
    :=
      by
        apply multiplicity.pow_dvd_of_le_multiplicity
          have
            aux
              : multiplicity p p ^ n . choose j + 1 . Dom
              :=
              by
                rw [ ← multiplicity.finite_iff_dom , multiplicity.finite_nat_iff ]
                  exact ⟨ hp . 1 . ne_one , Nat.choose_pos hj ⟩
          rw
            [
              ← PartEnat.coe_get aux
                ,
                PartEnat.coe_le_coe
                ,
                tsub_le_iff_left
                ,
                ← PartEnat.coe_le_coe
                ,
                Nat.cast_add
                ,
                pnat_multiplicity
                ,
                PartEnat.coe_get
                ,
                PartEnat.coe_get
                ,
                add_comm
              ]
          exact hp . 1 . multiplicity_choose_prime_pow hj j.succ_pos . ge
#align witt_vector.map_frobenius_poly.key₁ WittVector.MapFrobeniusPoly.key₁

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "A key numerical identity needed for the proof of `witt_vector.map_frobenius_poly`. -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `MapFrobeniusPoly.key₂ [])
      (Command.declSig
       [(Term.implicitBinder "{" [`n `i `j] [":" (termℕ "ℕ")] "}")
        (Term.explicitBinder "(" [`hi] [":" («term_<_» `i "<" `n)] [] ")")
        (Term.explicitBinder
         "("
         [`hj]
         [":" («term_<_» `j "<" («term_^_» `p "^" («term_-_» `n "-" `i)))]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         («term_+_»
          («term_-_»
           `j
           "-"
           (Term.app
            (WittVector.RingTheory.WittVector.Frobenius.termv "v")
            [`p
             (Term.anonymousCtor
              "⟨"
              [(«term_+_» `j "+" (num "1")) "," (Term.proj `j "." `succ_pos)]
              "⟩")]))
          "+"
          `n)
         "="
         («term_+_»
          («term_+_» `i "+" `j)
          "+"
          («term_-_»
           («term_-_» `n "-" `i)
           "-"
           (Term.app
            (WittVector.RingTheory.WittVector.Frobenius.termv "v")
            [`p
             (Term.anonymousCtor
              "⟨"
              [(«term_+_» `j "+" (num "1")) "," (Term.proj `j "." `succ_pos)]
              "⟩")]))))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.generalize
            "generalize"
            [(Tactic.generalizeArg
              [`h ":"]
              (Term.app
               (WittVector.RingTheory.WittVector.Frobenius.termv "v")
               [`p (Term.anonymousCtor "⟨" [(«term_+_» `j "+" (num "1")) "," `j.succ_pos] "⟩")])
              "="
              `m)]
            [])
           []
           (Tactic.tacticSuffices_
            "suffices"
            (Term.sufficesDecl
             []
             («term_∧_» («term_≤_» `m "≤" («term_-_» `n "-" `i)) "∧" («term_≤_» `m "≤" `j))
             (Term.byTactic'
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule
                     []
                     (Term.app `tsub_add_eq_add_tsub [(Term.proj `this "." (fieldIdx "2"))]))
                    ","
                    (Tactic.rwRule [] (Term.app `add_comm [`i `j]))
                    ","
                    (Tactic.rwRule
                     []
                     (Term.app
                      `add_tsub_assoc_of_le
                      [(Term.app
                        (Term.proj (Term.proj `this "." (fieldIdx "1")) "." `trans)
                        [(Term.app `Nat.sub_le [`n `i])])]))
                    ","
                    (Tactic.rwRule [] `add_assoc)
                    ","
                    (Tactic.rwRule [] `tsub_right_comm)
                    ","
                    (Tactic.rwRule [] (Term.app `add_comm [`i]))
                    ","
                    (Tactic.rwRule
                     []
                     (Term.app
                      `tsub_add_cancel_of_le
                      [(Term.app
                        `le_tsub_of_add_le_right
                        [(Term.app
                          (Term.proj (Term.app `le_tsub_iff_left [`hi.le]) "." `mp)
                          [(Term.proj `this "." (fieldIdx "1"))])])]))]
                   "]")
                  [])])))))
           []
           (Tactic.constructor "constructor")
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `h)
                ","
                (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `PartEnat.coe_le_coe)
                ","
                (Tactic.rwRule [] `pnat_multiplicity)
                ","
                (Tactic.rwRule [] `PartEnat.coe_get)
                ","
                (Tactic.rwRule
                 [(patternIgnore (token.«← » "←"))]
                 (Term.app
                  (Term.proj (Term.proj `hp "." (fieldIdx "1")) "." `multiplicity_choose_prime_pow)
                  [`hj `j.succ_pos]))]
               "]")
              [])
             []
             (Tactic.apply "apply" `le_add_left)
             []
             (Tactic.tacticRfl "rfl")])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Std.Tactic.obtain
              "obtain"
              [(Std.Tactic.RCases.rcasesPatMed
                [(Std.Tactic.RCases.rcasesPat.tuple
                  "⟨"
                  [(Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `c)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hc)])
                    [])]
                  "⟩")])]
              [":" («term_∣_» («term_^_» `p "^" `m) "∣" («term_+_» `j "+" (num "1")))]
              [":="
               [(Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(Tactic.rwSeq
                     "rw"
                     []
                     (Tactic.rwRuleSeq
                      "["
                      [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `h)]
                      "]")
                     [])
                    []
                    (Tactic.exact
                     "exact"
                     (Term.app `multiplicity.pow_multiplicity_dvd [(Term.hole "_")]))])))]])
             []
             (Std.Tactic.obtain
              "obtain"
              [(Std.Tactic.RCases.rcasesPatMed
                [(Std.Tactic.RCases.rcasesPat.tuple
                  "⟨"
                  [(Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `c)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                    [])]
                  "⟩")])]
              [":"
               («term∃_,_»
                "∃"
                (Lean.explicitBinders
                 (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k)] [":" (termℕ "ℕ")]))
                ","
                («term_=_» `c "=" («term_+_» `k "+" (num "1"))))]
              [":="
               [(Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(Tactic.apply "apply" `Nat.exists_eq_succ_of_ne_zero)
                    []
                    (Std.Tactic.rintro
                     "rintro"
                     [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `rfl))]
                     [])
                    []
                    (Std.Tactic.Simpa.simpa
                     "simpa"
                     []
                     []
                     (Std.Tactic.Simpa.simpaArgsRest [] [] ["only"] [] ["using" `hc]))])))]])
             []
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [] `mul_add) "," (Tactic.rwRule [] `mul_one)]
               "]")
              [(Tactic.location "at" (Tactic.locationHyp [`hc] []))])
             []
             (Tactic.apply "apply" `Nat.le_of_lt_succ)
             []
             (calcTactic
              "calc"
              (calcStep
               («term_<_» `m "<" («term_^_» `p "^" `m))
               ":="
               (Term.app
                `Nat.lt_pow_self
                [(Term.proj (Term.proj `hp "." (fieldIdx "1")) "." `one_lt) `m]))
              [(calcStep
                («term_≤_» (Term.hole "_") "≤" («term_+_» `j "+" (num "1")))
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
                      [(Tactic.rwRule
                        [(patternIgnore (token.«← » "←"))]
                        (Term.app `tsub_eq_of_eq_add_rev [`hc]))]
                      "]")
                     [])
                    []
                    (Tactic.apply "apply" `Nat.sub_le)]))))])])])))
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
         [(Tactic.generalize
           "generalize"
           [(Tactic.generalizeArg
             [`h ":"]
             (Term.app
              (WittVector.RingTheory.WittVector.Frobenius.termv "v")
              [`p (Term.anonymousCtor "⟨" [(«term_+_» `j "+" (num "1")) "," `j.succ_pos] "⟩")])
             "="
             `m)]
           [])
          []
          (Tactic.tacticSuffices_
           "suffices"
           (Term.sufficesDecl
            []
            («term_∧_» («term_≤_» `m "≤" («term_-_» `n "-" `i)) "∧" («term_≤_» `m "≤" `j))
            (Term.byTactic'
             "by"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(Tactic.rwSeq
                 "rw"
                 []
                 (Tactic.rwRuleSeq
                  "["
                  [(Tactic.rwRule
                    []
                    (Term.app `tsub_add_eq_add_tsub [(Term.proj `this "." (fieldIdx "2"))]))
                   ","
                   (Tactic.rwRule [] (Term.app `add_comm [`i `j]))
                   ","
                   (Tactic.rwRule
                    []
                    (Term.app
                     `add_tsub_assoc_of_le
                     [(Term.app
                       (Term.proj (Term.proj `this "." (fieldIdx "1")) "." `trans)
                       [(Term.app `Nat.sub_le [`n `i])])]))
                   ","
                   (Tactic.rwRule [] `add_assoc)
                   ","
                   (Tactic.rwRule [] `tsub_right_comm)
                   ","
                   (Tactic.rwRule [] (Term.app `add_comm [`i]))
                   ","
                   (Tactic.rwRule
                    []
                    (Term.app
                     `tsub_add_cancel_of_le
                     [(Term.app
                       `le_tsub_of_add_le_right
                       [(Term.app
                         (Term.proj (Term.app `le_tsub_iff_left [`hi.le]) "." `mp)
                         [(Term.proj `this "." (fieldIdx "1"))])])]))]
                  "]")
                 [])])))))
          []
          (Tactic.constructor "constructor")
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `h)
               ","
               (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `PartEnat.coe_le_coe)
               ","
               (Tactic.rwRule [] `pnat_multiplicity)
               ","
               (Tactic.rwRule [] `PartEnat.coe_get)
               ","
               (Tactic.rwRule
                [(patternIgnore (token.«← » "←"))]
                (Term.app
                 (Term.proj (Term.proj `hp "." (fieldIdx "1")) "." `multiplicity_choose_prime_pow)
                 [`hj `j.succ_pos]))]
              "]")
             [])
            []
            (Tactic.apply "apply" `le_add_left)
            []
            (Tactic.tacticRfl "rfl")])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Std.Tactic.obtain
             "obtain"
             [(Std.Tactic.RCases.rcasesPatMed
               [(Std.Tactic.RCases.rcasesPat.tuple
                 "⟨"
                 [(Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `c)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hc)])
                   [])]
                 "⟩")])]
             [":" («term_∣_» («term_^_» `p "^" `m) "∣" («term_+_» `j "+" (num "1")))]
             [":="
              [(Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(Tactic.rwSeq
                    "rw"
                    []
                    (Tactic.rwRuleSeq
                     "["
                     [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `h)]
                     "]")
                    [])
                   []
                   (Tactic.exact
                    "exact"
                    (Term.app `multiplicity.pow_multiplicity_dvd [(Term.hole "_")]))])))]])
            []
            (Std.Tactic.obtain
             "obtain"
             [(Std.Tactic.RCases.rcasesPatMed
               [(Std.Tactic.RCases.rcasesPat.tuple
                 "⟨"
                 [(Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `c)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                   [])]
                 "⟩")])]
             [":"
              («term∃_,_»
               "∃"
               (Lean.explicitBinders
                (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k)] [":" (termℕ "ℕ")]))
               ","
               («term_=_» `c "=" («term_+_» `k "+" (num "1"))))]
             [":="
              [(Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(Tactic.apply "apply" `Nat.exists_eq_succ_of_ne_zero)
                   []
                   (Std.Tactic.rintro
                    "rintro"
                    [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `rfl))]
                    [])
                   []
                   (Std.Tactic.Simpa.simpa
                    "simpa"
                    []
                    []
                    (Std.Tactic.Simpa.simpaArgsRest [] [] ["only"] [] ["using" `hc]))])))]])
            []
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] `mul_add) "," (Tactic.rwRule [] `mul_one)]
              "]")
             [(Tactic.location "at" (Tactic.locationHyp [`hc] []))])
            []
            (Tactic.apply "apply" `Nat.le_of_lt_succ)
            []
            (calcTactic
             "calc"
             (calcStep
              («term_<_» `m "<" («term_^_» `p "^" `m))
              ":="
              (Term.app
               `Nat.lt_pow_self
               [(Term.proj (Term.proj `hp "." (fieldIdx "1")) "." `one_lt) `m]))
             [(calcStep
               («term_≤_» (Term.hole "_") "≤" («term_+_» `j "+" (num "1")))
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
                     [(Tactic.rwRule
                       [(patternIgnore (token.«← » "←"))]
                       (Term.app `tsub_eq_of_eq_add_rev [`hc]))]
                     "]")
                    [])
                   []
                   (Tactic.apply "apply" `Nat.sub_le)]))))])])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Std.Tactic.obtain
         "obtain"
         [(Std.Tactic.RCases.rcasesPatMed
           [(Std.Tactic.RCases.rcasesPat.tuple
             "⟨"
             [(Std.Tactic.RCases.rcasesPatLo
               (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `c)])
               [])
              ","
              (Std.Tactic.RCases.rcasesPatLo
               (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hc)])
               [])]
             "⟩")])]
         [":" («term_∣_» («term_^_» `p "^" `m) "∣" («term_+_» `j "+" (num "1")))]
         [":="
          [(Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq "[" [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `h)] "]")
                [])
               []
               (Tactic.exact
                "exact"
                (Term.app `multiplicity.pow_multiplicity_dvd [(Term.hole "_")]))])))]])
        []
        (Std.Tactic.obtain
         "obtain"
         [(Std.Tactic.RCases.rcasesPatMed
           [(Std.Tactic.RCases.rcasesPat.tuple
             "⟨"
             [(Std.Tactic.RCases.rcasesPatLo
               (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `c)])
               [])
              ","
              (Std.Tactic.RCases.rcasesPatLo
               (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
               [])]
             "⟩")])]
         [":"
          («term∃_,_»
           "∃"
           (Lean.explicitBinders
            (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k)] [":" (termℕ "ℕ")]))
           ","
           («term_=_» `c "=" («term_+_» `k "+" (num "1"))))]
         [":="
          [(Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.apply "apply" `Nat.exists_eq_succ_of_ne_zero)
               []
               (Std.Tactic.rintro
                "rintro"
                [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `rfl))]
                [])
               []
               (Std.Tactic.Simpa.simpa
                "simpa"
                []
                []
                (Std.Tactic.Simpa.simpaArgsRest [] [] ["only"] [] ["using" `hc]))])))]])
        []
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_add) "," (Tactic.rwRule [] `mul_one)] "]")
         [(Tactic.location "at" (Tactic.locationHyp [`hc] []))])
        []
        (Tactic.apply "apply" `Nat.le_of_lt_succ)
        []
        (calcTactic
         "calc"
         (calcStep
          («term_<_» `m "<" («term_^_» `p "^" `m))
          ":="
          (Term.app
           `Nat.lt_pow_self
           [(Term.proj (Term.proj `hp "." (fieldIdx "1")) "." `one_lt) `m]))
         [(calcStep
           («term_≤_» (Term.hole "_") "≤" («term_+_» `j "+" (num "1")))
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
                 [(Tactic.rwRule
                   [(patternIgnore (token.«← » "←"))]
                   (Term.app `tsub_eq_of_eq_add_rev [`hc]))]
                 "]")
                [])
               []
               (Tactic.apply "apply" `Nat.sub_le)]))))])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (calcTactic
       "calc"
       (calcStep
        («term_<_» `m "<" («term_^_» `p "^" `m))
        ":="
        (Term.app `Nat.lt_pow_self [(Term.proj (Term.proj `hp "." (fieldIdx "1")) "." `one_lt) `m]))
       [(calcStep
         («term_≤_» (Term.hole "_") "≤" («term_+_» `j "+" (num "1")))
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
               [(Tactic.rwRule
                 [(patternIgnore (token.«← » "←"))]
                 (Term.app `tsub_eq_of_eq_add_rev [`hc]))]
               "]")
              [])
             []
             (Tactic.apply "apply" `Nat.sub_le)]))))])
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
            [(Tactic.rwRule
              [(patternIgnore (token.«← » "←"))]
              (Term.app `tsub_eq_of_eq_add_rev [`hc]))]
            "]")
           [])
          []
          (Tactic.apply "apply" `Nat.sub_le)])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.apply "apply" `Nat.sub_le)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Nat.sub_le
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] (Term.app `tsub_eq_of_eq_add_rev [`hc]))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `tsub_eq_of_eq_add_rev [`hc])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hc
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `tsub_eq_of_eq_add_rev
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≤_» (Term.hole "_") "≤" («term_+_» `j "+" (num "1")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_» `j "+" (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `j
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
      (Term.app `Nat.lt_pow_self [(Term.proj (Term.proj `hp "." (fieldIdx "1")) "." `one_lt) `m])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `m
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj (Term.proj `hp "." (fieldIdx "1")) "." `one_lt)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj `hp "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hp
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Nat.lt_pow_self
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<_» `m "<" («term_^_» `p "^" `m))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_» `p "^" `m)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `m
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `m
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.apply "apply" `Nat.le_of_lt_succ)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Nat.le_of_lt_succ
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_add) "," (Tactic.rwRule [] `mul_one)] "]")
       [(Tactic.location "at" (Tactic.locationHyp [`hc] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hc
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_one
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_add
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.obtain
       "obtain"
       [(Std.Tactic.RCases.rcasesPatMed
         [(Std.Tactic.RCases.rcasesPat.tuple
           "⟨"
           [(Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `c)])
             [])
            ","
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
             [])]
           "⟩")])]
       [":"
        («term∃_,_»
         "∃"
         (Lean.explicitBinders
          (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k)] [":" (termℕ "ℕ")]))
         ","
         («term_=_» `c "=" («term_+_» `k "+" (num "1"))))]
       [":="
        [(Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.apply "apply" `Nat.exists_eq_succ_of_ne_zero)
             []
             (Std.Tactic.rintro
              "rintro"
              [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `rfl))]
              [])
             []
             (Std.Tactic.Simpa.simpa
              "simpa"
              []
              []
              (Std.Tactic.Simpa.simpaArgsRest [] [] ["only"] [] ["using" `hc]))])))]])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.apply "apply" `Nat.exists_eq_succ_of_ne_zero)
          []
          (Std.Tactic.rintro
           "rintro"
           [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `rfl))]
           [])
          []
          (Std.Tactic.Simpa.simpa
           "simpa"
           []
           []
           (Std.Tactic.Simpa.simpaArgsRest [] [] ["only"] [] ["using" `hc]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Simpa.simpa
       "simpa"
       []
       []
       (Std.Tactic.Simpa.simpaArgsRest [] [] ["only"] [] ["using" `hc]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hc
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.rintro
       "rintro"
       [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `rfl))]
       [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.apply "apply" `Nat.exists_eq_succ_of_ne_zero)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Nat.exists_eq_succ_of_ne_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term∃_,_»
       "∃"
       (Lean.explicitBinders
        (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k)] [":" (termℕ "ℕ")]))
       ","
       («term_=_» `c "=" («term_+_» `k "+" (num "1"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_» `c "=" («term_+_» `k "+" (num "1")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_» `k "+" (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `k
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `c
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'Lean.bracketedExplicitBinders'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (termℕ "ℕ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.obtain
       "obtain"
       [(Std.Tactic.RCases.rcasesPatMed
         [(Std.Tactic.RCases.rcasesPat.tuple
           "⟨"
           [(Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `c)])
             [])
            ","
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hc)])
             [])]
           "⟩")])]
       [":" («term_∣_» («term_^_» `p "^" `m) "∣" («term_+_» `j "+" (num "1")))]
       [":="
        [(Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq "[" [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `h)] "]")
              [])
             []
             (Tactic.exact
              "exact"
              (Term.app `multiplicity.pow_multiplicity_dvd [(Term.hole "_")]))])))]])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `h)] "]")
           [])
          []
          (Tactic.exact "exact" (Term.app `multiplicity.pow_multiplicity_dvd [(Term.hole "_")]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" (Term.app `multiplicity.pow_multiplicity_dvd [(Term.hole "_")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `multiplicity.pow_multiplicity_dvd [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `multiplicity.pow_multiplicity_dvd
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `h)] "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∣_» («term_^_» `p "^" `m) "∣" («term_+_» `j "+" (num "1")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_» `j "+" (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `j
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      («term_^_» `p "^" `m)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `m
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 80, (some 80, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
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
          [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `h)
           ","
           (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `PartEnat.coe_le_coe)
           ","
           (Tactic.rwRule [] `pnat_multiplicity)
           ","
           (Tactic.rwRule [] `PartEnat.coe_get)
           ","
           (Tactic.rwRule
            [(patternIgnore (token.«← » "←"))]
            (Term.app
             (Term.proj (Term.proj `hp "." (fieldIdx "1")) "." `multiplicity_choose_prime_pow)
             [`hj `j.succ_pos]))]
          "]")
         [])
        []
        (Tactic.apply "apply" `le_add_left)
        []
        (Tactic.tacticRfl "rfl")])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticRfl "rfl")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.apply "apply" `le_add_left)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `le_add_left
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `h)
         ","
         (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `PartEnat.coe_le_coe)
         ","
         (Tactic.rwRule [] `pnat_multiplicity)
         ","
         (Tactic.rwRule [] `PartEnat.coe_get)
         ","
         (Tactic.rwRule
          [(patternIgnore (token.«← » "←"))]
          (Term.app
           (Term.proj (Term.proj `hp "." (fieldIdx "1")) "." `multiplicity_choose_prime_pow)
           [`hj `j.succ_pos]))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj (Term.proj `hp "." (fieldIdx "1")) "." `multiplicity_choose_prime_pow)
       [`hj `j.succ_pos])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `j.succ_pos
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hj
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.proj `hp "." (fieldIdx "1")) "." `multiplicity_choose_prime_pow)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj `hp "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hp
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `PartEnat.coe_get
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `pnat_multiplicity
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `PartEnat.coe_le_coe
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.constructor "constructor")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticSuffices_
       "suffices"
       (Term.sufficesDecl
        []
        («term_∧_» («term_≤_» `m "≤" («term_-_» `n "-" `i)) "∧" («term_≤_» `m "≤" `j))
        (Term.byTactic'
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule
                []
                (Term.app `tsub_add_eq_add_tsub [(Term.proj `this "." (fieldIdx "2"))]))
               ","
               (Tactic.rwRule [] (Term.app `add_comm [`i `j]))
               ","
               (Tactic.rwRule
                []
                (Term.app
                 `add_tsub_assoc_of_le
                 [(Term.app
                   (Term.proj (Term.proj `this "." (fieldIdx "1")) "." `trans)
                   [(Term.app `Nat.sub_le [`n `i])])]))
               ","
               (Tactic.rwRule [] `add_assoc)
               ","
               (Tactic.rwRule [] `tsub_right_comm)
               ","
               (Tactic.rwRule [] (Term.app `add_comm [`i]))
               ","
               (Tactic.rwRule
                []
                (Term.app
                 `tsub_add_cancel_of_le
                 [(Term.app
                   `le_tsub_of_add_le_right
                   [(Term.app
                     (Term.proj (Term.app `le_tsub_iff_left [`hi.le]) "." `mp)
                     [(Term.proj `this "." (fieldIdx "1"))])])]))]
              "]")
             [])])))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic'', expected 'Lean.Parser.Term.fromTerm'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] (Term.app `tsub_add_eq_add_tsub [(Term.proj `this "." (fieldIdx "2"))]))
         ","
         (Tactic.rwRule [] (Term.app `add_comm [`i `j]))
         ","
         (Tactic.rwRule
          []
          (Term.app
           `add_tsub_assoc_of_le
           [(Term.app
             (Term.proj (Term.proj `this "." (fieldIdx "1")) "." `trans)
             [(Term.app `Nat.sub_le [`n `i])])]))
         ","
         (Tactic.rwRule [] `add_assoc)
         ","
         (Tactic.rwRule [] `tsub_right_comm)
         ","
         (Tactic.rwRule [] (Term.app `add_comm [`i]))
         ","
         (Tactic.rwRule
          []
          (Term.app
           `tsub_add_cancel_of_le
           [(Term.app
             `le_tsub_of_add_le_right
             [(Term.app
               (Term.proj (Term.app `le_tsub_iff_left [`hi.le]) "." `mp)
               [(Term.proj `this "." (fieldIdx "1"))])])]))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `tsub_add_cancel_of_le
       [(Term.app
         `le_tsub_of_add_le_right
         [(Term.app
           (Term.proj (Term.app `le_tsub_iff_left [`hi.le]) "." `mp)
           [(Term.proj `this "." (fieldIdx "1"))])])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `le_tsub_of_add_le_right
       [(Term.app
         (Term.proj (Term.app `le_tsub_iff_left [`hi.le]) "." `mp)
         [(Term.proj `this "." (fieldIdx "1"))])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj (Term.app `le_tsub_iff_left [`hi.le]) "." `mp)
       [(Term.proj `this "." (fieldIdx "1"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `this "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `this
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app `le_tsub_iff_left [`hi.le]) "." `mp)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `le_tsub_iff_left [`hi.le])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hi.le
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `le_tsub_iff_left
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `le_tsub_iff_left [`hi.le])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      (Term.proj (Term.paren "(" (Term.app `le_tsub_iff_left [`hi.le]) ")") "." `mp)
      [(Term.proj `this "." (fieldIdx "1"))])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `le_tsub_of_add_le_right
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `le_tsub_of_add_le_right
      [(Term.paren
        "("
        (Term.app
         (Term.proj (Term.paren "(" (Term.app `le_tsub_iff_left [`hi.le]) ")") "." `mp)
         [(Term.proj `this "." (fieldIdx "1"))])
        ")")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `tsub_add_cancel_of_le
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `add_comm [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `add_comm
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `tsub_right_comm
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `add_assoc
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `add_tsub_assoc_of_le
       [(Term.app
         (Term.proj (Term.proj `this "." (fieldIdx "1")) "." `trans)
         [(Term.app `Nat.sub_le [`n `i])])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj (Term.proj `this "." (fieldIdx "1")) "." `trans)
       [(Term.app `Nat.sub_le [`n `i])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Nat.sub_le [`n `i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Nat.sub_le
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `Nat.sub_le [`n `i]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.proj `this "." (fieldIdx "1")) "." `trans)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj `this "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `this
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      (Term.proj (Term.proj `this "." (fieldIdx "1")) "." `trans)
      [(Term.paren "(" (Term.app `Nat.sub_le [`n `i]) ")")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `add_tsub_assoc_of_le
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `add_comm [`i `j])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `j
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `add_comm
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `tsub_add_eq_add_tsub [(Term.proj `this "." (fieldIdx "2"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `this "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `this
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `tsub_add_eq_add_tsub
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_∧_» («term_≤_» `m "≤" («term_-_» `n "-" `i)) "∧" («term_≤_» `m "≤" `j))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≤_» `m "≤" `j)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `j
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `m
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 35 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 35, term))
      («term_≤_» `m "≤" («term_-_» `n "-" `i))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_-_» `n "-" `i)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `n
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `m
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 36 >? 50, (some 51, term) <=? (some 35, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 35, (some 35,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.generalize
       "generalize"
       [(Tactic.generalizeArg
         [`h ":"]
         (Term.app
          (WittVector.RingTheory.WittVector.Frobenius.termv "v")
          [`p (Term.anonymousCtor "⟨" [(«term_+_» `j "+" (num "1")) "," `j.succ_pos] "⟩")])
         "="
         `m)]
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (WittVector.RingTheory.WittVector.Frobenius.termv "v")
       [`p (Term.anonymousCtor "⟨" [(«term_+_» `j "+" (num "1")) "," `j.succ_pos] "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [(«term_+_» `j "+" (num "1")) "," `j.succ_pos] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `j.succ_pos
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_» `j "+" (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `j
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (WittVector.RingTheory.WittVector.Frobenius.termv "v")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'WittVector.RingTheory.WittVector.Frobenius.termv', expected 'WittVector.RingTheory.WittVector.Frobenius.termv._@.RingTheory.WittVector.Frobenius._hyg.519'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/-- A key numerical identity needed for the proof of `witt_vector.map_frobenius_poly`. -/
  theorem
    MapFrobeniusPoly.key₂
    { n i j : ℕ } ( hi : i < n ) ( hj : j < p ^ n - i )
      : j - v p ⟨ j + 1 , j . succ_pos ⟩ + n = i + j + n - i - v p ⟨ j + 1 , j . succ_pos ⟩
    :=
      by
        generalize h : v p ⟨ j + 1 , j.succ_pos ⟩ = m
          suffices
            m ≤ n - i ∧ m ≤ j
              by
                rw
                  [
                    tsub_add_eq_add_tsub this . 2
                      ,
                      add_comm i j
                      ,
                      add_tsub_assoc_of_le this . 1 . trans Nat.sub_le n i
                      ,
                      add_assoc
                      ,
                      tsub_right_comm
                      ,
                      add_comm i
                      ,
                      tsub_add_cancel_of_le
                        le_tsub_of_add_le_right le_tsub_iff_left hi.le . mp this . 1
                    ]
          constructor
          ·
            rw
                [
                  ← h
                    ,
                    ← PartEnat.coe_le_coe
                    ,
                    pnat_multiplicity
                    ,
                    PartEnat.coe_get
                    ,
                    ← hp . 1 . multiplicity_choose_prime_pow hj j.succ_pos
                  ]
              apply le_add_left
              rfl
          ·
            obtain
                ⟨ c , hc ⟩
                : p ^ m ∣ j + 1
                := by rw [ ← h ] exact multiplicity.pow_multiplicity_dvd _
              obtain
                ⟨ c , rfl ⟩
                : ∃ k : ℕ , c = k + 1
                := by apply Nat.exists_eq_succ_of_ne_zero rintro rfl simpa only using hc
              rw [ mul_add , mul_one ] at hc
              apply Nat.le_of_lt_succ
              calc
                m < p ^ m := Nat.lt_pow_self hp . 1 . one_lt m
                _ ≤ j + 1 := by rw [ ← tsub_eq_of_eq_add_rev hc ] apply Nat.sub_le
#align witt_vector.map_frobenius_poly.key₂ WittVector.MapFrobeniusPoly.key₂

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `map_frobenius_poly [])
      (Command.declSig
       [(Term.explicitBinder "(" [`n] [":" (termℕ "ℕ")] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app
          `MvPolynomial.map
          [(Term.app `Int.castRingHom [(Data.Rat.Init.termℚ "ℚ")])
           (Term.app `frobeniusPoly [`p `n])])
         "="
         (Term.app `frobeniusPolyRat [`p `n]))))
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
             [(Tactic.rwRule [] `frobenius_poly)
              ","
              (Tactic.rwRule [] `RingHom.map_add)
              ","
              (Tactic.rwRule [] `RingHom.map_mul)
              ","
              (Tactic.rwRule [] `RingHom.map_pow)
              ","
              (Tactic.rwRule [] `map_C)
              ","
              (Tactic.rwRule [] `map_X)
              ","
              (Tactic.rwRule [] `eq_intCast)
              ","
              (Tactic.rwRule [] `Int.cast_ofNat)
              ","
              (Tactic.rwRule [] `frobenius_poly_rat)]
             "]")
            [])
           []
           (Tactic.apply "apply" (Term.app `Nat.strong_induction_on [`n]))
           []
           (Tactic.clear "clear" [`n])
           []
           (Tactic.intro "intro" [`n `IH])
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `X_in_terms_of_W_eq)] "]")
            [])
           []
           (Tactic.simp
            "simp"
            []
            []
            ["only"]
            ["["
             [(Tactic.simpLemma [] [] `AlgHom.map_sum)
              ","
              (Tactic.simpLemma [] [] `AlgHom.map_sub)
              ","
              (Tactic.simpLemma [] [] `AlgHom.map_mul)
              ","
              (Tactic.simpLemma [] [] `AlgHom.map_pow)
              ","
              (Tactic.simpLemma [] [] `bind₁_C_right)]
             "]"]
            [])
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`h1 []]
              [(Term.typeSpec
                ":"
                («term_=_»
                 («term_*_»
                  («term_^_» (coeNotation "↑" `p) "^" `n)
                  "*"
                  («term_^_»
                   (Term.app
                    (Algebra.Invertible.«term⅟» "⅟")
                    [(Term.typeAscription
                      "("
                      (coeNotation "↑" `p)
                      ":"
                      [(Data.Rat.Init.termℚ "ℚ")]
                      ")")])
                   "^"
                   `n))
                 "="
                 (num "1")))]
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
                    [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `mul_pow)
                     ","
                     (Tactic.rwRule [] `mul_invOf_self)
                     ","
                     (Tactic.rwRule [] `one_pow)]
                    "]")
                   [])]))))))
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [] `bind₁_X_right)
              ","
              (Tactic.rwRule [] `Function.comp_apply)
              ","
              (Tactic.rwRule [] `witt_polynomial_eq_sum_C_mul_X_pow)
              ","
              (Tactic.rwRule [] `sum_range_succ)
              ","
              (Tactic.rwRule [] `sum_range_succ)
              ","
              (Tactic.rwRule [] `tsub_self)
              ","
              (Tactic.rwRule [] `add_tsub_cancel_left)
              ","
              (Tactic.rwRule [] `pow_zero)
              ","
              (Tactic.rwRule [] `pow_one)
              ","
              (Tactic.rwRule [] `pow_one)
              ","
              (Tactic.rwRule [] `sub_mul)
              ","
              (Tactic.rwRule [] `add_mul)
              ","
              (Tactic.rwRule [] `add_mul)
              ","
              (Tactic.rwRule [] `mul_right_comm)
              ","
              (Tactic.rwRule
               []
               (Term.app
                `mul_right_comm
                [(Term.app
                  `C
                  [(«term_^_» (coeNotation "↑" `p) "^" («term_+_» `n "+" (num "1")))])]))
              ","
              (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `C_mul)
              ","
              (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `C_mul)
              ","
              (Tactic.rwRule [] `pow_succ)
              ","
              (Tactic.rwRule
               []
               (Term.app `mul_assoc [(coeNotation "↑" `p) («term_^_» (coeNotation "↑" `p) "^" `n)]))
              ","
              (Tactic.rwRule [] `h1)
              ","
              (Tactic.rwRule [] `mul_one)
              ","
              (Tactic.rwRule [] `C_1)
              ","
              (Tactic.rwRule [] `one_mul)
              ","
              (Tactic.rwRule
               []
               (Term.app `add_comm [(Term.hole "_") («term_^_» (Term.app `X [`n]) "^" `p)]))
              ","
              (Tactic.rwRule [] `add_assoc)
              ","
              (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `add_sub)
              ","
              (Tactic.rwRule [] `add_right_inj)
              ","
              (Tactic.rwRule [] `frobenius_poly_aux_eq)
              ","
              (Tactic.rwRule [] `RingHom.map_sub)
              ","
              (Tactic.rwRule [] `map_X)
              ","
              (Tactic.rwRule [] `mul_sub)
              ","
              (Tactic.rwRule [] `sub_eq_add_neg)
              ","
              (Tactic.rwRule
               []
               (Term.app
                `add_comm
                [(Term.hole "_")
                 («term_*_»
                  (Term.app `C [(coeNotation "↑" `p)])
                  "*"
                  (Term.app `X [(«term_+_» `n "+" (num "1"))]))]))
              ","
              (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `add_sub)
              ","
              (Tactic.rwRule [] `add_right_inj)
              ","
              (Tactic.rwRule [] `neg_eq_iff_neg_eq)
              ","
              (Tactic.rwRule [] `neg_sub)]
             "]")
            [])
           []
           (Tactic.simp
            "simp"
            []
            []
            ["only"]
            ["["
             [(Tactic.simpLemma [] [] `RingHom.map_sum)
              ","
              (Tactic.simpLemma [] [] `mul_sum)
              ","
              (Tactic.simpLemma [] [] `sum_mul)
              ","
              (Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `sum_sub_distrib)]
             "]"]
            [])
           []
           (Tactic.apply "apply" (Term.app `sum_congr [`rfl]))
           []
           (Tactic.intro "intro" [`i `hi])
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mem_range)] "]")
            [(Tactic.location "at" (Tactic.locationHyp [`hi] []))])
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] (Term.app `IH [`i `hi]))]
             "]")
            [])
           []
           (Tactic.clear "clear" [`IH])
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [] (Term.app `add_comm [(«term_^_» (Term.app `X [`i]) "^" `p)]))
              ","
              (Tactic.rwRule [] `add_pow)
              ","
              (Tactic.rwRule [] `sum_range_succ')
              ","
              (Tactic.rwRule [] `pow_zero)
              ","
              (Tactic.rwRule [] `tsub_zero)
              ","
              (Tactic.rwRule [] `Nat.choose_zero_right)
              ","
              (Tactic.rwRule [] `one_mul)
              ","
              (Tactic.rwRule [] `Nat.cast_one)
              ","
              (Tactic.rwRule [] `mul_one)
              ","
              (Tactic.rwRule [] `mul_add)
              ","
              (Tactic.rwRule [] `add_mul)
              ","
              (Tactic.rwRule [] (Term.app `Nat.succ_sub [(Term.app `le_of_lt [`hi])]))
              ","
              (Tactic.rwRule [] (Term.app `Nat.succ_eq_add_one [(«term_-_» `n "-" `i)]))
              ","
              (Tactic.rwRule [] `pow_succ)
              ","
              (Tactic.rwRule [] `pow_mul)
              ","
              (Tactic.rwRule [] `add_sub_cancel)
              ","
              (Tactic.rwRule [] `mul_sum)
              ","
              (Tactic.rwRule [] `sum_mul)]
             "]")
            [])
           []
           (Tactic.apply "apply" (Term.app `sum_congr [`rfl]))
           []
           (Tactic.intro "intro" [`j `hj])
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mem_range)] "]")
            [(Tactic.location "at" (Tactic.locationHyp [`hj] []))])
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [] `RingHom.map_mul)
              ","
              (Tactic.rwRule [] `RingHom.map_mul)
              ","
              (Tactic.rwRule [] `RingHom.map_pow)
              ","
              (Tactic.rwRule [] `RingHom.map_pow)
              ","
              (Tactic.rwRule [] `RingHom.map_pow)
              ","
              (Tactic.rwRule [] `RingHom.map_pow)
              ","
              (Tactic.rwRule [] `RingHom.map_pow)
              ","
              (Tactic.rwRule [] `map_C)
              ","
              (Tactic.rwRule [] `map_X)
              ","
              (Tactic.rwRule [] `mul_pow)]
             "]")
            [])
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule
               []
               (Term.app `mul_comm [(«term_^_» (Term.app `C [(coeNotation "↑" `p)]) "^" `i)]))
              ","
              (Tactic.rwRule
               []
               (Term.app
                `mul_comm
                [(Term.hole "_")
                 («term_^_» («term_^_» (Term.app `X [`i]) "^" `p) "^" (Term.hole "_"))]))
              ","
              (Tactic.rwRule
               []
               (Term.app
                `mul_comm
                [(«term_^_»
                  (Term.app `C [(coeNotation "↑" `p)])
                  "^"
                  («term_+_» `j "+" (num "1")))]))
              ","
              (Tactic.rwRule [] (Term.app `mul_comm [(Term.app `C [(coeNotation "↑" `p)])]))]
             "]")
            [])
           []
           (Tactic.simp "simp" [] [] ["only"] ["[" [(Tactic.simpLemma [] [] `mul_assoc)] "]"] [])
           []
           (Tactic.apply "apply" `congr_arg)
           []
           (Tactic.apply "apply" `congr_arg)
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `C_eq_coe_nat)]
             "]")
            [])
           []
           (Tactic.simp
            "simp"
            []
            []
            ["only"]
            ["["
             [(Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `RingHom.map_pow)
              ","
              (Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `C_mul)]
             "]"]
            [])
           []
           (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `C_inj)] "]") [])
           []
           (Tactic.simp
            "simp"
            []
            []
            ["only"]
            ["["
             [(Tactic.simpLemma [] [] `invOf_eq_inv)
              ","
              (Tactic.simpLemma [] [] `eq_intCast)
              ","
              (Tactic.simpLemma [] [] `inv_pow)
              ","
              (Tactic.simpLemma [] [] `Int.cast_ofNat)
              ","
              (Tactic.simpLemma [] [] `Nat.cast_mul)
              ","
              (Tactic.simpLemma [] [] `Int.cast_mul)]
             "]"]
            [])
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule
               []
               (Term.app
                `Rat.coe_nat_div
                [(Term.hole "_")
                 (Term.hole "_")
                 (Term.app `map_frobenius_poly.key₁ [`p («term_-_» `n "-" `i) `j `hj])]))]
             "]")
            [])
           []
           (Tactic.simp
            "simp"
            []
            []
            ["only"]
            ["["
             [(Tactic.simpLemma [] [] `Nat.cast_pow)
              ","
              (Tactic.simpLemma [] [] `pow_add)
              ","
              (Tactic.simpLemma [] [] `pow_one)]
             "]"]
            [])
           []
           (Tactic.tacticSuffices_
            "suffices"
            (Term.sufficesDecl
             []
             («term_=_»
              (Term.typeAscription
               "("
               («term_*_»
                («term_*_»
                 («term_*_»
                  (Term.app
                   (Term.proj («term_^_» `p "^" («term_-_» `n "-" `i)) "." `choose)
                   [(«term_+_» `j "+" (num "1"))])
                  "*"
                  («term_^_»
                   `p
                   "^"
                   («term_-_»
                    `j
                    "-"
                    (Term.app
                     (WittVector.RingTheory.WittVector.Frobenius.termv "v")
                     [`p
                      (Term.anonymousCtor
                       "⟨"
                       [(«term_+_» `j "+" (num "1")) "," `j.succ_pos]
                       "⟩")]))))
                 "*"
                 `p)
                "*"
                («term_^_» `p "^" `n))
               ":"
               [(Data.Rat.Init.termℚ "ℚ")]
               ")")
              "="
              («term_*_»
               («term_*_»
                («term_*_» («term_^_» `p "^" `j) "*" `p)
                "*"
                («term_*_»
                 (Term.app
                  (Term.proj («term_^_» `p "^" («term_-_» `n "-" `i)) "." `choose)
                  [(«term_+_» `j "+" (num "1"))])
                 "*"
                 («term_^_» `p "^" `i)))
               "*"
               («term_^_»
                `p
                "^"
                («term_-_»
                 («term_-_» `n "-" `i)
                 "-"
                 (Term.app
                  (WittVector.RingTheory.WittVector.Frobenius.termv "v")
                  [`p
                   (Term.anonymousCtor "⟨" [(«term_+_» `j "+" (num "1")) "," `j.succ_pos] "⟩")])))))
             (Term.byTactic'
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.tacticHave_
                  "have"
                  (Term.haveDecl
                   (Term.haveIdDecl
                    [`aux []]
                    [(Term.typeSpec
                      ":"
                      (Term.forall
                       "∀"
                       [`k]
                       [(Term.typeSpec ":" (termℕ "ℕ"))]
                       ","
                       («term_≠_»
                        (Term.typeAscription
                         "("
                         («term_^_» `p "^" `k)
                         ":"
                         [(Data.Rat.Init.termℚ "ℚ")]
                         ")")
                        "≠"
                        (num "0"))))]
                    ":="
                    (Term.byTactic
                     "by"
                     (Tactic.tacticSeq
                      (Tactic.tacticSeq1Indented
                       [(Tactic.intro "intro" [])
                        []
                        (Tactic.apply "apply" `pow_ne_zero)
                        []
                        (Tactic.NormCast.tacticExact_mod_cast_
                         "exact_mod_cast"
                         (Term.proj (Term.proj `hp "." (fieldIdx "1")) "." `NeZero))]))))))
                 []
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
                     [(Tactic.simpLemma [] [] `aux)
                      ","
                      (Tactic.simpErase "-" `one_div)
                      ","
                      (Tactic.simpLemma [] [] `field_simps)]
                     "]")]
                   ["using" `this.symm]))])))))
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule
               []
               (Term.app
                `mul_comm
                [(Term.hole "_") (Term.typeAscription "(" `p ":" [(Data.Rat.Init.termℚ "ℚ")] ")")]))
              ","
              (Tactic.rwRule [] `mul_assoc)
              ","
              (Tactic.rwRule [] `mul_assoc)
              ","
              (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `pow_add)
              ","
              (Tactic.rwRule [] (Term.app `map_frobenius_poly.key₂ [`p `hi `hj]))]
             "]")
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
         [(Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `frobenius_poly)
             ","
             (Tactic.rwRule [] `RingHom.map_add)
             ","
             (Tactic.rwRule [] `RingHom.map_mul)
             ","
             (Tactic.rwRule [] `RingHom.map_pow)
             ","
             (Tactic.rwRule [] `map_C)
             ","
             (Tactic.rwRule [] `map_X)
             ","
             (Tactic.rwRule [] `eq_intCast)
             ","
             (Tactic.rwRule [] `Int.cast_ofNat)
             ","
             (Tactic.rwRule [] `frobenius_poly_rat)]
            "]")
           [])
          []
          (Tactic.apply "apply" (Term.app `Nat.strong_induction_on [`n]))
          []
          (Tactic.clear "clear" [`n])
          []
          (Tactic.intro "intro" [`n `IH])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `X_in_terms_of_W_eq)] "]")
           [])
          []
          (Tactic.simp
           "simp"
           []
           []
           ["only"]
           ["["
            [(Tactic.simpLemma [] [] `AlgHom.map_sum)
             ","
             (Tactic.simpLemma [] [] `AlgHom.map_sub)
             ","
             (Tactic.simpLemma [] [] `AlgHom.map_mul)
             ","
             (Tactic.simpLemma [] [] `AlgHom.map_pow)
             ","
             (Tactic.simpLemma [] [] `bind₁_C_right)]
            "]"]
           [])
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`h1 []]
             [(Term.typeSpec
               ":"
               («term_=_»
                («term_*_»
                 («term_^_» (coeNotation "↑" `p) "^" `n)
                 "*"
                 («term_^_»
                  (Term.app
                   (Algebra.Invertible.«term⅟» "⅟")
                   [(Term.typeAscription
                     "("
                     (coeNotation "↑" `p)
                     ":"
                     [(Data.Rat.Init.termℚ "ℚ")]
                     ")")])
                  "^"
                  `n))
                "="
                (num "1")))]
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
                   [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `mul_pow)
                    ","
                    (Tactic.rwRule [] `mul_invOf_self)
                    ","
                    (Tactic.rwRule [] `one_pow)]
                   "]")
                  [])]))))))
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `bind₁_X_right)
             ","
             (Tactic.rwRule [] `Function.comp_apply)
             ","
             (Tactic.rwRule [] `witt_polynomial_eq_sum_C_mul_X_pow)
             ","
             (Tactic.rwRule [] `sum_range_succ)
             ","
             (Tactic.rwRule [] `sum_range_succ)
             ","
             (Tactic.rwRule [] `tsub_self)
             ","
             (Tactic.rwRule [] `add_tsub_cancel_left)
             ","
             (Tactic.rwRule [] `pow_zero)
             ","
             (Tactic.rwRule [] `pow_one)
             ","
             (Tactic.rwRule [] `pow_one)
             ","
             (Tactic.rwRule [] `sub_mul)
             ","
             (Tactic.rwRule [] `add_mul)
             ","
             (Tactic.rwRule [] `add_mul)
             ","
             (Tactic.rwRule [] `mul_right_comm)
             ","
             (Tactic.rwRule
              []
              (Term.app
               `mul_right_comm
               [(Term.app `C [(«term_^_» (coeNotation "↑" `p) "^" («term_+_» `n "+" (num "1")))])]))
             ","
             (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `C_mul)
             ","
             (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `C_mul)
             ","
             (Tactic.rwRule [] `pow_succ)
             ","
             (Tactic.rwRule
              []
              (Term.app `mul_assoc [(coeNotation "↑" `p) («term_^_» (coeNotation "↑" `p) "^" `n)]))
             ","
             (Tactic.rwRule [] `h1)
             ","
             (Tactic.rwRule [] `mul_one)
             ","
             (Tactic.rwRule [] `C_1)
             ","
             (Tactic.rwRule [] `one_mul)
             ","
             (Tactic.rwRule
              []
              (Term.app `add_comm [(Term.hole "_") («term_^_» (Term.app `X [`n]) "^" `p)]))
             ","
             (Tactic.rwRule [] `add_assoc)
             ","
             (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `add_sub)
             ","
             (Tactic.rwRule [] `add_right_inj)
             ","
             (Tactic.rwRule [] `frobenius_poly_aux_eq)
             ","
             (Tactic.rwRule [] `RingHom.map_sub)
             ","
             (Tactic.rwRule [] `map_X)
             ","
             (Tactic.rwRule [] `mul_sub)
             ","
             (Tactic.rwRule [] `sub_eq_add_neg)
             ","
             (Tactic.rwRule
              []
              (Term.app
               `add_comm
               [(Term.hole "_")
                («term_*_»
                 (Term.app `C [(coeNotation "↑" `p)])
                 "*"
                 (Term.app `X [(«term_+_» `n "+" (num "1"))]))]))
             ","
             (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `add_sub)
             ","
             (Tactic.rwRule [] `add_right_inj)
             ","
             (Tactic.rwRule [] `neg_eq_iff_neg_eq)
             ","
             (Tactic.rwRule [] `neg_sub)]
            "]")
           [])
          []
          (Tactic.simp
           "simp"
           []
           []
           ["only"]
           ["["
            [(Tactic.simpLemma [] [] `RingHom.map_sum)
             ","
             (Tactic.simpLemma [] [] `mul_sum)
             ","
             (Tactic.simpLemma [] [] `sum_mul)
             ","
             (Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `sum_sub_distrib)]
            "]"]
           [])
          []
          (Tactic.apply "apply" (Term.app `sum_congr [`rfl]))
          []
          (Tactic.intro "intro" [`i `hi])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mem_range)] "]")
           [(Tactic.location "at" (Tactic.locationHyp [`hi] []))])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] (Term.app `IH [`i `hi]))]
            "]")
           [])
          []
          (Tactic.clear "clear" [`IH])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] (Term.app `add_comm [(«term_^_» (Term.app `X [`i]) "^" `p)]))
             ","
             (Tactic.rwRule [] `add_pow)
             ","
             (Tactic.rwRule [] `sum_range_succ')
             ","
             (Tactic.rwRule [] `pow_zero)
             ","
             (Tactic.rwRule [] `tsub_zero)
             ","
             (Tactic.rwRule [] `Nat.choose_zero_right)
             ","
             (Tactic.rwRule [] `one_mul)
             ","
             (Tactic.rwRule [] `Nat.cast_one)
             ","
             (Tactic.rwRule [] `mul_one)
             ","
             (Tactic.rwRule [] `mul_add)
             ","
             (Tactic.rwRule [] `add_mul)
             ","
             (Tactic.rwRule [] (Term.app `Nat.succ_sub [(Term.app `le_of_lt [`hi])]))
             ","
             (Tactic.rwRule [] (Term.app `Nat.succ_eq_add_one [(«term_-_» `n "-" `i)]))
             ","
             (Tactic.rwRule [] `pow_succ)
             ","
             (Tactic.rwRule [] `pow_mul)
             ","
             (Tactic.rwRule [] `add_sub_cancel)
             ","
             (Tactic.rwRule [] `mul_sum)
             ","
             (Tactic.rwRule [] `sum_mul)]
            "]")
           [])
          []
          (Tactic.apply "apply" (Term.app `sum_congr [`rfl]))
          []
          (Tactic.intro "intro" [`j `hj])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mem_range)] "]")
           [(Tactic.location "at" (Tactic.locationHyp [`hj] []))])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `RingHom.map_mul)
             ","
             (Tactic.rwRule [] `RingHom.map_mul)
             ","
             (Tactic.rwRule [] `RingHom.map_pow)
             ","
             (Tactic.rwRule [] `RingHom.map_pow)
             ","
             (Tactic.rwRule [] `RingHom.map_pow)
             ","
             (Tactic.rwRule [] `RingHom.map_pow)
             ","
             (Tactic.rwRule [] `RingHom.map_pow)
             ","
             (Tactic.rwRule [] `map_C)
             ","
             (Tactic.rwRule [] `map_X)
             ","
             (Tactic.rwRule [] `mul_pow)]
            "]")
           [])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule
              []
              (Term.app `mul_comm [(«term_^_» (Term.app `C [(coeNotation "↑" `p)]) "^" `i)]))
             ","
             (Tactic.rwRule
              []
              (Term.app
               `mul_comm
               [(Term.hole "_")
                («term_^_» («term_^_» (Term.app `X [`i]) "^" `p) "^" (Term.hole "_"))]))
             ","
             (Tactic.rwRule
              []
              (Term.app
               `mul_comm
               [(«term_^_» (Term.app `C [(coeNotation "↑" `p)]) "^" («term_+_» `j "+" (num "1")))]))
             ","
             (Tactic.rwRule [] (Term.app `mul_comm [(Term.app `C [(coeNotation "↑" `p)])]))]
            "]")
           [])
          []
          (Tactic.simp "simp" [] [] ["only"] ["[" [(Tactic.simpLemma [] [] `mul_assoc)] "]"] [])
          []
          (Tactic.apply "apply" `congr_arg)
          []
          (Tactic.apply "apply" `congr_arg)
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `C_eq_coe_nat)]
            "]")
           [])
          []
          (Tactic.simp
           "simp"
           []
           []
           ["only"]
           ["["
            [(Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `RingHom.map_pow)
             ","
             (Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `C_mul)]
            "]"]
           [])
          []
          (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `C_inj)] "]") [])
          []
          (Tactic.simp
           "simp"
           []
           []
           ["only"]
           ["["
            [(Tactic.simpLemma [] [] `invOf_eq_inv)
             ","
             (Tactic.simpLemma [] [] `eq_intCast)
             ","
             (Tactic.simpLemma [] [] `inv_pow)
             ","
             (Tactic.simpLemma [] [] `Int.cast_ofNat)
             ","
             (Tactic.simpLemma [] [] `Nat.cast_mul)
             ","
             (Tactic.simpLemma [] [] `Int.cast_mul)]
            "]"]
           [])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule
              []
              (Term.app
               `Rat.coe_nat_div
               [(Term.hole "_")
                (Term.hole "_")
                (Term.app `map_frobenius_poly.key₁ [`p («term_-_» `n "-" `i) `j `hj])]))]
            "]")
           [])
          []
          (Tactic.simp
           "simp"
           []
           []
           ["only"]
           ["["
            [(Tactic.simpLemma [] [] `Nat.cast_pow)
             ","
             (Tactic.simpLemma [] [] `pow_add)
             ","
             (Tactic.simpLemma [] [] `pow_one)]
            "]"]
           [])
          []
          (Tactic.tacticSuffices_
           "suffices"
           (Term.sufficesDecl
            []
            («term_=_»
             (Term.typeAscription
              "("
              («term_*_»
               («term_*_»
                («term_*_»
                 (Term.app
                  (Term.proj («term_^_» `p "^" («term_-_» `n "-" `i)) "." `choose)
                  [(«term_+_» `j "+" (num "1"))])
                 "*"
                 («term_^_»
                  `p
                  "^"
                  («term_-_»
                   `j
                   "-"
                   (Term.app
                    (WittVector.RingTheory.WittVector.Frobenius.termv "v")
                    [`p
                     (Term.anonymousCtor
                      "⟨"
                      [(«term_+_» `j "+" (num "1")) "," `j.succ_pos]
                      "⟩")]))))
                "*"
                `p)
               "*"
               («term_^_» `p "^" `n))
              ":"
              [(Data.Rat.Init.termℚ "ℚ")]
              ")")
             "="
             («term_*_»
              («term_*_»
               («term_*_» («term_^_» `p "^" `j) "*" `p)
               "*"
               («term_*_»
                (Term.app
                 (Term.proj («term_^_» `p "^" («term_-_» `n "-" `i)) "." `choose)
                 [(«term_+_» `j "+" (num "1"))])
                "*"
                («term_^_» `p "^" `i)))
              "*"
              («term_^_»
               `p
               "^"
               («term_-_»
                («term_-_» `n "-" `i)
                "-"
                (Term.app
                 (WittVector.RingTheory.WittVector.Frobenius.termv "v")
                 [`p
                  (Term.anonymousCtor "⟨" [(«term_+_» `j "+" (num "1")) "," `j.succ_pos] "⟩")])))))
            (Term.byTactic'
             "by"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(Tactic.tacticHave_
                 "have"
                 (Term.haveDecl
                  (Term.haveIdDecl
                   [`aux []]
                   [(Term.typeSpec
                     ":"
                     (Term.forall
                      "∀"
                      [`k]
                      [(Term.typeSpec ":" (termℕ "ℕ"))]
                      ","
                      («term_≠_»
                       (Term.typeAscription
                        "("
                        («term_^_» `p "^" `k)
                        ":"
                        [(Data.Rat.Init.termℚ "ℚ")]
                        ")")
                       "≠"
                       (num "0"))))]
                   ":="
                   (Term.byTactic
                    "by"
                    (Tactic.tacticSeq
                     (Tactic.tacticSeq1Indented
                      [(Tactic.intro "intro" [])
                       []
                       (Tactic.apply "apply" `pow_ne_zero)
                       []
                       (Tactic.NormCast.tacticExact_mod_cast_
                        "exact_mod_cast"
                        (Term.proj (Term.proj `hp "." (fieldIdx "1")) "." `NeZero))]))))))
                []
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
                    [(Tactic.simpLemma [] [] `aux)
                     ","
                     (Tactic.simpErase "-" `one_div)
                     ","
                     (Tactic.simpLemma [] [] `field_simps)]
                    "]")]
                  ["using" `this.symm]))])))))
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule
              []
              (Term.app
               `mul_comm
               [(Term.hole "_") (Term.typeAscription "(" `p ":" [(Data.Rat.Init.termℚ "ℚ")] ")")]))
             ","
             (Tactic.rwRule [] `mul_assoc)
             ","
             (Tactic.rwRule [] `mul_assoc)
             ","
             (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `pow_add)
             ","
             (Tactic.rwRule [] (Term.app `map_frobenius_poly.key₂ [`p `hi `hj]))]
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
        [(Tactic.rwRule
          []
          (Term.app
           `mul_comm
           [(Term.hole "_") (Term.typeAscription "(" `p ":" [(Data.Rat.Init.termℚ "ℚ")] ")")]))
         ","
         (Tactic.rwRule [] `mul_assoc)
         ","
         (Tactic.rwRule [] `mul_assoc)
         ","
         (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `pow_add)
         ","
         (Tactic.rwRule [] (Term.app `map_frobenius_poly.key₂ [`p `hi `hj]))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `map_frobenius_poly.key₂ [`p `hi `hj])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hj
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hi
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `map_frobenius_poly.key₂
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `pow_add
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_assoc
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_assoc
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `mul_comm
       [(Term.hole "_") (Term.typeAscription "(" `p ":" [(Data.Rat.Init.termℚ "ℚ")] ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription "(" `p ":" [(Data.Rat.Init.termℚ "ℚ")] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Rat.Init.termℚ "ℚ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p
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
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `mul_comm
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticSuffices_
       "suffices"
       (Term.sufficesDecl
        []
        («term_=_»
         (Term.typeAscription
          "("
          («term_*_»
           («term_*_»
            («term_*_»
             (Term.app
              (Term.proj («term_^_» `p "^" («term_-_» `n "-" `i)) "." `choose)
              [(«term_+_» `j "+" (num "1"))])
             "*"
             («term_^_»
              `p
              "^"
              («term_-_»
               `j
               "-"
               (Term.app
                (WittVector.RingTheory.WittVector.Frobenius.termv "v")
                [`p (Term.anonymousCtor "⟨" [(«term_+_» `j "+" (num "1")) "," `j.succ_pos] "⟩")]))))
            "*"
            `p)
           "*"
           («term_^_» `p "^" `n))
          ":"
          [(Data.Rat.Init.termℚ "ℚ")]
          ")")
         "="
         («term_*_»
          («term_*_»
           («term_*_» («term_^_» `p "^" `j) "*" `p)
           "*"
           («term_*_»
            (Term.app
             (Term.proj («term_^_» `p "^" («term_-_» `n "-" `i)) "." `choose)
             [(«term_+_» `j "+" (num "1"))])
            "*"
            («term_^_» `p "^" `i)))
          "*"
          («term_^_»
           `p
           "^"
           («term_-_»
            («term_-_» `n "-" `i)
            "-"
            (Term.app
             (WittVector.RingTheory.WittVector.Frobenius.termv "v")
             [`p (Term.anonymousCtor "⟨" [(«term_+_» `j "+" (num "1")) "," `j.succ_pos] "⟩")])))))
        (Term.byTactic'
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               [`aux []]
               [(Term.typeSpec
                 ":"
                 (Term.forall
                  "∀"
                  [`k]
                  [(Term.typeSpec ":" (termℕ "ℕ"))]
                  ","
                  («term_≠_»
                   (Term.typeAscription
                    "("
                    («term_^_» `p "^" `k)
                    ":"
                    [(Data.Rat.Init.termℚ "ℚ")]
                    ")")
                   "≠"
                   (num "0"))))]
               ":="
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(Tactic.intro "intro" [])
                   []
                   (Tactic.apply "apply" `pow_ne_zero)
                   []
                   (Tactic.NormCast.tacticExact_mod_cast_
                    "exact_mod_cast"
                    (Term.proj (Term.proj `hp "." (fieldIdx "1")) "." `NeZero))]))))))
            []
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
                [(Tactic.simpLemma [] [] `aux)
                 ","
                 (Tactic.simpErase "-" `one_div)
                 ","
                 (Tactic.simpLemma [] [] `field_simps)]
                "]")]
              ["using" `this.symm]))])))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic'', expected 'Lean.Parser.Term.fromTerm'
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
          [(Tactic.simpLemma [] [] `aux)
           ","
           (Tactic.simpErase "-" `one_div)
           ","
           (Tactic.simpLemma [] [] `field_simps)]
          "]")]
        ["using" `this.symm]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `this.symm
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `field_simps
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpErase', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `one_div
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `aux
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`aux []]
         [(Term.typeSpec
           ":"
           (Term.forall
            "∀"
            [`k]
            [(Term.typeSpec ":" (termℕ "ℕ"))]
            ","
            («term_≠_»
             (Term.typeAscription "(" («term_^_» `p "^" `k) ":" [(Data.Rat.Init.termℚ "ℚ")] ")")
             "≠"
             (num "0"))))]
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.intro "intro" [])
             []
             (Tactic.apply "apply" `pow_ne_zero)
             []
             (Tactic.NormCast.tacticExact_mod_cast_
              "exact_mod_cast"
              (Term.proj (Term.proj `hp "." (fieldIdx "1")) "." `NeZero))]))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.intro "intro" [])
          []
          (Tactic.apply "apply" `pow_ne_zero)
          []
          (Tactic.NormCast.tacticExact_mod_cast_
           "exact_mod_cast"
           (Term.proj (Term.proj `hp "." (fieldIdx "1")) "." `NeZero))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.NormCast.tacticExact_mod_cast_
       "exact_mod_cast"
       (Term.proj (Term.proj `hp "." (fieldIdx "1")) "." `NeZero))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.proj `hp "." (fieldIdx "1")) "." `NeZero)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj `hp "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hp
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.apply "apply" `pow_ne_zero)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `pow_ne_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.intro "intro" [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.forall
       "∀"
       [`k]
       [(Term.typeSpec ":" (termℕ "ℕ"))]
       ","
       («term_≠_»
        (Term.typeAscription "(" («term_^_» `p "^" `k) ":" [(Data.Rat.Init.termℚ "ℚ")] ")")
        "≠"
        (num "0")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≠_»
       (Term.typeAscription "(" («term_^_» `p "^" `k) ":" [(Data.Rat.Init.termℚ "ℚ")] ")")
       "≠"
       (num "0"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.typeAscription "(" («term_^_» `p "^" `k) ":" [(Data.Rat.Init.termℚ "ℚ")] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Rat.Init.termℚ "ℚ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_» `p "^" `k)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (termℕ "ℕ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.typeAscription
        "("
        («term_*_»
         («term_*_»
          («term_*_»
           (Term.app
            (Term.proj («term_^_» `p "^" («term_-_» `n "-" `i)) "." `choose)
            [(«term_+_» `j "+" (num "1"))])
           "*"
           («term_^_»
            `p
            "^"
            («term_-_»
             `j
             "-"
             (Term.app
              (WittVector.RingTheory.WittVector.Frobenius.termv "v")
              [`p (Term.anonymousCtor "⟨" [(«term_+_» `j "+" (num "1")) "," `j.succ_pos] "⟩")]))))
          "*"
          `p)
         "*"
         («term_^_» `p "^" `n))
        ":"
        [(Data.Rat.Init.termℚ "ℚ")]
        ")")
       "="
       («term_*_»
        («term_*_»
         («term_*_» («term_^_» `p "^" `j) "*" `p)
         "*"
         («term_*_»
          (Term.app
           (Term.proj («term_^_» `p "^" («term_-_» `n "-" `i)) "." `choose)
           [(«term_+_» `j "+" (num "1"))])
          "*"
          («term_^_» `p "^" `i)))
        "*"
        («term_^_»
         `p
         "^"
         («term_-_»
          («term_-_» `n "-" `i)
          "-"
          (Term.app
           (WittVector.RingTheory.WittVector.Frobenius.termv "v")
           [`p (Term.anonymousCtor "⟨" [(«term_+_» `j "+" (num "1")) "," `j.succ_pos] "⟩")])))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_»
       («term_*_»
        («term_*_» («term_^_» `p "^" `j) "*" `p)
        "*"
        («term_*_»
         (Term.app
          (Term.proj («term_^_» `p "^" («term_-_» `n "-" `i)) "." `choose)
          [(«term_+_» `j "+" (num "1"))])
         "*"
         («term_^_» `p "^" `i)))
       "*"
       («term_^_»
        `p
        "^"
        («term_-_»
         («term_-_» `n "-" `i)
         "-"
         (Term.app
          (WittVector.RingTheory.WittVector.Frobenius.termv "v")
          [`p (Term.anonymousCtor "⟨" [(«term_+_» `j "+" (num "1")) "," `j.succ_pos] "⟩")]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_»
       `p
       "^"
       («term_-_»
        («term_-_» `n "-" `i)
        "-"
        (Term.app
         (WittVector.RingTheory.WittVector.Frobenius.termv "v")
         [`p (Term.anonymousCtor "⟨" [(«term_+_» `j "+" (num "1")) "," `j.succ_pos] "⟩")])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_-_»
       («term_-_» `n "-" `i)
       "-"
       (Term.app
        (WittVector.RingTheory.WittVector.Frobenius.termv "v")
        [`p (Term.anonymousCtor "⟨" [(«term_+_» `j "+" (num "1")) "," `j.succ_pos] "⟩")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (WittVector.RingTheory.WittVector.Frobenius.termv "v")
       [`p (Term.anonymousCtor "⟨" [(«term_+_» `j "+" (num "1")) "," `j.succ_pos] "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [(«term_+_» `j "+" (num "1")) "," `j.succ_pos] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `j.succ_pos
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_» `j "+" (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `j
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (WittVector.RingTheory.WittVector.Frobenius.termv "v")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'WittVector.RingTheory.WittVector.Frobenius.termv', expected 'WittVector.RingTheory.WittVector.Frobenius.termv._@.RingTheory.WittVector.Frobenius._hyg.519'
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
  map_frobenius_poly
  ( n : ℕ ) : MvPolynomial.map Int.castRingHom ℚ frobeniusPoly p n = frobeniusPolyRat p n
  :=
    by
      rw
          [
            frobenius_poly
              ,
              RingHom.map_add
              ,
              RingHom.map_mul
              ,
              RingHom.map_pow
              ,
              map_C
              ,
              map_X
              ,
              eq_intCast
              ,
              Int.cast_ofNat
              ,
              frobenius_poly_rat
            ]
        apply Nat.strong_induction_on n
        clear n
        intro n IH
        rw [ X_in_terms_of_W_eq ]
        simp
          only
          [ AlgHom.map_sum , AlgHom.map_sub , AlgHom.map_mul , AlgHom.map_pow , bind₁_C_right ]
        have h1 : ↑ p ^ n * ⅟ ( ↑ p : ℚ ) ^ n = 1 := by rw [ ← mul_pow , mul_invOf_self , one_pow ]
        rw
          [
            bind₁_X_right
              ,
              Function.comp_apply
              ,
              witt_polynomial_eq_sum_C_mul_X_pow
              ,
              sum_range_succ
              ,
              sum_range_succ
              ,
              tsub_self
              ,
              add_tsub_cancel_left
              ,
              pow_zero
              ,
              pow_one
              ,
              pow_one
              ,
              sub_mul
              ,
              add_mul
              ,
              add_mul
              ,
              mul_right_comm
              ,
              mul_right_comm C ↑ p ^ n + 1
              ,
              ← C_mul
              ,
              ← C_mul
              ,
              pow_succ
              ,
              mul_assoc ↑ p ↑ p ^ n
              ,
              h1
              ,
              mul_one
              ,
              C_1
              ,
              one_mul
              ,
              add_comm _ X n ^ p
              ,
              add_assoc
              ,
              ← add_sub
              ,
              add_right_inj
              ,
              frobenius_poly_aux_eq
              ,
              RingHom.map_sub
              ,
              map_X
              ,
              mul_sub
              ,
              sub_eq_add_neg
              ,
              add_comm _ C ↑ p * X n + 1
              ,
              ← add_sub
              ,
              add_right_inj
              ,
              neg_eq_iff_neg_eq
              ,
              neg_sub
            ]
        simp only [ RingHom.map_sum , mul_sum , sum_mul , ← sum_sub_distrib ]
        apply sum_congr rfl
        intro i hi
        rw [ mem_range ] at hi
        rw [ ← IH i hi ]
        clear IH
        rw
          [
            add_comm X i ^ p
              ,
              add_pow
              ,
              sum_range_succ'
              ,
              pow_zero
              ,
              tsub_zero
              ,
              Nat.choose_zero_right
              ,
              one_mul
              ,
              Nat.cast_one
              ,
              mul_one
              ,
              mul_add
              ,
              add_mul
              ,
              Nat.succ_sub le_of_lt hi
              ,
              Nat.succ_eq_add_one n - i
              ,
              pow_succ
              ,
              pow_mul
              ,
              add_sub_cancel
              ,
              mul_sum
              ,
              sum_mul
            ]
        apply sum_congr rfl
        intro j hj
        rw [ mem_range ] at hj
        rw
          [
            RingHom.map_mul
              ,
              RingHom.map_mul
              ,
              RingHom.map_pow
              ,
              RingHom.map_pow
              ,
              RingHom.map_pow
              ,
              RingHom.map_pow
              ,
              RingHom.map_pow
              ,
              map_C
              ,
              map_X
              ,
              mul_pow
            ]
        rw [ mul_comm C ↑ p ^ i , mul_comm _ X i ^ p ^ _ , mul_comm C ↑ p ^ j + 1 , mul_comm C ↑ p ]
        simp only [ mul_assoc ]
        apply congr_arg
        apply congr_arg
        rw [ ← C_eq_coe_nat ]
        simp only [ ← RingHom.map_pow , ← C_mul ]
        rw [ C_inj ]
        simp
          only
          [ invOf_eq_inv , eq_intCast , inv_pow , Int.cast_ofNat , Nat.cast_mul , Int.cast_mul ]
        rw [ Rat.coe_nat_div _ _ map_frobenius_poly.key₁ p n - i j hj ]
        simp only [ Nat.cast_pow , pow_add , pow_one ]
        suffices
          ( p ^ n - i . choose j + 1 * p ^ j - v p ⟨ j + 1 , j.succ_pos ⟩ * p * p ^ n : ℚ )
              =
              p ^ j * p * p ^ n - i . choose j + 1 * p ^ i * p ^ n - i - v p ⟨ j + 1 , j.succ_pos ⟩
            by
              have
                  aux
                    : ∀ k : ℕ , ( p ^ k : ℚ ) ≠ 0
                    :=
                    by intro apply pow_ne_zero exact_mod_cast hp . 1 . NeZero
                simpa [ aux , - one_div , field_simps ] using this.symm
        rw
          [
            mul_comm _ ( p : ℚ )
              ,
              mul_assoc
              ,
              mul_assoc
              ,
              ← pow_add
              ,
              map_frobenius_poly.key₂ p hi hj
            ]
        ring
#align witt_vector.map_frobenius_poly WittVector.map_frobenius_poly

theorem frobenius_poly_zmod (n : ℕ) :
    MvPolynomial.map (Int.castRingHom (Zmod p)) (frobeniusPoly p n) = x n ^ p :=
  by
  rw [frobenius_poly, RingHom.map_add, RingHom.map_pow, RingHom.map_mul, map_X, map_C]
  simp only [Int.cast_ofNat, add_zero, eq_intCast, Zmod.nat_cast_self, zero_mul, C_0]
#align witt_vector.frobenius_poly_zmod WittVector.frobenius_poly_zmod

@[simp]
theorem bind₁_frobenius_poly_witt_polynomial (n : ℕ) :
    bind₁ (frobeniusPoly p) (wittPolynomial p ℤ n) = wittPolynomial p ℤ (n + 1) :=
  by
  apply MvPolynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
  simp only [map_bind₁, map_frobenius_poly, bind₁_frobenius_poly_rat_witt_polynomial,
    map_witt_polynomial]
#align
  witt_vector.bind₁_frobenius_poly_witt_polynomial WittVector.bind₁_frobenius_poly_witt_polynomial

variable {p}

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "`frobenius_fun` is the function underlying the ring endomorphism\n`frobenius : 𝕎 R →+* frobenius 𝕎 R`. -/")]
      []
      []
      []
      []
      [])
     (Command.def
      "def"
      (Command.declId `frobeniusFun [])
      (Command.optDeclSig
       [(Term.explicitBinder
         "("
         [`x]
         [":" (Term.app (WittVector.RingTheory.WittVector.Frobenius.term𝕎 "𝕎") [`R])]
         []
         ")")]
       [(Term.typeSpec ":" (Term.app (WittVector.RingTheory.WittVector.Frobenius.term𝕎 "𝕎") [`R]))])
      (Command.declValSimple
       ":="
       (Term.app
        (Term.app `mk [`p])
        [(Term.fun
          "fun"
          (Term.basicFun
           [`n]
           []
           "=>"
           (Term.app
            `MvPolynomial.aeval
            [(Term.proj `x "." `coeff) (Term.app `frobeniusPoly [`p `n])])))])
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.app `mk [`p])
       [(Term.fun
         "fun"
         (Term.basicFun
          [`n]
          []
          "=>"
          (Term.app
           `MvPolynomial.aeval
           [(Term.proj `x "." `coeff) (Term.app `frobeniusPoly [`p `n])])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`n]
        []
        "=>"
        (Term.app
         `MvPolynomial.aeval
         [(Term.proj `x "." `coeff) (Term.app `frobeniusPoly [`p `n])])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `MvPolynomial.aeval [(Term.proj `x "." `coeff) (Term.app `frobeniusPoly [`p `n])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `frobeniusPoly [`p `n])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `frobeniusPoly
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `frobeniusPoly [`p `n]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj `x "." `coeff)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `MvPolynomial.aeval
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.app `mk [`p])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `mk
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1022, (some 1023,
     term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `mk [`p]) ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app (WittVector.RingTheory.WittVector.Frobenius.term𝕎 "𝕎") [`R])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `R
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (WittVector.RingTheory.WittVector.Frobenius.term𝕎 "𝕎")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'WittVector.RingTheory.WittVector.Frobenius.term𝕎', expected 'WittVector.RingTheory.WittVector.Frobenius.term𝕎._@.RingTheory.WittVector.Frobenius._hyg.6'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    `frobenius_fun` is the function underlying the ring endomorphism
    `frobenius : 𝕎 R →+* frobenius 𝕎 R`. -/
  def frobeniusFun ( x : 𝕎 R ) : 𝕎 R := mk p fun n => MvPolynomial.aeval x . coeff frobeniusPoly p n
#align witt_vector.frobenius_fun WittVector.frobeniusFun

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `coeff_frobenius_fun [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`x]
         [":" (Term.app (WittVector.RingTheory.WittVector.Frobenius.term𝕎 "𝕎") [`R])]
         []
         ")")
        (Term.explicitBinder "(" [`n] [":" (termℕ "ℕ")] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app `coeff [(Term.app `frobeniusFun [`x]) `n])
         "="
         (Term.app
          `MvPolynomial.aeval
          [(Term.proj `x "." `coeff) (Term.app `frobeniusPoly [`p `n])]))))
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
             [(Tactic.rwRule [] `frobenius_fun) "," (Tactic.rwRule [] `coeff_mk)]
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
         [(Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `frobenius_fun) "," (Tactic.rwRule [] `coeff_mk)]
            "]")
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `frobenius_fun) "," (Tactic.rwRule [] `coeff_mk)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `coeff_mk
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `frobenius_fun
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app `coeff [(Term.app `frobeniusFun [`x]) `n])
       "="
       (Term.app `MvPolynomial.aeval [(Term.proj `x "." `coeff) (Term.app `frobeniusPoly [`p `n])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `MvPolynomial.aeval [(Term.proj `x "." `coeff) (Term.app `frobeniusPoly [`p `n])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `frobeniusPoly [`p `n])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `frobeniusPoly
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `frobeniusPoly [`p `n]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj `x "." `coeff)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `MvPolynomial.aeval
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app `coeff [(Term.app `frobeniusFun [`x]) `n])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `frobeniusFun [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `frobeniusFun
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `frobeniusFun [`x]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `coeff
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (termℕ "ℕ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (WittVector.RingTheory.WittVector.Frobenius.term𝕎 "𝕎") [`R])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `R
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (WittVector.RingTheory.WittVector.Frobenius.term𝕎 "𝕎")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'WittVector.RingTheory.WittVector.Frobenius.term𝕎', expected 'WittVector.RingTheory.WittVector.Frobenius.term𝕎._@.RingTheory.WittVector.Frobenius._hyg.6'
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
  coeff_frobenius_fun
  ( x : 𝕎 R ) ( n : ℕ ) : coeff frobeniusFun x n = MvPolynomial.aeval x . coeff frobeniusPoly p n
  := by rw [ frobenius_fun , coeff_mk ]
#align witt_vector.coeff_frobenius_fun WittVector.coeff_frobenius_fun

variable (p)

/-- `frobenius_fun` is tautologically a polynomial function.

See also `frobenius_is_poly`. -/
@[is_poly]
theorem frobenius_fun_is_poly : IsPoly p fun R _Rcr => @frobeniusFun p R _ _Rcr :=
  ⟨⟨frobeniusPoly p, by
      intros
      funext n
      apply coeff_frobenius_fun⟩⟩
#align witt_vector.frobenius_fun_is_poly WittVector.frobenius_fun_is_poly

variable {p}

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      []
      [(Term.attributes
        "@["
        [(Term.attrInstance (Term.attrKind []) (Attr.simple `ghost_simps []))]
        "]")]
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `ghost_component_frobenius_fun [])
      (Command.declSig
       [(Term.explicitBinder "(" [`n] [":" (termℕ "ℕ")] [] ")")
        (Term.explicitBinder
         "("
         [`x]
         [":" (Term.app (WittVector.RingTheory.WittVector.Frobenius.term𝕎 "𝕎") [`R])]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app `ghostComponent [`n (Term.app `frobeniusFun [`x])])
         "="
         (Term.app `ghostComponent [(«term_+_» `n "+" (num "1")) `x]))))
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
             [(Tactic.simpLemma [] [] `ghost_component_apply)
              ","
              (Tactic.simpLemma [] [] `frobenius_fun)
              ","
              (Tactic.simpLemma [] [] `coeff_mk)
              ","
              (Tactic.simpLemma
               []
               [(patternIgnore (token.«← » "←"))]
               `bind₁_frobenius_poly_witt_polynomial)
              ","
              (Tactic.simpLemma [] [] `aeval_bind₁)]
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
            [(Tactic.simpLemma [] [] `ghost_component_apply)
             ","
             (Tactic.simpLemma [] [] `frobenius_fun)
             ","
             (Tactic.simpLemma [] [] `coeff_mk)
             ","
             (Tactic.simpLemma
              []
              [(patternIgnore (token.«← » "←"))]
              `bind₁_frobenius_poly_witt_polynomial)
             ","
             (Tactic.simpLemma [] [] `aeval_bind₁)]
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
        [(Tactic.simpLemma [] [] `ghost_component_apply)
         ","
         (Tactic.simpLemma [] [] `frobenius_fun)
         ","
         (Tactic.simpLemma [] [] `coeff_mk)
         ","
         (Tactic.simpLemma
          []
          [(patternIgnore (token.«← » "←"))]
          `bind₁_frobenius_poly_witt_polynomial)
         ","
         (Tactic.simpLemma [] [] `aeval_bind₁)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `aeval_bind₁
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `bind₁_frobenius_poly_witt_polynomial
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `coeff_mk
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `frobenius_fun
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ghost_component_apply
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app `ghostComponent [`n (Term.app `frobeniusFun [`x])])
       "="
       (Term.app `ghostComponent [(«term_+_» `n "+" (num "1")) `x]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `ghostComponent [(«term_+_» `n "+" (num "1")) `x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_+_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_+_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      («term_+_» `n "+" (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `n
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 65, (some 66, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_+_» `n "+" (num "1")) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `ghostComponent
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app `ghostComponent [`n (Term.app `frobeniusFun [`x])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `frobeniusFun [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `frobeniusFun
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `frobeniusFun [`x]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `ghostComponent
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (WittVector.RingTheory.WittVector.Frobenius.term𝕎 "𝕎") [`R])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `R
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (WittVector.RingTheory.WittVector.Frobenius.term𝕎 "𝕎")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'WittVector.RingTheory.WittVector.Frobenius.term𝕎', expected 'WittVector.RingTheory.WittVector.Frobenius.term𝕎._@.RingTheory.WittVector.Frobenius._hyg.6'
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
@[ ghost_simps ]
  theorem
    ghost_component_frobenius_fun
    ( n : ℕ ) ( x : 𝕎 R ) : ghostComponent n frobeniusFun x = ghostComponent n + 1 x
    :=
      by
        simp
          only
          [
            ghost_component_apply
              ,
              frobenius_fun
              ,
              coeff_mk
              ,
              ← bind₁_frobenius_poly_witt_polynomial
              ,
              aeval_bind₁
            ]
#align witt_vector.ghost_component_frobenius_fun WittVector.ghost_component_frobenius_fun

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "If `R` has characteristic `p`, then there is a ring endomorphism\nthat raises `r : R` to the power `p`.\nBy applying `witt_vector.map` to this endomorphism,\nwe obtain a ring endomorphism `frobenius R p : 𝕎 R →+* 𝕎 R`.\n\nThe underlying function of this morphism is `witt_vector.frobenius_fun`.\n-/")]
      []
      []
      []
      []
      [])
     (Command.def
      "def"
      (Command.declId `frobenius [])
      (Command.optDeclSig
       []
       [(Term.typeSpec
         ":"
         (Algebra.Hom.Ring.«term_→+*_»
          (Term.app (WittVector.RingTheory.WittVector.Frobenius.term𝕎 "𝕎") [`R])
          " →+* "
          (Term.app (WittVector.RingTheory.WittVector.Frobenius.term𝕎 "𝕎") [`R])))])
      (Command.whereStructInst
       "where"
       [(Command.whereStructField (Term.letDecl (Term.letIdDecl `toFun [] [] ":=" `frobeniusFun)))
        []
        (Command.whereStructField
         (Term.letDecl
          (Term.letIdDecl
           `map_zero'
           []
           []
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.refine'
                "refine'"
                (Term.app
                 `is_poly.ext
                 [(Term.app
                   (Term.proj (Term.app `frobenius_fun_is_poly [`p]) "." `comp)
                   [`WittVector.zero_is_poly])
                  (Term.app
                   (Term.proj `WittVector.zero_is_poly "." `comp)
                   [(Term.app `frobenius_fun_is_poly [`p])])
                  (Term.hole "_")
                  (Term.hole "_")
                  (num "0")]))
               []
               (Tactic.ghostSimp "ghost_simp" [])]))))))
        []
        (Command.whereStructField
         (Term.letDecl
          (Term.letIdDecl
           `map_one'
           []
           []
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.refine'
                "refine'"
                (Term.app
                 `is_poly.ext
                 [(Term.app
                   (Term.proj (Term.app `frobenius_fun_is_poly [`p]) "." `comp)
                   [`WittVector.one_is_poly])
                  (Term.app
                   (Term.proj `WittVector.one_is_poly "." `comp)
                   [(Term.app `frobenius_fun_is_poly [`p])])
                  (Term.hole "_")
                  (Term.hole "_")
                  (num "0")]))
               []
               (Tactic.ghostSimp "ghost_simp" [])]))))))
        []
        (Command.whereStructField
         (Term.letDecl
          (Term.letIdDecl
           `map_add'
           []
           []
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.«tactic_<;>_»
                (Tactic.ghostCalc
                 "ghost_calc"
                 [(group (Lean.binderIdent (Term.hole "_")))
                  (group (Lean.binderIdent (Term.hole "_")))])
                "<;>"
                (Tactic.ghostSimp "ghost_simp" []))]))))))
        []
        (Command.whereStructField
         (Term.letDecl
          (Term.letIdDecl
           `map_mul'
           []
           []
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.«tactic_<;>_»
                (Tactic.ghostCalc
                 "ghost_calc"
                 [(group (Lean.binderIdent (Term.hole "_")))
                  (group (Lean.binderIdent (Term.hole "_")))])
                "<;>"
                (Tactic.ghostSimp "ghost_simp" []))]))))))]
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.whereStructInst', expected 'Lean.Parser.Command.declValSimple'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.whereStructInst', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.«tactic_<;>_»
           (Tactic.ghostCalc
            "ghost_calc"
            [(group (Lean.binderIdent (Term.hole "_"))) (group (Lean.binderIdent (Term.hole "_")))])
           "<;>"
           (Tactic.ghostSimp "ghost_simp" []))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.«tactic_<;>_»
       (Tactic.ghostCalc
        "ghost_calc"
        [(group (Lean.binderIdent (Term.hole "_"))) (group (Lean.binderIdent (Term.hole "_")))])
       "<;>"
       (Tactic.ghostSimp "ghost_simp" []))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.ghostSimp "ghost_simp" [])
[PrettyPrinter.parenthesize] ...precedences are 2 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
      (Tactic.ghostCalc
       "ghost_calc"
       [(group (Lean.binderIdent (Term.hole "_"))) (group (Lean.binderIdent (Term.hole "_")))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'ident'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.«tactic_<;>_»
           (Tactic.ghostCalc
            "ghost_calc"
            [(group (Lean.binderIdent (Term.hole "_"))) (group (Lean.binderIdent (Term.hole "_")))])
           "<;>"
           (Tactic.ghostSimp "ghost_simp" []))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.«tactic_<;>_»
       (Tactic.ghostCalc
        "ghost_calc"
        [(group (Lean.binderIdent (Term.hole "_"))) (group (Lean.binderIdent (Term.hole "_")))])
       "<;>"
       (Tactic.ghostSimp "ghost_simp" []))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.ghostSimp "ghost_simp" [])
[PrettyPrinter.parenthesize] ...precedences are 2 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
      (Tactic.ghostCalc
       "ghost_calc"
       [(group (Lean.binderIdent (Term.hole "_"))) (group (Lean.binderIdent (Term.hole "_")))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'ident'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.refine'
           "refine'"
           (Term.app
            `is_poly.ext
            [(Term.app
              (Term.proj (Term.app `frobenius_fun_is_poly [`p]) "." `comp)
              [`WittVector.one_is_poly])
             (Term.app
              (Term.proj `WittVector.one_is_poly "." `comp)
              [(Term.app `frobenius_fun_is_poly [`p])])
             (Term.hole "_")
             (Term.hole "_")
             (num "0")]))
          []
          (Tactic.ghostSimp "ghost_simp" [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.ghostSimp "ghost_simp" [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine'
       "refine'"
       (Term.app
        `is_poly.ext
        [(Term.app
          (Term.proj (Term.app `frobenius_fun_is_poly [`p]) "." `comp)
          [`WittVector.one_is_poly])
         (Term.app
          (Term.proj `WittVector.one_is_poly "." `comp)
          [(Term.app `frobenius_fun_is_poly [`p])])
         (Term.hole "_")
         (Term.hole "_")
         (num "0")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `is_poly.ext
       [(Term.app
         (Term.proj (Term.app `frobenius_fun_is_poly [`p]) "." `comp)
         [`WittVector.one_is_poly])
        (Term.app
         (Term.proj `WittVector.one_is_poly "." `comp)
         [(Term.app `frobenius_fun_is_poly [`p])])
        (Term.hole "_")
        (Term.hole "_")
        (num "0")])
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.app
       (Term.proj `WittVector.one_is_poly "." `comp)
       [(Term.app `frobenius_fun_is_poly [`p])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `frobenius_fun_is_poly [`p])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `frobenius_fun_is_poly
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `frobenius_fun_is_poly [`p])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `WittVector.one_is_poly "." `comp)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `WittVector.one_is_poly
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      (Term.proj `WittVector.one_is_poly "." `comp)
      [(Term.paren "(" (Term.app `frobenius_fun_is_poly [`p]) ")")])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       (Term.proj (Term.app `frobenius_fun_is_poly [`p]) "." `comp)
       [`WittVector.one_is_poly])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `WittVector.one_is_poly
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app `frobenius_fun_is_poly [`p]) "." `comp)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `frobenius_fun_is_poly [`p])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `frobenius_fun_is_poly
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `frobenius_fun_is_poly [`p])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      (Term.proj (Term.paren "(" (Term.app `frobenius_fun_is_poly [`p]) ")") "." `comp)
      [`WittVector.one_is_poly])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `is_poly.ext
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.refine'
           "refine'"
           (Term.app
            `is_poly.ext
            [(Term.app
              (Term.proj (Term.app `frobenius_fun_is_poly [`p]) "." `comp)
              [`WittVector.zero_is_poly])
             (Term.app
              (Term.proj `WittVector.zero_is_poly "." `comp)
              [(Term.app `frobenius_fun_is_poly [`p])])
             (Term.hole "_")
             (Term.hole "_")
             (num "0")]))
          []
          (Tactic.ghostSimp "ghost_simp" [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.ghostSimp "ghost_simp" [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine'
       "refine'"
       (Term.app
        `is_poly.ext
        [(Term.app
          (Term.proj (Term.app `frobenius_fun_is_poly [`p]) "." `comp)
          [`WittVector.zero_is_poly])
         (Term.app
          (Term.proj `WittVector.zero_is_poly "." `comp)
          [(Term.app `frobenius_fun_is_poly [`p])])
         (Term.hole "_")
         (Term.hole "_")
         (num "0")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `is_poly.ext
       [(Term.app
         (Term.proj (Term.app `frobenius_fun_is_poly [`p]) "." `comp)
         [`WittVector.zero_is_poly])
        (Term.app
         (Term.proj `WittVector.zero_is_poly "." `comp)
         [(Term.app `frobenius_fun_is_poly [`p])])
        (Term.hole "_")
        (Term.hole "_")
        (num "0")])
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.app
       (Term.proj `WittVector.zero_is_poly "." `comp)
       [(Term.app `frobenius_fun_is_poly [`p])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `frobenius_fun_is_poly [`p])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `frobenius_fun_is_poly
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `frobenius_fun_is_poly [`p])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `WittVector.zero_is_poly "." `comp)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `WittVector.zero_is_poly
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      (Term.proj `WittVector.zero_is_poly "." `comp)
      [(Term.paren "(" (Term.app `frobenius_fun_is_poly [`p]) ")")])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       (Term.proj (Term.app `frobenius_fun_is_poly [`p]) "." `comp)
       [`WittVector.zero_is_poly])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `WittVector.zero_is_poly
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app `frobenius_fun_is_poly [`p]) "." `comp)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `frobenius_fun_is_poly [`p])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `frobenius_fun_is_poly
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `frobenius_fun_is_poly [`p])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      (Term.proj (Term.paren "(" (Term.app `frobenius_fun_is_poly [`p]) ")") "." `comp)
      [`WittVector.zero_is_poly])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `is_poly.ext
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `frobeniusFun
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Algebra.Hom.Ring.«term_→+*_»
       (Term.app (WittVector.RingTheory.WittVector.Frobenius.term𝕎 "𝕎") [`R])
       " →+* "
       (Term.app (WittVector.RingTheory.WittVector.Frobenius.term𝕎 "𝕎") [`R]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (WittVector.RingTheory.WittVector.Frobenius.term𝕎 "𝕎") [`R])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `R
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (WittVector.RingTheory.WittVector.Frobenius.term𝕎 "𝕎")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'WittVector.RingTheory.WittVector.Frobenius.term𝕎', expected 'WittVector.RingTheory.WittVector.Frobenius.term𝕎._@.RingTheory.WittVector.Frobenius._hyg.6'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    If `R` has characteristic `p`, then there is a ring endomorphism
    that raises `r : R` to the power `p`.
    By applying `witt_vector.map` to this endomorphism,
    we obtain a ring endomorphism `frobenius R p : 𝕎 R →+* 𝕎 R`.
    
    The underlying function of this morphism is `witt_vector.frobenius_fun`.
    -/
  def
    frobenius
    : 𝕎 R →+* 𝕎 R
    where
      toFun := frobeniusFun
        map_zero'
          :=
          by
            refine'
                is_poly.ext
                  frobenius_fun_is_poly p . comp WittVector.zero_is_poly
                    WittVector.zero_is_poly . comp frobenius_fun_is_poly p
                    _
                    _
                    0
              ghost_simp
        map_one'
          :=
          by
            refine'
                is_poly.ext
                  frobenius_fun_is_poly p . comp WittVector.one_is_poly
                    WittVector.one_is_poly . comp frobenius_fun_is_poly p
                    _
                    _
                    0
              ghost_simp
        map_add' := by ghost_calc _ _ <;> ghost_simp
        map_mul' := by ghost_calc _ _ <;> ghost_simp
#align witt_vector.frobenius WittVector.frobenius

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `coeff_frobenius [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`x]
         [":" (Term.app (WittVector.RingTheory.WittVector.Frobenius.term𝕎 "𝕎") [`R])]
         []
         ")")
        (Term.explicitBinder "(" [`n] [":" (termℕ "ℕ")] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app `coeff [(Term.app `frobenius [`x]) `n])
         "="
         (Term.app
          `MvPolynomial.aeval
          [(Term.proj `x "." `coeff) (Term.app `frobeniusPoly [`p `n])]))))
      (Command.declValSimple
       ":="
       (Term.app `coeff_frobenius_fun [(Term.hole "_") (Term.hole "_")])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `coeff_frobenius_fun [(Term.hole "_") (Term.hole "_")])
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
      `coeff_frobenius_fun
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app `coeff [(Term.app `frobenius [`x]) `n])
       "="
       (Term.app `MvPolynomial.aeval [(Term.proj `x "." `coeff) (Term.app `frobeniusPoly [`p `n])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `MvPolynomial.aeval [(Term.proj `x "." `coeff) (Term.app `frobeniusPoly [`p `n])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `frobeniusPoly [`p `n])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `frobeniusPoly
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `frobeniusPoly [`p `n]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj `x "." `coeff)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `MvPolynomial.aeval
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app `coeff [(Term.app `frobenius [`x]) `n])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `frobenius [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `frobenius
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `frobenius [`x]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `coeff
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (termℕ "ℕ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (WittVector.RingTheory.WittVector.Frobenius.term𝕎 "𝕎") [`R])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `R
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (WittVector.RingTheory.WittVector.Frobenius.term𝕎 "𝕎")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'WittVector.RingTheory.WittVector.Frobenius.term𝕎', expected 'WittVector.RingTheory.WittVector.Frobenius.term𝕎._@.RingTheory.WittVector.Frobenius._hyg.6'
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
  coeff_frobenius
  ( x : 𝕎 R ) ( n : ℕ ) : coeff frobenius x n = MvPolynomial.aeval x . coeff frobeniusPoly p n
  := coeff_frobenius_fun _ _
#align witt_vector.coeff_frobenius WittVector.coeff_frobenius

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      []
      [(Term.attributes
        "@["
        [(Term.attrInstance (Term.attrKind []) (Attr.simple `ghost_simps []))]
        "]")]
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `ghost_component_frobenius [])
      (Command.declSig
       [(Term.explicitBinder "(" [`n] [":" (termℕ "ℕ")] [] ")")
        (Term.explicitBinder
         "("
         [`x]
         [":" (Term.app (WittVector.RingTheory.WittVector.Frobenius.term𝕎 "𝕎") [`R])]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app `ghostComponent [`n (Term.app `frobenius [`x])])
         "="
         (Term.app `ghostComponent [(«term_+_» `n "+" (num "1")) `x]))))
      (Command.declValSimple
       ":="
       (Term.app `ghost_component_frobenius_fun [(Term.hole "_") (Term.hole "_")])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `ghost_component_frobenius_fun [(Term.hole "_") (Term.hole "_")])
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
      `ghost_component_frobenius_fun
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app `ghostComponent [`n (Term.app `frobenius [`x])])
       "="
       (Term.app `ghostComponent [(«term_+_» `n "+" (num "1")) `x]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `ghostComponent [(«term_+_» `n "+" (num "1")) `x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_+_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_+_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      («term_+_» `n "+" (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `n
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 65, (some 66, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_+_» `n "+" (num "1")) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `ghostComponent
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app `ghostComponent [`n (Term.app `frobenius [`x])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `frobenius [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `frobenius
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `frobenius [`x]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `ghostComponent
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (WittVector.RingTheory.WittVector.Frobenius.term𝕎 "𝕎") [`R])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `R
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (WittVector.RingTheory.WittVector.Frobenius.term𝕎 "𝕎")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'WittVector.RingTheory.WittVector.Frobenius.term𝕎', expected 'WittVector.RingTheory.WittVector.Frobenius.term𝕎._@.RingTheory.WittVector.Frobenius._hyg.6'
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
@[ ghost_simps ]
  theorem
    ghost_component_frobenius
    ( n : ℕ ) ( x : 𝕎 R ) : ghostComponent n frobenius x = ghostComponent n + 1 x
    := ghost_component_frobenius_fun _ _
#align witt_vector.ghost_component_frobenius WittVector.ghost_component_frobenius

variable (p)

/-- `frobenius` is tautologically a polynomial function. -/
@[is_poly]
theorem frobenius_is_poly : IsPoly p fun R _Rcr => @frobenius p R _ _Rcr :=
  frobenius_fun_is_poly _
#align witt_vector.frobenius_is_poly WittVector.frobenius_is_poly

section CharP

variable [CharP R p]

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
      (Command.declId `coeff_frobenius_char_p [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`x]
         [":" (Term.app (WittVector.RingTheory.WittVector.Frobenius.term𝕎 "𝕎") [`R])]
         []
         ")")
        (Term.explicitBinder "(" [`n] [":" (termℕ "ℕ")] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app `coeff [(Term.app `frobenius [`x]) `n])
         "="
         («term_^_» (Term.app (Term.proj `x "." `coeff) [`n]) "^" `p))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `coeff_frobenius)] "]")
            [])
           []
           (calcTactic
            "calc"
            (calcStep
             («term_=_»
              (Term.app
               `aeval
               [(Term.fun "fun" (Term.basicFun [`k] [] "=>" (Term.app `x.coeff [`k])))
                (Term.app `frobenius_poly [`p `n])])
              "="
              (Term.app
               `aeval
               [(Term.fun "fun" (Term.basicFun [`k] [] "=>" (Term.app `x.coeff [`k])))
                (Term.app
                 `MvPolynomial.map
                 [(Term.app `Int.castRingHom [(Term.app `Zmod [`p])])
                  (Term.app `frobenius_poly [`p `n])])]))
             ":="
             (Term.hole "_"))
            [(calcStep
              («term_=_»
               (Term.hole "_")
               "="
               (Term.app
                `aeval
                [(Term.fun "fun" (Term.basicFun [`k] [] "=>" (Term.app `x.coeff [`k])))
                 (Term.typeAscription
                  "("
                  («term_^_» (Term.app `X [`n]) "^" `p)
                  ":"
                  [(Term.app `MvPolynomial [(termℕ "ℕ") (Term.app `Zmod [`p])])]
                  ")")]))
              ":="
              (Term.hole "_"))
             (calcStep
              («term_=_» (Term.hole "_") "=" («term_^_» (Term.app `x.coeff [`n]) "^" `p))
              ":="
              (Term.hole "_"))])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Mathlib.Tactic.Conv.convRHS
              "conv_rhs"
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
                   [(Tactic.rwRule [] `aeval_eq_eval₂_hom)
                    ","
                    (Tactic.rwRule [] `eval₂_hom_map_hom)]
                   "]"))])))
             []
             (Tactic.apply
              "apply"
              (Term.app
               `eval₂_hom_congr
               [(Term.app `RingHom.ext_int [(Term.hole "_") (Term.hole "_")]) `rfl `rfl]))])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `frobenius_poly_zmod)] "]")
              [])])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [] `AlgHom.map_pow) "," (Tactic.rwRule [] `aeval_X)]
               "]")
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
         [(Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `coeff_frobenius)] "]") [])
          []
          (calcTactic
           "calc"
           (calcStep
            («term_=_»
             (Term.app
              `aeval
              [(Term.fun "fun" (Term.basicFun [`k] [] "=>" (Term.app `x.coeff [`k])))
               (Term.app `frobenius_poly [`p `n])])
             "="
             (Term.app
              `aeval
              [(Term.fun "fun" (Term.basicFun [`k] [] "=>" (Term.app `x.coeff [`k])))
               (Term.app
                `MvPolynomial.map
                [(Term.app `Int.castRingHom [(Term.app `Zmod [`p])])
                 (Term.app `frobenius_poly [`p `n])])]))
            ":="
            (Term.hole "_"))
           [(calcStep
             («term_=_»
              (Term.hole "_")
              "="
              (Term.app
               `aeval
               [(Term.fun "fun" (Term.basicFun [`k] [] "=>" (Term.app `x.coeff [`k])))
                (Term.typeAscription
                 "("
                 («term_^_» (Term.app `X [`n]) "^" `p)
                 ":"
                 [(Term.app `MvPolynomial [(termℕ "ℕ") (Term.app `Zmod [`p])])]
                 ")")]))
             ":="
             (Term.hole "_"))
            (calcStep
             («term_=_» (Term.hole "_") "=" («term_^_» (Term.app `x.coeff [`n]) "^" `p))
             ":="
             (Term.hole "_"))])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Mathlib.Tactic.Conv.convRHS
             "conv_rhs"
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
                  [(Tactic.rwRule [] `aeval_eq_eval₂_hom) "," (Tactic.rwRule [] `eval₂_hom_map_hom)]
                  "]"))])))
            []
            (Tactic.apply
             "apply"
             (Term.app
              `eval₂_hom_congr
              [(Term.app `RingHom.ext_int [(Term.hole "_") (Term.hole "_")]) `rfl `rfl]))])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `frobenius_poly_zmod)] "]")
             [])])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] `AlgHom.map_pow) "," (Tactic.rwRule [] `aeval_X)]
              "]")
             [])])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule [] `AlgHom.map_pow) "," (Tactic.rwRule [] `aeval_X)]
          "]")
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `AlgHom.map_pow) "," (Tactic.rwRule [] `aeval_X)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `aeval_X
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `AlgHom.map_pow
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
         (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `frobenius_poly_zmod)] "]")
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `frobenius_poly_zmod)] "]") [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `frobenius_poly_zmod
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Mathlib.Tactic.Conv.convRHS
         "conv_rhs"
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
              [(Tactic.rwRule [] `aeval_eq_eval₂_hom) "," (Tactic.rwRule [] `eval₂_hom_map_hom)]
              "]"))])))
        []
        (Tactic.apply
         "apply"
         (Term.app
          `eval₂_hom_congr
          [(Term.app `RingHom.ext_int [(Term.hole "_") (Term.hole "_")]) `rfl `rfl]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.apply
       "apply"
       (Term.app
        `eval₂_hom_congr
        [(Term.app `RingHom.ext_int [(Term.hole "_") (Term.hole "_")]) `rfl `rfl]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `eval₂_hom_congr
       [(Term.app `RingHom.ext_int [(Term.hole "_") (Term.hole "_")]) `rfl `rfl])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rfl
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `rfl
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `RingHom.ext_int [(Term.hole "_") (Term.hole "_")])
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
      `RingHom.ext_int
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `RingHom.ext_int [(Term.hole "_") (Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `eval₂_hom_congr
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.Conv.convRHS
       "conv_rhs"
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
            [(Tactic.rwRule [] `aeval_eq_eval₂_hom) "," (Tactic.rwRule [] `eval₂_hom_map_hom)]
            "]"))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.Conv.convSeq1Indented', expected 'Lean.Parser.Tactic.Conv.convSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `eval₂_hom_map_hom
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `aeval_eq_eval₂_hom
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (calcTactic
       "calc"
       (calcStep
        («term_=_»
         (Term.app
          `aeval
          [(Term.fun "fun" (Term.basicFun [`k] [] "=>" (Term.app `x.coeff [`k])))
           (Term.app `frobenius_poly [`p `n])])
         "="
         (Term.app
          `aeval
          [(Term.fun "fun" (Term.basicFun [`k] [] "=>" (Term.app `x.coeff [`k])))
           (Term.app
            `MvPolynomial.map
            [(Term.app `Int.castRingHom [(Term.app `Zmod [`p])])
             (Term.app `frobenius_poly [`p `n])])]))
        ":="
        (Term.hole "_"))
       [(calcStep
         («term_=_»
          (Term.hole "_")
          "="
          (Term.app
           `aeval
           [(Term.fun "fun" (Term.basicFun [`k] [] "=>" (Term.app `x.coeff [`k])))
            (Term.typeAscription
             "("
             («term_^_» (Term.app `X [`n]) "^" `p)
             ":"
             [(Term.app `MvPolynomial [(termℕ "ℕ") (Term.app `Zmod [`p])])]
             ")")]))
         ":="
         (Term.hole "_"))
        (calcStep
         («term_=_» (Term.hole "_") "=" («term_^_» (Term.app `x.coeff [`n]) "^" `p))
         ":="
         (Term.hole "_"))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_» (Term.hole "_") "=" («term_^_» (Term.app `x.coeff [`n]) "^" `p))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_» (Term.app `x.coeff [`n]) "^" `p)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Term.app `x.coeff [`n])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `x.coeff
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1022, (some 1023, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Term.hole "_")
       "="
       (Term.app
        `aeval
        [(Term.fun "fun" (Term.basicFun [`k] [] "=>" (Term.app `x.coeff [`k])))
         (Term.typeAscription
          "("
          («term_^_» (Term.app `X [`n]) "^" `p)
          ":"
          [(Term.app `MvPolynomial [(termℕ "ℕ") (Term.app `Zmod [`p])])]
          ")")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `aeval
       [(Term.fun "fun" (Term.basicFun [`k] [] "=>" (Term.app `x.coeff [`k])))
        (Term.typeAscription
         "("
         («term_^_» (Term.app `X [`n]) "^" `p)
         ":"
         [(Term.app `MvPolynomial [(termℕ "ℕ") (Term.app `Zmod [`p])])]
         ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription
       "("
       («term_^_» (Term.app `X [`n]) "^" `p)
       ":"
       [(Term.app `MvPolynomial [(termℕ "ℕ") (Term.app `Zmod [`p])])]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `MvPolynomial [(termℕ "ℕ") (Term.app `Zmod [`p])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Zmod [`p])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Zmod
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `Zmod [`p]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'termℕ', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'termℕ', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (termℕ "ℕ")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `MvPolynomial
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_» (Term.app `X [`n]) "^" `p)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Term.app `X [`n])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `X
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1022, (some 1023, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.fun "fun" (Term.basicFun [`k] [] "=>" (Term.app `x.coeff [`k])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `x.coeff [`k])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `x.coeff
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
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.fun "fun" (Term.basicFun [`k] [] "=>" (Term.app `x.coeff [`k])))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `aeval
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Term.app
        `aeval
        [(Term.fun "fun" (Term.basicFun [`k] [] "=>" (Term.app `x.coeff [`k])))
         (Term.app `frobenius_poly [`p `n])])
       "="
       (Term.app
        `aeval
        [(Term.fun "fun" (Term.basicFun [`k] [] "=>" (Term.app `x.coeff [`k])))
         (Term.app
          `MvPolynomial.map
          [(Term.app `Int.castRingHom [(Term.app `Zmod [`p])])
           (Term.app `frobenius_poly [`p `n])])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `aeval
       [(Term.fun "fun" (Term.basicFun [`k] [] "=>" (Term.app `x.coeff [`k])))
        (Term.app
         `MvPolynomial.map
         [(Term.app `Int.castRingHom [(Term.app `Zmod [`p])]) (Term.app `frobenius_poly [`p `n])])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `MvPolynomial.map
       [(Term.app `Int.castRingHom [(Term.app `Zmod [`p])]) (Term.app `frobenius_poly [`p `n])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `frobenius_poly [`p `n])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `frobenius_poly
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `frobenius_poly [`p `n]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `Int.castRingHom [(Term.app `Zmod [`p])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Zmod [`p])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Zmod
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `Zmod [`p]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Int.castRingHom
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `Int.castRingHom [(Term.paren "(" (Term.app `Zmod [`p]) ")")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `MvPolynomial.map
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `MvPolynomial.map
      [(Term.paren "(" (Term.app `Int.castRingHom [(Term.paren "(" (Term.app `Zmod [`p]) ")")]) ")")
       (Term.paren "(" (Term.app `frobenius_poly [`p `n]) ")")])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.fun "fun" (Term.basicFun [`k] [] "=>" (Term.app `x.coeff [`k])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `x.coeff [`k])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `x.coeff
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
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.fun "fun" (Term.basicFun [`k] [] "=>" (Term.app `x.coeff [`k])))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `aeval
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app
       `aeval
       [(Term.fun "fun" (Term.basicFun [`k] [] "=>" (Term.app `x.coeff [`k])))
        (Term.app `frobenius_poly [`p `n])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `frobenius_poly [`p `n])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `frobenius_poly
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `frobenius_poly [`p `n]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.fun "fun" (Term.basicFun [`k] [] "=>" (Term.app `x.coeff [`k])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `x.coeff [`k])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `x.coeff
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
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.fun "fun" (Term.basicFun [`k] [] "=>" (Term.app `x.coeff [`k])))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `aeval
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `coeff_frobenius)] "]") [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `coeff_frobenius
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app `coeff [(Term.app `frobenius [`x]) `n])
       "="
       («term_^_» (Term.app (Term.proj `x "." `coeff) [`n]) "^" `p))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_» (Term.app (Term.proj `x "." `coeff) [`n]) "^" `p)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Term.app (Term.proj `x "." `coeff) [`n])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `x "." `coeff)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1022, (some 1023, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app `coeff [(Term.app `frobenius [`x]) `n])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `frobenius [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `frobenius
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `frobenius [`x]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `coeff
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (termℕ "ℕ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (WittVector.RingTheory.WittVector.Frobenius.term𝕎 "𝕎") [`R])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `R
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (WittVector.RingTheory.WittVector.Frobenius.term𝕎 "𝕎")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'WittVector.RingTheory.WittVector.Frobenius.term𝕎', expected 'WittVector.RingTheory.WittVector.Frobenius.term𝕎._@.RingTheory.WittVector.Frobenius._hyg.6'
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
    coeff_frobenius_char_p
    ( x : 𝕎 R ) ( n : ℕ ) : coeff frobenius x n = x . coeff n ^ p
    :=
      by
        rw [ coeff_frobenius ]
          calc
            aeval fun k => x.coeff k frobenius_poly p n
                =
                aeval fun k => x.coeff k MvPolynomial.map Int.castRingHom Zmod p frobenius_poly p n
              :=
              _
            _ = aeval fun k => x.coeff k ( X n ^ p : MvPolynomial ℕ Zmod p ) := _
              _ = x.coeff n ^ p := _
          ·
            conv_rhs => rw [ aeval_eq_eval₂_hom , eval₂_hom_map_hom ]
              apply eval₂_hom_congr RingHom.ext_int _ _ rfl rfl
          · rw [ frobenius_poly_zmod ]
          · rw [ AlgHom.map_pow , aeval_X ]
#align witt_vector.coeff_frobenius_char_p WittVector.coeff_frobenius_char_p

theorem frobenius_eq_map_frobenius : @frobenius p R _ _ = map (frobenius R p) :=
  by
  ext (x n)
  simp only [coeff_frobenius_char_p, map_coeff, frobenius_def]
#align witt_vector.frobenius_eq_map_frobenius WittVector.frobenius_eq_map_frobenius

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
      (Command.declId `frobenius_zmodp [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`x]
         [":"
          (Term.app (WittVector.RingTheory.WittVector.Frobenius.term𝕎 "𝕎") [(Term.app `Zmod [`p])])]
         []
         ")")]
       (Term.typeSpec ":" («term_=_» (Term.app `frobenius [`x]) "=" `x)))
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
             [(Tactic.simpLemma [] [] `ext_iff)
              ","
              (Tactic.simpLemma [] [] `coeff_frobenius_char_p)
              ","
              (Tactic.simpLemma [] [] `Zmod.pow_card)
              ","
              (Tactic.simpLemma [] [] `eq_self_iff_true)
              ","
              (Tactic.simpLemma [] [] `forall_const)]
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
            [(Tactic.simpLemma [] [] `ext_iff)
             ","
             (Tactic.simpLemma [] [] `coeff_frobenius_char_p)
             ","
             (Tactic.simpLemma [] [] `Zmod.pow_card)
             ","
             (Tactic.simpLemma [] [] `eq_self_iff_true)
             ","
             (Tactic.simpLemma [] [] `forall_const)]
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
        [(Tactic.simpLemma [] [] `ext_iff)
         ","
         (Tactic.simpLemma [] [] `coeff_frobenius_char_p)
         ","
         (Tactic.simpLemma [] [] `Zmod.pow_card)
         ","
         (Tactic.simpLemma [] [] `eq_self_iff_true)
         ","
         (Tactic.simpLemma [] [] `forall_const)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `forall_const
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
      `Zmod.pow_card
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `coeff_frobenius_char_p
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ext_iff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_» (Term.app `frobenius [`x]) "=" `x)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app `frobenius [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `frobenius
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (WittVector.RingTheory.WittVector.Frobenius.term𝕎 "𝕎") [(Term.app `Zmod [`p])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Zmod [`p])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Zmod
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `Zmod [`p]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (WittVector.RingTheory.WittVector.Frobenius.term𝕎 "𝕎")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'WittVector.RingTheory.WittVector.Frobenius.term𝕎', expected 'WittVector.RingTheory.WittVector.Frobenius.term𝕎._@.RingTheory.WittVector.Frobenius._hyg.6'
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
    frobenius_zmodp
    ( x : 𝕎 Zmod p ) : frobenius x = x
    :=
      by
        simp
          only
          [ ext_iff , coeff_frobenius_char_p , Zmod.pow_card , eq_self_iff_true , forall_const ]
#align witt_vector.frobenius_zmodp WittVector.frobenius_zmodp

variable (p R)

/-- `witt_vector.frobenius` as an equiv. -/
@[simps (config := { fullyApplied := false })]
def frobeniusEquiv [PerfectRing R p] : WittVector p R ≃+* WittVector p R :=
  {
    (WittVector.frobenius :
      WittVector p R →+* WittVector p
          R) with
    toFun := WittVector.frobenius
    invFun := map (pthRoot R p)
    left_inv := fun f =>
      ext fun n => by
        rw [frobenius_eq_map_frobenius]
        exact pth_root_frobenius _
    right_inv := fun f =>
      ext fun n => by
        rw [frobenius_eq_map_frobenius]
        exact frobenius_pth_root _ }
#align witt_vector.frobenius_equiv WittVector.frobeniusEquiv

theorem frobenius_bijective [PerfectRing R p] :
    Function.Bijective (@WittVector.frobenius p R _ _) :=
  (frobeniusEquiv p R).Bijective
#align witt_vector.frobenius_bijective WittVector.frobenius_bijective

end CharP

end WittVector

