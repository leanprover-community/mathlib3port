import Mathbin.Data.Nat.Multiplicity
import Mathbin.RingTheory.WittVector.Basic
import Mathbin.RingTheory.WittVector.IsPoly

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

variable {p : ℕ} {R S : Type _} [hp : Fact p.prime] [CommRingₓ R] [CommRingₓ S]

local notation "𝕎" => WittVector p

noncomputable section

open MvPolynomial Finset

open_locale BigOperators

variable (p)

include hp

/--  The rational polynomials that give the coefficients of `frobenius x`,
in terms of the coefficients of `x`.
These polynomials actually have integral coefficients,
see `frobenius_poly` and `map_frobenius_poly`. -/
def frobenius_poly_rat (n : ℕ) : MvPolynomial ℕ ℚ :=
  bind₁ (wittPolynomial p ℚ ∘ fun n => n+1) (xInTermsOfW p ℚ n)

theorem bind₁_frobenius_poly_rat_witt_polynomial (n : ℕ) :
    bind₁ (frobenius_poly_rat p) (wittPolynomial p ℚ n) = wittPolynomial p ℚ (n+1) := by
  delta' frobenius_poly_rat
  rw [← bind₁_bind₁, bind₁_X_in_terms_of_W_witt_polynomial, bind₁_X_right]

/--  An auxiliary definition, to avoid an excessive amount of finiteness proofs
for `multiplicity p n`. -/
private def pnat_multiplicity (n : ℕ+) : ℕ :=
  (multiplicity p n).get $ multiplicity.finite_nat_iff.mpr $ ⟨ne_of_gtₓ hp.1.one_lt, n.2⟩

local notation "v" => pnat_multiplicity

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  [(Command.docComment
    "/--"
    " An auxiliary polynomial over the integers, that satisfies\n`p * (frobenius_poly_aux p n) + X n ^ p = frobenius_poly p n`.\nThis makes it easy to show that `frobenius_poly p n` is congruent to `X n ^ p`\nmodulo `p`. -/")]
  []
  []
  [(Command.noncomputable "noncomputable")]
  []
  [])
 (Command.def
  "def"
  (Command.declId `frobenius_poly_aux [])
  (Command.optDeclSig
   []
   [(Term.typeSpec ":" (Term.arrow (termℕ "ℕ") "→" (Term.app `MvPolynomial [(termℕ "ℕ") (termℤ "ℤ")])))])
  (Command.declValEqns
   (Term.matchAltsWhereDecls
    (Term.matchAlts
     [(Term.matchAlt
       "|"
       [`n]
       "=>"
       («term_-_»
        (Term.app `X [(Init.Logic.«term_+_» `n "+" (numLit "1"))])
        "-"
        (Algebra.BigOperators.Basic.«term∑_,_»
         "∑"
         (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] [":" (Term.app `Finₓ [`n])]))
         ", "
         (Term.have
          "have"
          (Term.haveDecl (Term.haveIdDecl [] [] ":=" `i.is_lt))
          []
          (Algebra.BigOperators.Basic.«term∑_in_,_»
           "∑"
           (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `j)] []))
           " in "
           (Term.app `range [(Cardinal.SetTheory.Cofinality.«term_^_» `p "^" («term_-_» `n "-" `i))])
           ", "
           (Finset.Data.Finset.Fold.«term_*_»
            (Finset.Data.Finset.Fold.«term_*_»
             (Cardinal.SetTheory.Cofinality.«term_^_»
              (Cardinal.SetTheory.Cofinality.«term_^_» (Term.app `X [`i]) "^" `p)
              "^"
              («term_-_»
               (Cardinal.SetTheory.Cofinality.«term_^_» `p "^" («term_-_» `n "-" `i))
               "-"
               (Init.Logic.«term_+_» `j "+" (numLit "1"))))
             "*"
             (Cardinal.SetTheory.Cofinality.«term_^_»
              (Term.app `frobenius_poly_aux [`i])
              "^"
              (Init.Logic.«term_+_» `j "+" (numLit "1"))))
            "*"
            (Term.app
             `C
             [(Init.Coe.«term↑_»
               "↑"
               (Term.paren
                "("
                [(Finset.Data.Finset.Fold.«term_*_»
                  («term_/_»
                   (Term.app
                    (Term.proj (Cardinal.SetTheory.Cofinality.«term_^_» `p "^" («term_-_» `n "-" `i)) "." `choose)
                    [(Init.Logic.«term_+_» `j "+" (numLit "1"))])
                   "/"
                   (Cardinal.SetTheory.Cofinality.«term_^_»
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
                        [(Init.Logic.«term_+_» `j "+" (numLit "1")) "," (Term.app `Nat.succ_posₓ [`j])]
                        "⟩")]))))
                  "*"
                  (Cardinal.SetTheory.Cofinality.«term_^_»
                   (Init.Coe.«term↑_» "↑" `p)
                   "^"
                   («term_-_»
                    `j
                    "-"
                    (Term.app
                     (WittVector.RingTheory.WittVector.Frobenius.termv "v")
                     [`p
                      (Term.anonymousCtor
                       "⟨"
                       [(Init.Logic.«term_+_» `j "+" (numLit "1")) "," (Term.app `Nat.succ_posₓ [`j])]
                       "⟩")]))))
                 [(Term.typeAscription ":" (termℕ "ℕ"))]]
                ")"))])))))))])
    []))
  []
  []
  []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'Lean.Parser.Command.declaration.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.def.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValEqns', expected 'Lean.Parser.Command.declValSimple.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValEqns', expected 'Lean.Parser.Command.declValSimple'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValEqns', expected 'Lean.Parser.Command.declValEqns.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.matchAltsWhereDecls', expected 'Lean.Parser.Term.matchAltsWhereDecls.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.matchAlts', expected 'Lean.Parser.Term.matchAlts.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.matchAlt', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.matchAlt', expected 'Lean.Parser.Term.matchAlt.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_-_»
   (Term.app `X [(Init.Logic.«term_+_» `n "+" (numLit "1"))])
   "-"
   (Algebra.BigOperators.Basic.«term∑_,_»
    "∑"
    (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] [":" (Term.app `Finₓ [`n])]))
    ", "
    (Term.have
     "have"
     (Term.haveDecl (Term.haveIdDecl [] [] ":=" `i.is_lt))
     []
     (Algebra.BigOperators.Basic.«term∑_in_,_»
      "∑"
      (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `j)] []))
      " in "
      (Term.app `range [(Cardinal.SetTheory.Cofinality.«term_^_» `p "^" («term_-_» `n "-" `i))])
      ", "
      (Finset.Data.Finset.Fold.«term_*_»
       (Finset.Data.Finset.Fold.«term_*_»
        (Cardinal.SetTheory.Cofinality.«term_^_»
         (Cardinal.SetTheory.Cofinality.«term_^_» (Term.app `X [`i]) "^" `p)
         "^"
         («term_-_»
          (Cardinal.SetTheory.Cofinality.«term_^_» `p "^" («term_-_» `n "-" `i))
          "-"
          (Init.Logic.«term_+_» `j "+" (numLit "1"))))
        "*"
        (Cardinal.SetTheory.Cofinality.«term_^_»
         (Term.app `frobenius_poly_aux [`i])
         "^"
         (Init.Logic.«term_+_» `j "+" (numLit "1"))))
       "*"
       (Term.app
        `C
        [(Init.Coe.«term↑_»
          "↑"
          (Term.paren
           "("
           [(Finset.Data.Finset.Fold.«term_*_»
             («term_/_»
              (Term.app
               (Term.proj (Cardinal.SetTheory.Cofinality.«term_^_» `p "^" («term_-_» `n "-" `i)) "." `choose)
               [(Init.Logic.«term_+_» `j "+" (numLit "1"))])
              "/"
              (Cardinal.SetTheory.Cofinality.«term_^_»
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
                   [(Init.Logic.«term_+_» `j "+" (numLit "1")) "," (Term.app `Nat.succ_posₓ [`j])]
                   "⟩")]))))
             "*"
             (Cardinal.SetTheory.Cofinality.«term_^_»
              (Init.Coe.«term↑_» "↑" `p)
              "^"
              («term_-_»
               `j
               "-"
               (Term.app
                (WittVector.RingTheory.WittVector.Frobenius.termv "v")
                [`p
                 (Term.anonymousCtor
                  "⟨"
                  [(Init.Logic.«term_+_» `j "+" (numLit "1")) "," (Term.app `Nat.succ_posₓ [`j])]
                  "⟩")]))))
            [(Term.typeAscription ":" (termℕ "ℕ"))]]
           ")"))]))))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_-_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Algebra.BigOperators.Basic.«term∑_,_»
   "∑"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] [":" (Term.app `Finₓ [`n])]))
   ", "
   (Term.have
    "have"
    (Term.haveDecl (Term.haveIdDecl [] [] ":=" `i.is_lt))
    []
    (Algebra.BigOperators.Basic.«term∑_in_,_»
     "∑"
     (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `j)] []))
     " in "
     (Term.app `range [(Cardinal.SetTheory.Cofinality.«term_^_» `p "^" («term_-_» `n "-" `i))])
     ", "
     (Finset.Data.Finset.Fold.«term_*_»
      (Finset.Data.Finset.Fold.«term_*_»
       (Cardinal.SetTheory.Cofinality.«term_^_»
        (Cardinal.SetTheory.Cofinality.«term_^_» (Term.app `X [`i]) "^" `p)
        "^"
        («term_-_»
         (Cardinal.SetTheory.Cofinality.«term_^_» `p "^" («term_-_» `n "-" `i))
         "-"
         (Init.Logic.«term_+_» `j "+" (numLit "1"))))
       "*"
       (Cardinal.SetTheory.Cofinality.«term_^_»
        (Term.app `frobenius_poly_aux [`i])
        "^"
        (Init.Logic.«term_+_» `j "+" (numLit "1"))))
      "*"
      (Term.app
       `C
       [(Init.Coe.«term↑_»
         "↑"
         (Term.paren
          "("
          [(Finset.Data.Finset.Fold.«term_*_»
            («term_/_»
             (Term.app
              (Term.proj (Cardinal.SetTheory.Cofinality.«term_^_» `p "^" («term_-_» `n "-" `i)) "." `choose)
              [(Init.Logic.«term_+_» `j "+" (numLit "1"))])
             "/"
             (Cardinal.SetTheory.Cofinality.«term_^_»
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
                  [(Init.Logic.«term_+_» `j "+" (numLit "1")) "," (Term.app `Nat.succ_posₓ [`j])]
                  "⟩")]))))
            "*"
            (Cardinal.SetTheory.Cofinality.«term_^_»
             (Init.Coe.«term↑_» "↑" `p)
             "^"
             («term_-_»
              `j
              "-"
              (Term.app
               (WittVector.RingTheory.WittVector.Frobenius.termv "v")
               [`p
                (Term.anonymousCtor
                 "⟨"
                 [(Init.Logic.«term_+_» `j "+" (numLit "1")) "," (Term.app `Nat.succ_posₓ [`j])]
                 "⟩")]))))
           [(Term.typeAscription ":" (termℕ "ℕ"))]]
          ")"))])))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.BigOperators.Basic.«term∑_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.have
   "have"
   (Term.haveDecl (Term.haveIdDecl [] [] ":=" `i.is_lt))
   []
   (Algebra.BigOperators.Basic.«term∑_in_,_»
    "∑"
    (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `j)] []))
    " in "
    (Term.app `range [(Cardinal.SetTheory.Cofinality.«term_^_» `p "^" («term_-_» `n "-" `i))])
    ", "
    (Finset.Data.Finset.Fold.«term_*_»
     (Finset.Data.Finset.Fold.«term_*_»
      (Cardinal.SetTheory.Cofinality.«term_^_»
       (Cardinal.SetTheory.Cofinality.«term_^_» (Term.app `X [`i]) "^" `p)
       "^"
       («term_-_»
        (Cardinal.SetTheory.Cofinality.«term_^_» `p "^" («term_-_» `n "-" `i))
        "-"
        (Init.Logic.«term_+_» `j "+" (numLit "1"))))
      "*"
      (Cardinal.SetTheory.Cofinality.«term_^_»
       (Term.app `frobenius_poly_aux [`i])
       "^"
       (Init.Logic.«term_+_» `j "+" (numLit "1"))))
     "*"
     (Term.app
      `C
      [(Init.Coe.«term↑_»
        "↑"
        (Term.paren
         "("
         [(Finset.Data.Finset.Fold.«term_*_»
           («term_/_»
            (Term.app
             (Term.proj (Cardinal.SetTheory.Cofinality.«term_^_» `p "^" («term_-_» `n "-" `i)) "." `choose)
             [(Init.Logic.«term_+_» `j "+" (numLit "1"))])
            "/"
            (Cardinal.SetTheory.Cofinality.«term_^_»
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
                 [(Init.Logic.«term_+_» `j "+" (numLit "1")) "," (Term.app `Nat.succ_posₓ [`j])]
                 "⟩")]))))
           "*"
           (Cardinal.SetTheory.Cofinality.«term_^_»
            (Init.Coe.«term↑_» "↑" `p)
            "^"
            («term_-_»
             `j
             "-"
             (Term.app
              (WittVector.RingTheory.WittVector.Frobenius.termv "v")
              [`p
               (Term.anonymousCtor
                "⟨"
                [(Init.Logic.«term_+_» `j "+" (numLit "1")) "," (Term.app `Nat.succ_posₓ [`j])]
                "⟩")]))))
          [(Term.typeAscription ":" (termℕ "ℕ"))]]
         ")"))]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.have', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.have', expected 'Lean.Parser.Term.have.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Algebra.BigOperators.Basic.«term∑_in_,_»
   "∑"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `j)] []))
   " in "
   (Term.app `range [(Cardinal.SetTheory.Cofinality.«term_^_» `p "^" («term_-_» `n "-" `i))])
   ", "
   (Finset.Data.Finset.Fold.«term_*_»
    (Finset.Data.Finset.Fold.«term_*_»
     (Cardinal.SetTheory.Cofinality.«term_^_»
      (Cardinal.SetTheory.Cofinality.«term_^_» (Term.app `X [`i]) "^" `p)
      "^"
      («term_-_»
       (Cardinal.SetTheory.Cofinality.«term_^_» `p "^" («term_-_» `n "-" `i))
       "-"
       (Init.Logic.«term_+_» `j "+" (numLit "1"))))
     "*"
     (Cardinal.SetTheory.Cofinality.«term_^_»
      (Term.app `frobenius_poly_aux [`i])
      "^"
      (Init.Logic.«term_+_» `j "+" (numLit "1"))))
    "*"
    (Term.app
     `C
     [(Init.Coe.«term↑_»
       "↑"
       (Term.paren
        "("
        [(Finset.Data.Finset.Fold.«term_*_»
          («term_/_»
           (Term.app
            (Term.proj (Cardinal.SetTheory.Cofinality.«term_^_» `p "^" («term_-_» `n "-" `i)) "." `choose)
            [(Init.Logic.«term_+_» `j "+" (numLit "1"))])
           "/"
           (Cardinal.SetTheory.Cofinality.«term_^_»
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
                [(Init.Logic.«term_+_» `j "+" (numLit "1")) "," (Term.app `Nat.succ_posₓ [`j])]
                "⟩")]))))
          "*"
          (Cardinal.SetTheory.Cofinality.«term_^_»
           (Init.Coe.«term↑_» "↑" `p)
           "^"
           («term_-_»
            `j
            "-"
            (Term.app
             (WittVector.RingTheory.WittVector.Frobenius.termv "v")
             [`p
              (Term.anonymousCtor
               "⟨"
               [(Init.Logic.«term_+_» `j "+" (numLit "1")) "," (Term.app `Nat.succ_posₓ [`j])]
               "⟩")]))))
         [(Term.typeAscription ":" (termℕ "ℕ"))]]
        ")"))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.BigOperators.Basic.«term∑_in_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Finset.Data.Finset.Fold.«term_*_»
   (Finset.Data.Finset.Fold.«term_*_»
    (Cardinal.SetTheory.Cofinality.«term_^_»
     (Cardinal.SetTheory.Cofinality.«term_^_» (Term.app `X [`i]) "^" `p)
     "^"
     («term_-_»
      (Cardinal.SetTheory.Cofinality.«term_^_» `p "^" («term_-_» `n "-" `i))
      "-"
      (Init.Logic.«term_+_» `j "+" (numLit "1"))))
    "*"
    (Cardinal.SetTheory.Cofinality.«term_^_»
     (Term.app `frobenius_poly_aux [`i])
     "^"
     (Init.Logic.«term_+_» `j "+" (numLit "1"))))
   "*"
   (Term.app
    `C
    [(Init.Coe.«term↑_»
      "↑"
      (Term.paren
       "("
       [(Finset.Data.Finset.Fold.«term_*_»
         («term_/_»
          (Term.app
           (Term.proj (Cardinal.SetTheory.Cofinality.«term_^_» `p "^" («term_-_» `n "-" `i)) "." `choose)
           [(Init.Logic.«term_+_» `j "+" (numLit "1"))])
          "/"
          (Cardinal.SetTheory.Cofinality.«term_^_»
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
               [(Init.Logic.«term_+_» `j "+" (numLit "1")) "," (Term.app `Nat.succ_posₓ [`j])]
               "⟩")]))))
         "*"
         (Cardinal.SetTheory.Cofinality.«term_^_»
          (Init.Coe.«term↑_» "↑" `p)
          "^"
          («term_-_»
           `j
           "-"
           (Term.app
            (WittVector.RingTheory.WittVector.Frobenius.termv "v")
            [`p
             (Term.anonymousCtor
              "⟨"
              [(Init.Logic.«term_+_» `j "+" (numLit "1")) "," (Term.app `Nat.succ_posₓ [`j])]
              "⟩")]))))
        [(Term.typeAscription ":" (termℕ "ℕ"))]]
       ")"))]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `C
   [(Init.Coe.«term↑_»
     "↑"
     (Term.paren
      "("
      [(Finset.Data.Finset.Fold.«term_*_»
        («term_/_»
         (Term.app
          (Term.proj (Cardinal.SetTheory.Cofinality.«term_^_» `p "^" («term_-_» `n "-" `i)) "." `choose)
          [(Init.Logic.«term_+_» `j "+" (numLit "1"))])
         "/"
         (Cardinal.SetTheory.Cofinality.«term_^_»
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
              [(Init.Logic.«term_+_» `j "+" (numLit "1")) "," (Term.app `Nat.succ_posₓ [`j])]
              "⟩")]))))
        "*"
        (Cardinal.SetTheory.Cofinality.«term_^_»
         (Init.Coe.«term↑_» "↑" `p)
         "^"
         («term_-_»
          `j
          "-"
          (Term.app
           (WittVector.RingTheory.WittVector.Frobenius.termv "v")
           [`p
            (Term.anonymousCtor
             "⟨"
             [(Init.Logic.«term_+_» `j "+" (numLit "1")) "," (Term.app `Nat.succ_posₓ [`j])]
             "⟩")]))))
       [(Term.typeAscription ":" (termℕ "ℕ"))]]
      ")"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Coe.«term↑_»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Coe.«term↑_»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Coe.«term↑_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Coe.«term↑_»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Coe.«term↑_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Coe.«term↑_»
   "↑"
   (Term.paren
    "("
    [(Finset.Data.Finset.Fold.«term_*_»
      («term_/_»
       (Term.app
        (Term.proj (Cardinal.SetTheory.Cofinality.«term_^_» `p "^" («term_-_» `n "-" `i)) "." `choose)
        [(Init.Logic.«term_+_» `j "+" (numLit "1"))])
       "/"
       (Cardinal.SetTheory.Cofinality.«term_^_»
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
            [(Init.Logic.«term_+_» `j "+" (numLit "1")) "," (Term.app `Nat.succ_posₓ [`j])]
            "⟩")]))))
      "*"
      (Cardinal.SetTheory.Cofinality.«term_^_»
       (Init.Coe.«term↑_» "↑" `p)
       "^"
       («term_-_»
        `j
        "-"
        (Term.app
         (WittVector.RingTheory.WittVector.Frobenius.termv "v")
         [`p
          (Term.anonymousCtor
           "⟨"
           [(Init.Logic.«term_+_» `j "+" (numLit "1")) "," (Term.app `Nat.succ_posₓ [`j])]
           "⟩")]))))
     [(Term.typeAscription ":" (termℕ "ℕ"))]]
    ")"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Coe.«term↑_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.paren
   "("
   [(Finset.Data.Finset.Fold.«term_*_»
     («term_/_»
      (Term.app
       (Term.proj (Cardinal.SetTheory.Cofinality.«term_^_» `p "^" («term_-_» `n "-" `i)) "." `choose)
       [(Init.Logic.«term_+_» `j "+" (numLit "1"))])
      "/"
      (Cardinal.SetTheory.Cofinality.«term_^_»
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
           [(Init.Logic.«term_+_» `j "+" (numLit "1")) "," (Term.app `Nat.succ_posₓ [`j])]
           "⟩")]))))
     "*"
     (Cardinal.SetTheory.Cofinality.«term_^_»
      (Init.Coe.«term↑_» "↑" `p)
      "^"
      («term_-_»
       `j
       "-"
       (Term.app
        (WittVector.RingTheory.WittVector.Frobenius.termv "v")
        [`p
         (Term.anonymousCtor
          "⟨"
          [(Init.Logic.«term_+_» `j "+" (numLit "1")) "," (Term.app `Nat.succ_posₓ [`j])]
          "⟩")]))))
    [(Term.typeAscription ":" (termℕ "ℕ"))]]
   ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.paren.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.typeAscription.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (termℕ "ℕ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'termℕ', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  (Finset.Data.Finset.Fold.«term_*_»
   («term_/_»
    (Term.app
     (Term.proj (Cardinal.SetTheory.Cofinality.«term_^_» `p "^" («term_-_» `n "-" `i)) "." `choose)
     [(Init.Logic.«term_+_» `j "+" (numLit "1"))])
    "/"
    (Cardinal.SetTheory.Cofinality.«term_^_»
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
         [(Init.Logic.«term_+_» `j "+" (numLit "1")) "," (Term.app `Nat.succ_posₓ [`j])]
         "⟩")]))))
   "*"
   (Cardinal.SetTheory.Cofinality.«term_^_»
    (Init.Coe.«term↑_» "↑" `p)
    "^"
    («term_-_»
     `j
     "-"
     (Term.app
      (WittVector.RingTheory.WittVector.Frobenius.termv "v")
      [`p
       (Term.anonymousCtor "⟨" [(Init.Logic.«term_+_» `j "+" (numLit "1")) "," (Term.app `Nat.succ_posₓ [`j])] "⟩")]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Cardinal.SetTheory.Cofinality.«term_^_»
   (Init.Coe.«term↑_» "↑" `p)
   "^"
   («term_-_»
    `j
    "-"
    (Term.app
     (WittVector.RingTheory.WittVector.Frobenius.termv "v")
     [`p
      (Term.anonymousCtor "⟨" [(Init.Logic.«term_+_» `j "+" (numLit "1")) "," (Term.app `Nat.succ_posₓ [`j])] "⟩")])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Cardinal.SetTheory.Cofinality.«term_^_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_-_»
   `j
   "-"
   (Term.app
    (WittVector.RingTheory.WittVector.Frobenius.termv "v")
    [`p (Term.anonymousCtor "⟨" [(Init.Logic.«term_+_» `j "+" (numLit "1")) "," (Term.app `Nat.succ_posₓ [`j])] "⟩")]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_-_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   (WittVector.RingTheory.WittVector.Frobenius.termv "v")
   [`p (Term.anonymousCtor "⟨" [(Init.Logic.«term_+_» `j "+" (numLit "1")) "," (Term.app `Nat.succ_posₓ [`j])] "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor "⟨" [(Init.Logic.«term_+_» `j "+" (numLit "1")) "," (Term.app `Nat.succ_posₓ [`j])] "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Nat.succ_posₓ [`j])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `j
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Nat.succ_posₓ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Logic.«term_+_» `j "+" (numLit "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "1")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `j
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  `p
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (WittVector.RingTheory.WittVector.Frobenius.termv "v")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'WittVector.RingTheory.WittVector.Frobenius.termv', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
  `j
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 0, term))
  (Init.Coe.«term↑_» "↑" `p)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Coe.«term↑_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `p
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 999 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1 >? 999, (some 999, term) <=? (some 0, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 0, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  («term_/_»
   (Term.app
    (Term.proj (Cardinal.SetTheory.Cofinality.«term_^_» `p "^" («term_-_» `n "-" `i)) "." `choose)
    [(Init.Logic.«term_+_» `j "+" (numLit "1"))])
   "/"
   (Cardinal.SetTheory.Cofinality.«term_^_»
    `p
    "^"
    («term_-_»
     («term_-_» `n "-" `i)
     "-"
     (Term.app
      (WittVector.RingTheory.WittVector.Frobenius.termv "v")
      [`p
       (Term.anonymousCtor "⟨" [(Init.Logic.«term_+_» `j "+" (numLit "1")) "," (Term.app `Nat.succ_posₓ [`j])] "⟩")]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_/_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Cardinal.SetTheory.Cofinality.«term_^_»
   `p
   "^"
   («term_-_»
    («term_-_» `n "-" `i)
    "-"
    (Term.app
     (WittVector.RingTheory.WittVector.Frobenius.termv "v")
     [`p
      (Term.anonymousCtor "⟨" [(Init.Logic.«term_+_» `j "+" (numLit "1")) "," (Term.app `Nat.succ_posₓ [`j])] "⟩")])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Cardinal.SetTheory.Cofinality.«term_^_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_-_»
   («term_-_» `n "-" `i)
   "-"
   (Term.app
    (WittVector.RingTheory.WittVector.Frobenius.termv "v")
    [`p (Term.anonymousCtor "⟨" [(Init.Logic.«term_+_» `j "+" (numLit "1")) "," (Term.app `Nat.succ_posₓ [`j])] "⟩")]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_-_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   (WittVector.RingTheory.WittVector.Frobenius.termv "v")
   [`p (Term.anonymousCtor "⟨" [(Init.Logic.«term_+_» `j "+" (numLit "1")) "," (Term.app `Nat.succ_posₓ [`j])] "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor "⟨" [(Init.Logic.«term_+_» `j "+" (numLit "1")) "," (Term.app `Nat.succ_posₓ [`j])] "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Nat.succ_posₓ [`j])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `j
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Nat.succ_posₓ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Logic.«term_+_» `j "+" (numLit "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "1")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `j
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  `p
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (WittVector.RingTheory.WittVector.Frobenius.termv "v")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'WittVector.RingTheory.WittVector.Frobenius.termv', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
  («term_-_» `n "-" `i)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_-_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `i
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 65 >? 65, (some 66, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 0, term))
  `p
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1 >? 1024, (none, [anonymous]) <=? (some 0, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 0, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Cardinal.SetTheory.Cofinality.«term_^_»
   `p
   "^"
   («term_-_»
    («term_-_» `n "-" `i)
    "-"
    (Term.app
     (WittVector.RingTheory.WittVector.Frobenius.termv "v")
     [`p
      (Term.anonymousCtor "⟨" [(Init.Logic.«term_+_» `j "+" (numLit "1")) "," (Term.app `Nat.succ_posₓ [`j])] "⟩")])))
  []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
  (Term.app
   (Term.proj (Cardinal.SetTheory.Cofinality.«term_^_» `p "^" («term_-_» `n "-" `i)) "." `choose)
   [(Init.Logic.«term_+_» `j "+" (numLit "1"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Logic.«term_+_» `j "+" (numLit "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "1")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `j
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Init.Logic.«term_+_» `j "+" (numLit "1")) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.proj (Cardinal.SetTheory.Cofinality.«term_^_» `p "^" («term_-_» `n "-" `i)) "." `choose)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Cardinal.SetTheory.Cofinality.«term_^_» `p "^" («term_-_» `n "-" `i))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Cardinal.SetTheory.Cofinality.«term_^_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_-_» `n "-" `i)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_-_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `i
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 0, term))
  `p
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1 >? 1024, (none, [anonymous]) <=? (some 0, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 0, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Cardinal.SetTheory.Cofinality.«term_^_» `p "^" («term_-_» `n "-" `i)) []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1022, (some 1023, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 70, (some 71, term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(«term_/_»
   (Term.app
    (Term.proj
     (Term.paren "(" [(Cardinal.SetTheory.Cofinality.«term_^_» `p "^" («term_-_» `n "-" `i)) []] ")")
     "."
     `choose)
    [(Term.paren "(" [(Init.Logic.«term_+_» `j "+" (numLit "1")) []] ")")])
   "/"
   (Term.paren
    "("
    [(Cardinal.SetTheory.Cofinality.«term_^_»
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
          [(Init.Logic.«term_+_» `j "+" (numLit "1")) "," (Term.app `Nat.succ_posₓ [`j])]
          "⟩")])))
     []]
    ")"))
  []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 999 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 999, (some 999, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Init.Coe.«term↑_»
   "↑"
   (Term.paren
    "("
    [(Finset.Data.Finset.Fold.«term_*_»
      (Term.paren
       "("
       [(«term_/_»
         (Term.app
          (Term.proj
           (Term.paren "(" [(Cardinal.SetTheory.Cofinality.«term_^_» `p "^" («term_-_» `n "-" `i)) []] ")")
           "."
           `choose)
          [(Term.paren "(" [(Init.Logic.«term_+_» `j "+" (numLit "1")) []] ")")])
         "/"
         (Term.paren
          "("
          [(Cardinal.SetTheory.Cofinality.«term_^_»
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
                [(Init.Logic.«term_+_» `j "+" (numLit "1")) "," (Term.app `Nat.succ_posₓ [`j])]
                "⟩")])))
           []]
          ")"))
        []]
       ")")
      "*"
      (Cardinal.SetTheory.Cofinality.«term_^_»
       (Init.Coe.«term↑_» "↑" `p)
       "^"
       («term_-_»
        `j
        "-"
        (Term.app
         (WittVector.RingTheory.WittVector.Frobenius.termv "v")
         [`p
          (Term.anonymousCtor
           "⟨"
           [(Init.Logic.«term_+_» `j "+" (numLit "1")) "," (Term.app `Nat.succ_posₓ [`j])]
           "⟩")]))))
     [(Term.typeAscription ":" (termℕ "ℕ"))]]
    ")"))
  []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `C
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Finset.Data.Finset.Fold.«term_*_»
   (Cardinal.SetTheory.Cofinality.«term_^_»
    (Cardinal.SetTheory.Cofinality.«term_^_» (Term.app `X [`i]) "^" `p)
    "^"
    («term_-_»
     (Cardinal.SetTheory.Cofinality.«term_^_» `p "^" («term_-_» `n "-" `i))
     "-"
     (Init.Logic.«term_+_» `j "+" (numLit "1"))))
   "*"
   (Cardinal.SetTheory.Cofinality.«term_^_»
    (Term.app `frobenius_poly_aux [`i])
    "^"
    (Init.Logic.«term_+_» `j "+" (numLit "1"))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Cardinal.SetTheory.Cofinality.«term_^_»
   (Term.app `frobenius_poly_aux [`i])
   "^"
   (Init.Logic.«term_+_» `j "+" (numLit "1")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Cardinal.SetTheory.Cofinality.«term_^_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Logic.«term_+_» `j "+" (numLit "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "1")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `j
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 0, term))
  (Term.app `frobenius_poly_aux [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `i
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `frobenius_poly_aux
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1 >? 1022, (some 1023, term) <=? (some 0, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 0, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Cardinal.SetTheory.Cofinality.«term_^_»
   (Cardinal.SetTheory.Cofinality.«term_^_» (Term.app `X [`i]) "^" `p)
   "^"
   («term_-_»
    (Cardinal.SetTheory.Cofinality.«term_^_» `p "^" («term_-_» `n "-" `i))
    "-"
    (Init.Logic.«term_+_» `j "+" (numLit "1"))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Cardinal.SetTheory.Cofinality.«term_^_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_-_»
   (Cardinal.SetTheory.Cofinality.«term_^_» `p "^" («term_-_» `n "-" `i))
   "-"
   (Init.Logic.«term_+_» `j "+" (numLit "1")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_-_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Logic.«term_+_» `j "+" (numLit "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "1")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `j
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
  (Cardinal.SetTheory.Cofinality.«term_^_» `p "^" («term_-_» `n "-" `i))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Cardinal.SetTheory.Cofinality.«term_^_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_-_» `n "-" `i)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_-_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `i
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 0, term))
  `p
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1 >? 1024, (none, [anonymous]) <=? (some 0, term)
[PrettyPrinter.parenthesize] ...precedences are 65 >? 0, (some 0, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Cardinal.SetTheory.Cofinality.«term_^_» `p "^" («term_-_» `n "-" `i)) []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 65, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 0, term))
  (Cardinal.SetTheory.Cofinality.«term_^_» (Term.app `X [`i]) "^" `p)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Cardinal.SetTheory.Cofinality.«term_^_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `p
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 0, term))
  (Term.app `X [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `i
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `X
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1 >? 1022, (some 1023, term) <=? (some 0, term)
[PrettyPrinter.parenthesize] ...precedences are 1 >? 0, (some 0, term) <=? (some 0, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Cardinal.SetTheory.Cofinality.«term_^_» (Term.app `X [`i]) "^" `p) []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 0, (some 0, term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Cardinal.SetTheory.Cofinality.«term_^_»
   (Term.paren "(" [(Cardinal.SetTheory.Cofinality.«term_^_» (Term.app `X [`i]) "^" `p) []] ")")
   "^"
   («term_-_»
    (Term.paren "(" [(Cardinal.SetTheory.Cofinality.«term_^_» `p "^" («term_-_» `n "-" `i)) []] ")")
    "-"
    (Init.Logic.«term_+_» `j "+" (numLit "1"))))
  []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Finset.Data.Finset.Fold.«term_*_»
   (Term.paren
    "("
    [(Cardinal.SetTheory.Cofinality.«term_^_»
      (Term.paren "(" [(Cardinal.SetTheory.Cofinality.«term_^_» (Term.app `X [`i]) "^" `p) []] ")")
      "^"
      («term_-_»
       (Term.paren "(" [(Cardinal.SetTheory.Cofinality.«term_^_» `p "^" («term_-_» `n "-" `i)) []] ")")
       "-"
       (Init.Logic.«term_+_» `j "+" (numLit "1"))))
     []]
    ")")
   "*"
   (Cardinal.SetTheory.Cofinality.«term_^_»
    (Term.app `frobenius_poly_aux [`i])
    "^"
    (Init.Logic.«term_+_» `j "+" (numLit "1"))))
  []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `range [(Cardinal.SetTheory.Cofinality.«term_^_» `p "^" («term_-_» `n "-" `i))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Cardinal.SetTheory.Cofinality.«term_^_»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Cardinal.SetTheory.Cofinality.«term_^_»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Cardinal.SetTheory.Cofinality.«term_^_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Cardinal.SetTheory.Cofinality.«term_^_»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Cardinal.SetTheory.Cofinality.«term_^_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Cardinal.SetTheory.Cofinality.«term_^_» `p "^" («term_-_» `n "-" `i))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Cardinal.SetTheory.Cofinality.«term_^_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_-_» `n "-" `i)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_-_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `i
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 0, term))
  `p
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1 >? 1024, (none, [anonymous]) <=? (some 0, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 0, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Cardinal.SetTheory.Cofinality.«term_^_» `p "^" («term_-_» `n "-" `i)) []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `range
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.explicitBinders', expected 'Mathlib.ExtendedBinder.extBinders'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValEqns', expected 'Lean.Parser.Command.whereStructInst.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValEqns', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.constant.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.constant'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
      An auxiliary polynomial over the integers, that satisfies
      `p * (frobenius_poly_aux p n) + X n ^ p = frobenius_poly p n`.
      This makes it easy to show that `frobenius_poly p n` is congruent to `X n ^ p`
      modulo `p`. -/
    noncomputable
  def
    frobenius_poly_aux
    : ℕ → MvPolynomial ℕ ℤ
    |
      n
      =>
      X n + 1
        -
        ∑
          i : Finₓ n
          ,
          have
            := i.is_lt
            ∑
              j
              in
              range p ^ n - i
              ,
              X i ^ p ^ p ^ n - i - j + 1 * frobenius_poly_aux i ^ j + 1
                *
                C
                  ↑
                    (
                      p ^ n - i . choose j + 1 / p ^ n - i - v p ⟨ j + 1 , Nat.succ_posₓ j ⟩
                          *
                          ↑ p ^ j - v p ⟨ j + 1 , Nat.succ_posₓ j ⟩
                        : ℕ
                      )

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
     (Term.app `frobenius_poly_aux [`p `n])
     "="
     («term_-_»
      (Term.app `X [(Init.Logic.«term_+_» `n "+" (numLit "1"))])
      "-"
      (Algebra.BigOperators.Basic.«term∑_in_,_»
       "∑"
       (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
       " in "
       (Term.app `range [`n])
       ", "
       (Algebra.BigOperators.Basic.«term∑_in_,_»
        "∑"
        (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `j)] []))
        " in "
        (Term.app `range [(Cardinal.SetTheory.Cofinality.«term_^_» `p "^" («term_-_» `n "-" `i))])
        ", "
        (Finset.Data.Finset.Fold.«term_*_»
         (Finset.Data.Finset.Fold.«term_*_»
          (Cardinal.SetTheory.Cofinality.«term_^_»
           (Cardinal.SetTheory.Cofinality.«term_^_» (Term.app `X [`i]) "^" `p)
           "^"
           («term_-_»
            (Cardinal.SetTheory.Cofinality.«term_^_» `p "^" («term_-_» `n "-" `i))
            "-"
            (Init.Logic.«term_+_» `j "+" (numLit "1"))))
          "*"
          (Cardinal.SetTheory.Cofinality.«term_^_»
           (Term.app `frobenius_poly_aux [`p `i])
           "^"
           (Init.Logic.«term_+_» `j "+" (numLit "1"))))
         "*"
         (Term.app
          `C
          [(Init.Coe.«term↑_»
            "↑"
            (Term.paren
             "("
             [(Finset.Data.Finset.Fold.«term_*_»
               («term_/_»
                (Term.app
                 (Term.proj (Cardinal.SetTheory.Cofinality.«term_^_» `p "^" («term_-_» `n "-" `i)) "." `choose)
                 [(Init.Logic.«term_+_» `j "+" (numLit "1"))])
                "/"
                (Cardinal.SetTheory.Cofinality.«term_^_»
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
                     [(Init.Logic.«term_+_» `j "+" (numLit "1")) "," (Term.app `Nat.succ_posₓ [`j])]
                     "⟩")]))))
               "*"
               (Cardinal.SetTheory.Cofinality.«term_^_»
                (Init.Coe.«term↑_» "↑" `p)
                "^"
                («term_-_»
                 `j
                 "-"
                 (Term.app
                  (WittVector.RingTheory.WittVector.Frobenius.termv "v")
                  [`p
                   (Term.anonymousCtor
                    "⟨"
                    [(Init.Logic.«term_+_» `j "+" (numLit "1")) "," (Term.app `Nat.succ_posₓ [`j])]
                    "⟩")]))))
              [(Term.typeAscription ":" (termℕ "ℕ"))]]
             ")"))]))))))))
  (Command.declValSimple
   ":="
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule [] `frobenius_poly_aux) "," (Tactic.rwRule ["←"] `Finₓ.sum_univ_eq_sum_range)]
          "]")
         [])
        [])])))
   [])
  []
  []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'Lean.Parser.Command.declaration.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.theorem.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValSimple.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.rwSeq
        "rw"
        []
        (Tactic.rwRuleSeq
         "["
         [(Tactic.rwRule [] `frobenius_poly_aux) "," (Tactic.rwRule ["←"] `Finₓ.sum_univ_eq_sum_range)]
         "]")
        [])
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.rwSeq
   "rw"
   []
   (Tactic.rwRuleSeq
    "["
    [(Tactic.rwRule [] `frobenius_poly_aux) "," (Tactic.rwRule ["←"] `Finₓ.sum_univ_eq_sum_range)]
    "]")
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwSeq', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Finₓ.sum_univ_eq_sum_range
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«←»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `frobenius_poly_aux
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declSig', expected 'Lean.Parser.Command.declSig.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  («term_=_»
   (Term.app `frobenius_poly_aux [`p `n])
   "="
   («term_-_»
    (Term.app `X [(Init.Logic.«term_+_» `n "+" (numLit "1"))])
    "-"
    (Algebra.BigOperators.Basic.«term∑_in_,_»
     "∑"
     (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
     " in "
     (Term.app `range [`n])
     ", "
     (Algebra.BigOperators.Basic.«term∑_in_,_»
      "∑"
      (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `j)] []))
      " in "
      (Term.app `range [(Cardinal.SetTheory.Cofinality.«term_^_» `p "^" («term_-_» `n "-" `i))])
      ", "
      (Finset.Data.Finset.Fold.«term_*_»
       (Finset.Data.Finset.Fold.«term_*_»
        (Cardinal.SetTheory.Cofinality.«term_^_»
         (Cardinal.SetTheory.Cofinality.«term_^_» (Term.app `X [`i]) "^" `p)
         "^"
         («term_-_»
          (Cardinal.SetTheory.Cofinality.«term_^_» `p "^" («term_-_» `n "-" `i))
          "-"
          (Init.Logic.«term_+_» `j "+" (numLit "1"))))
        "*"
        (Cardinal.SetTheory.Cofinality.«term_^_»
         (Term.app `frobenius_poly_aux [`p `i])
         "^"
         (Init.Logic.«term_+_» `j "+" (numLit "1"))))
       "*"
       (Term.app
        `C
        [(Init.Coe.«term↑_»
          "↑"
          (Term.paren
           "("
           [(Finset.Data.Finset.Fold.«term_*_»
             («term_/_»
              (Term.app
               (Term.proj (Cardinal.SetTheory.Cofinality.«term_^_» `p "^" («term_-_» `n "-" `i)) "." `choose)
               [(Init.Logic.«term_+_» `j "+" (numLit "1"))])
              "/"
              (Cardinal.SetTheory.Cofinality.«term_^_»
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
                   [(Init.Logic.«term_+_» `j "+" (numLit "1")) "," (Term.app `Nat.succ_posₓ [`j])]
                   "⟩")]))))
             "*"
             (Cardinal.SetTheory.Cofinality.«term_^_»
              (Init.Coe.«term↑_» "↑" `p)
              "^"
              («term_-_»
               `j
               "-"
               (Term.app
                (WittVector.RingTheory.WittVector.Frobenius.termv "v")
                [`p
                 (Term.anonymousCtor
                  "⟨"
                  [(Init.Logic.«term_+_» `j "+" (numLit "1")) "," (Term.app `Nat.succ_posₓ [`j])]
                  "⟩")]))))
            [(Term.typeAscription ":" (termℕ "ℕ"))]]
           ")"))]))))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_-_»
   (Term.app `X [(Init.Logic.«term_+_» `n "+" (numLit "1"))])
   "-"
   (Algebra.BigOperators.Basic.«term∑_in_,_»
    "∑"
    (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
    " in "
    (Term.app `range [`n])
    ", "
    (Algebra.BigOperators.Basic.«term∑_in_,_»
     "∑"
     (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `j)] []))
     " in "
     (Term.app `range [(Cardinal.SetTheory.Cofinality.«term_^_» `p "^" («term_-_» `n "-" `i))])
     ", "
     (Finset.Data.Finset.Fold.«term_*_»
      (Finset.Data.Finset.Fold.«term_*_»
       (Cardinal.SetTheory.Cofinality.«term_^_»
        (Cardinal.SetTheory.Cofinality.«term_^_» (Term.app `X [`i]) "^" `p)
        "^"
        («term_-_»
         (Cardinal.SetTheory.Cofinality.«term_^_» `p "^" («term_-_» `n "-" `i))
         "-"
         (Init.Logic.«term_+_» `j "+" (numLit "1"))))
       "*"
       (Cardinal.SetTheory.Cofinality.«term_^_»
        (Term.app `frobenius_poly_aux [`p `i])
        "^"
        (Init.Logic.«term_+_» `j "+" (numLit "1"))))
      "*"
      (Term.app
       `C
       [(Init.Coe.«term↑_»
         "↑"
         (Term.paren
          "("
          [(Finset.Data.Finset.Fold.«term_*_»
            («term_/_»
             (Term.app
              (Term.proj (Cardinal.SetTheory.Cofinality.«term_^_» `p "^" («term_-_» `n "-" `i)) "." `choose)
              [(Init.Logic.«term_+_» `j "+" (numLit "1"))])
             "/"
             (Cardinal.SetTheory.Cofinality.«term_^_»
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
                  [(Init.Logic.«term_+_» `j "+" (numLit "1")) "," (Term.app `Nat.succ_posₓ [`j])]
                  "⟩")]))))
            "*"
            (Cardinal.SetTheory.Cofinality.«term_^_»
             (Init.Coe.«term↑_» "↑" `p)
             "^"
             («term_-_»
              `j
              "-"
              (Term.app
               (WittVector.RingTheory.WittVector.Frobenius.termv "v")
               [`p
                (Term.anonymousCtor
                 "⟨"
                 [(Init.Logic.«term_+_» `j "+" (numLit "1")) "," (Term.app `Nat.succ_posₓ [`j])]
                 "⟩")]))))
           [(Term.typeAscription ":" (termℕ "ℕ"))]]
          ")"))])))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_-_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Algebra.BigOperators.Basic.«term∑_in_,_»
   "∑"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
   " in "
   (Term.app `range [`n])
   ", "
   (Algebra.BigOperators.Basic.«term∑_in_,_»
    "∑"
    (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `j)] []))
    " in "
    (Term.app `range [(Cardinal.SetTheory.Cofinality.«term_^_» `p "^" («term_-_» `n "-" `i))])
    ", "
    (Finset.Data.Finset.Fold.«term_*_»
     (Finset.Data.Finset.Fold.«term_*_»
      (Cardinal.SetTheory.Cofinality.«term_^_»
       (Cardinal.SetTheory.Cofinality.«term_^_» (Term.app `X [`i]) "^" `p)
       "^"
       («term_-_»
        (Cardinal.SetTheory.Cofinality.«term_^_» `p "^" («term_-_» `n "-" `i))
        "-"
        (Init.Logic.«term_+_» `j "+" (numLit "1"))))
      "*"
      (Cardinal.SetTheory.Cofinality.«term_^_»
       (Term.app `frobenius_poly_aux [`p `i])
       "^"
       (Init.Logic.«term_+_» `j "+" (numLit "1"))))
     "*"
     (Term.app
      `C
      [(Init.Coe.«term↑_»
        "↑"
        (Term.paren
         "("
         [(Finset.Data.Finset.Fold.«term_*_»
           («term_/_»
            (Term.app
             (Term.proj (Cardinal.SetTheory.Cofinality.«term_^_» `p "^" («term_-_» `n "-" `i)) "." `choose)
             [(Init.Logic.«term_+_» `j "+" (numLit "1"))])
            "/"
            (Cardinal.SetTheory.Cofinality.«term_^_»
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
                 [(Init.Logic.«term_+_» `j "+" (numLit "1")) "," (Term.app `Nat.succ_posₓ [`j])]
                 "⟩")]))))
           "*"
           (Cardinal.SetTheory.Cofinality.«term_^_»
            (Init.Coe.«term↑_» "↑" `p)
            "^"
            («term_-_»
             `j
             "-"
             (Term.app
              (WittVector.RingTheory.WittVector.Frobenius.termv "v")
              [`p
               (Term.anonymousCtor
                "⟨"
                [(Init.Logic.«term_+_» `j "+" (numLit "1")) "," (Term.app `Nat.succ_posₓ [`j])]
                "⟩")]))))
          [(Term.typeAscription ":" (termℕ "ℕ"))]]
         ")"))]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.BigOperators.Basic.«term∑_in_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Algebra.BigOperators.Basic.«term∑_in_,_»
   "∑"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `j)] []))
   " in "
   (Term.app `range [(Cardinal.SetTheory.Cofinality.«term_^_» `p "^" («term_-_» `n "-" `i))])
   ", "
   (Finset.Data.Finset.Fold.«term_*_»
    (Finset.Data.Finset.Fold.«term_*_»
     (Cardinal.SetTheory.Cofinality.«term_^_»
      (Cardinal.SetTheory.Cofinality.«term_^_» (Term.app `X [`i]) "^" `p)
      "^"
      («term_-_»
       (Cardinal.SetTheory.Cofinality.«term_^_» `p "^" («term_-_» `n "-" `i))
       "-"
       (Init.Logic.«term_+_» `j "+" (numLit "1"))))
     "*"
     (Cardinal.SetTheory.Cofinality.«term_^_»
      (Term.app `frobenius_poly_aux [`p `i])
      "^"
      (Init.Logic.«term_+_» `j "+" (numLit "1"))))
    "*"
    (Term.app
     `C
     [(Init.Coe.«term↑_»
       "↑"
       (Term.paren
        "("
        [(Finset.Data.Finset.Fold.«term_*_»
          («term_/_»
           (Term.app
            (Term.proj (Cardinal.SetTheory.Cofinality.«term_^_» `p "^" («term_-_» `n "-" `i)) "." `choose)
            [(Init.Logic.«term_+_» `j "+" (numLit "1"))])
           "/"
           (Cardinal.SetTheory.Cofinality.«term_^_»
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
                [(Init.Logic.«term_+_» `j "+" (numLit "1")) "," (Term.app `Nat.succ_posₓ [`j])]
                "⟩")]))))
          "*"
          (Cardinal.SetTheory.Cofinality.«term_^_»
           (Init.Coe.«term↑_» "↑" `p)
           "^"
           («term_-_»
            `j
            "-"
            (Term.app
             (WittVector.RingTheory.WittVector.Frobenius.termv "v")
             [`p
              (Term.anonymousCtor
               "⟨"
               [(Init.Logic.«term_+_» `j "+" (numLit "1")) "," (Term.app `Nat.succ_posₓ [`j])]
               "⟩")]))))
         [(Term.typeAscription ":" (termℕ "ℕ"))]]
        ")"))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.BigOperators.Basic.«term∑_in_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Finset.Data.Finset.Fold.«term_*_»
   (Finset.Data.Finset.Fold.«term_*_»
    (Cardinal.SetTheory.Cofinality.«term_^_»
     (Cardinal.SetTheory.Cofinality.«term_^_» (Term.app `X [`i]) "^" `p)
     "^"
     («term_-_»
      (Cardinal.SetTheory.Cofinality.«term_^_» `p "^" («term_-_» `n "-" `i))
      "-"
      (Init.Logic.«term_+_» `j "+" (numLit "1"))))
    "*"
    (Cardinal.SetTheory.Cofinality.«term_^_»
     (Term.app `frobenius_poly_aux [`p `i])
     "^"
     (Init.Logic.«term_+_» `j "+" (numLit "1"))))
   "*"
   (Term.app
    `C
    [(Init.Coe.«term↑_»
      "↑"
      (Term.paren
       "("
       [(Finset.Data.Finset.Fold.«term_*_»
         («term_/_»
          (Term.app
           (Term.proj (Cardinal.SetTheory.Cofinality.«term_^_» `p "^" («term_-_» `n "-" `i)) "." `choose)
           [(Init.Logic.«term_+_» `j "+" (numLit "1"))])
          "/"
          (Cardinal.SetTheory.Cofinality.«term_^_»
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
               [(Init.Logic.«term_+_» `j "+" (numLit "1")) "," (Term.app `Nat.succ_posₓ [`j])]
               "⟩")]))))
         "*"
         (Cardinal.SetTheory.Cofinality.«term_^_»
          (Init.Coe.«term↑_» "↑" `p)
          "^"
          («term_-_»
           `j
           "-"
           (Term.app
            (WittVector.RingTheory.WittVector.Frobenius.termv "v")
            [`p
             (Term.anonymousCtor
              "⟨"
              [(Init.Logic.«term_+_» `j "+" (numLit "1")) "," (Term.app `Nat.succ_posₓ [`j])]
              "⟩")]))))
        [(Term.typeAscription ":" (termℕ "ℕ"))]]
       ")"))]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `C
   [(Init.Coe.«term↑_»
     "↑"
     (Term.paren
      "("
      [(Finset.Data.Finset.Fold.«term_*_»
        («term_/_»
         (Term.app
          (Term.proj (Cardinal.SetTheory.Cofinality.«term_^_» `p "^" («term_-_» `n "-" `i)) "." `choose)
          [(Init.Logic.«term_+_» `j "+" (numLit "1"))])
         "/"
         (Cardinal.SetTheory.Cofinality.«term_^_»
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
              [(Init.Logic.«term_+_» `j "+" (numLit "1")) "," (Term.app `Nat.succ_posₓ [`j])]
              "⟩")]))))
        "*"
        (Cardinal.SetTheory.Cofinality.«term_^_»
         (Init.Coe.«term↑_» "↑" `p)
         "^"
         («term_-_»
          `j
          "-"
          (Term.app
           (WittVector.RingTheory.WittVector.Frobenius.termv "v")
           [`p
            (Term.anonymousCtor
             "⟨"
             [(Init.Logic.«term_+_» `j "+" (numLit "1")) "," (Term.app `Nat.succ_posₓ [`j])]
             "⟩")]))))
       [(Term.typeAscription ":" (termℕ "ℕ"))]]
      ")"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Coe.«term↑_»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Coe.«term↑_»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Coe.«term↑_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Coe.«term↑_»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Coe.«term↑_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Coe.«term↑_»
   "↑"
   (Term.paren
    "("
    [(Finset.Data.Finset.Fold.«term_*_»
      («term_/_»
       (Term.app
        (Term.proj (Cardinal.SetTheory.Cofinality.«term_^_» `p "^" («term_-_» `n "-" `i)) "." `choose)
        [(Init.Logic.«term_+_» `j "+" (numLit "1"))])
       "/"
       (Cardinal.SetTheory.Cofinality.«term_^_»
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
            [(Init.Logic.«term_+_» `j "+" (numLit "1")) "," (Term.app `Nat.succ_posₓ [`j])]
            "⟩")]))))
      "*"
      (Cardinal.SetTheory.Cofinality.«term_^_»
       (Init.Coe.«term↑_» "↑" `p)
       "^"
       («term_-_»
        `j
        "-"
        (Term.app
         (WittVector.RingTheory.WittVector.Frobenius.termv "v")
         [`p
          (Term.anonymousCtor
           "⟨"
           [(Init.Logic.«term_+_» `j "+" (numLit "1")) "," (Term.app `Nat.succ_posₓ [`j])]
           "⟩")]))))
     [(Term.typeAscription ":" (termℕ "ℕ"))]]
    ")"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Coe.«term↑_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.paren
   "("
   [(Finset.Data.Finset.Fold.«term_*_»
     («term_/_»
      (Term.app
       (Term.proj (Cardinal.SetTheory.Cofinality.«term_^_» `p "^" («term_-_» `n "-" `i)) "." `choose)
       [(Init.Logic.«term_+_» `j "+" (numLit "1"))])
      "/"
      (Cardinal.SetTheory.Cofinality.«term_^_»
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
           [(Init.Logic.«term_+_» `j "+" (numLit "1")) "," (Term.app `Nat.succ_posₓ [`j])]
           "⟩")]))))
     "*"
     (Cardinal.SetTheory.Cofinality.«term_^_»
      (Init.Coe.«term↑_» "↑" `p)
      "^"
      («term_-_»
       `j
       "-"
       (Term.app
        (WittVector.RingTheory.WittVector.Frobenius.termv "v")
        [`p
         (Term.anonymousCtor
          "⟨"
          [(Init.Logic.«term_+_» `j "+" (numLit "1")) "," (Term.app `Nat.succ_posₓ [`j])]
          "⟩")]))))
    [(Term.typeAscription ":" (termℕ "ℕ"))]]
   ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.paren.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.typeAscription.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (termℕ "ℕ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'termℕ', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  (Finset.Data.Finset.Fold.«term_*_»
   («term_/_»
    (Term.app
     (Term.proj (Cardinal.SetTheory.Cofinality.«term_^_» `p "^" («term_-_» `n "-" `i)) "." `choose)
     [(Init.Logic.«term_+_» `j "+" (numLit "1"))])
    "/"
    (Cardinal.SetTheory.Cofinality.«term_^_»
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
         [(Init.Logic.«term_+_» `j "+" (numLit "1")) "," (Term.app `Nat.succ_posₓ [`j])]
         "⟩")]))))
   "*"
   (Cardinal.SetTheory.Cofinality.«term_^_»
    (Init.Coe.«term↑_» "↑" `p)
    "^"
    («term_-_»
     `j
     "-"
     (Term.app
      (WittVector.RingTheory.WittVector.Frobenius.termv "v")
      [`p
       (Term.anonymousCtor "⟨" [(Init.Logic.«term_+_» `j "+" (numLit "1")) "," (Term.app `Nat.succ_posₓ [`j])] "⟩")]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Cardinal.SetTheory.Cofinality.«term_^_»
   (Init.Coe.«term↑_» "↑" `p)
   "^"
   («term_-_»
    `j
    "-"
    (Term.app
     (WittVector.RingTheory.WittVector.Frobenius.termv "v")
     [`p
      (Term.anonymousCtor "⟨" [(Init.Logic.«term_+_» `j "+" (numLit "1")) "," (Term.app `Nat.succ_posₓ [`j])] "⟩")])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Cardinal.SetTheory.Cofinality.«term_^_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_-_»
   `j
   "-"
   (Term.app
    (WittVector.RingTheory.WittVector.Frobenius.termv "v")
    [`p (Term.anonymousCtor "⟨" [(Init.Logic.«term_+_» `j "+" (numLit "1")) "," (Term.app `Nat.succ_posₓ [`j])] "⟩")]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_-_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   (WittVector.RingTheory.WittVector.Frobenius.termv "v")
   [`p (Term.anonymousCtor "⟨" [(Init.Logic.«term_+_» `j "+" (numLit "1")) "," (Term.app `Nat.succ_posₓ [`j])] "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor "⟨" [(Init.Logic.«term_+_» `j "+" (numLit "1")) "," (Term.app `Nat.succ_posₓ [`j])] "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Nat.succ_posₓ [`j])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `j
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Nat.succ_posₓ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Logic.«term_+_» `j "+" (numLit "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "1")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `j
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  `p
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (WittVector.RingTheory.WittVector.Frobenius.termv "v")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'WittVector.RingTheory.WittVector.Frobenius.termv', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
  `j
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 0, term))
  (Init.Coe.«term↑_» "↑" `p)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Coe.«term↑_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `p
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 999 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1 >? 999, (some 999, term) <=? (some 0, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 0, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  («term_/_»
   (Term.app
    (Term.proj (Cardinal.SetTheory.Cofinality.«term_^_» `p "^" («term_-_» `n "-" `i)) "." `choose)
    [(Init.Logic.«term_+_» `j "+" (numLit "1"))])
   "/"
   (Cardinal.SetTheory.Cofinality.«term_^_»
    `p
    "^"
    («term_-_»
     («term_-_» `n "-" `i)
     "-"
     (Term.app
      (WittVector.RingTheory.WittVector.Frobenius.termv "v")
      [`p
       (Term.anonymousCtor "⟨" [(Init.Logic.«term_+_» `j "+" (numLit "1")) "," (Term.app `Nat.succ_posₓ [`j])] "⟩")]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_/_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Cardinal.SetTheory.Cofinality.«term_^_»
   `p
   "^"
   («term_-_»
    («term_-_» `n "-" `i)
    "-"
    (Term.app
     (WittVector.RingTheory.WittVector.Frobenius.termv "v")
     [`p
      (Term.anonymousCtor "⟨" [(Init.Logic.«term_+_» `j "+" (numLit "1")) "," (Term.app `Nat.succ_posₓ [`j])] "⟩")])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Cardinal.SetTheory.Cofinality.«term_^_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_-_»
   («term_-_» `n "-" `i)
   "-"
   (Term.app
    (WittVector.RingTheory.WittVector.Frobenius.termv "v")
    [`p (Term.anonymousCtor "⟨" [(Init.Logic.«term_+_» `j "+" (numLit "1")) "," (Term.app `Nat.succ_posₓ [`j])] "⟩")]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_-_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   (WittVector.RingTheory.WittVector.Frobenius.termv "v")
   [`p (Term.anonymousCtor "⟨" [(Init.Logic.«term_+_» `j "+" (numLit "1")) "," (Term.app `Nat.succ_posₓ [`j])] "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor "⟨" [(Init.Logic.«term_+_» `j "+" (numLit "1")) "," (Term.app `Nat.succ_posₓ [`j])] "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Nat.succ_posₓ [`j])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `j
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Nat.succ_posₓ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Logic.«term_+_» `j "+" (numLit "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "1")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `j
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  `p
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (WittVector.RingTheory.WittVector.Frobenius.termv "v")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'WittVector.RingTheory.WittVector.Frobenius.termv', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
  («term_-_» `n "-" `i)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_-_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `i
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 65 >? 65, (some 66, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 0, term))
  `p
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1 >? 1024, (none, [anonymous]) <=? (some 0, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 0, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Cardinal.SetTheory.Cofinality.«term_^_»
   `p
   "^"
   («term_-_»
    («term_-_» `n "-" `i)
    "-"
    (Term.app
     (WittVector.RingTheory.WittVector.Frobenius.termv "v")
     [`p
      (Term.anonymousCtor "⟨" [(Init.Logic.«term_+_» `j "+" (numLit "1")) "," (Term.app `Nat.succ_posₓ [`j])] "⟩")])))
  []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
  (Term.app
   (Term.proj (Cardinal.SetTheory.Cofinality.«term_^_» `p "^" («term_-_» `n "-" `i)) "." `choose)
   [(Init.Logic.«term_+_» `j "+" (numLit "1"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Logic.«term_+_» `j "+" (numLit "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "1")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `j
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Init.Logic.«term_+_» `j "+" (numLit "1")) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.proj (Cardinal.SetTheory.Cofinality.«term_^_» `p "^" («term_-_» `n "-" `i)) "." `choose)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Cardinal.SetTheory.Cofinality.«term_^_» `p "^" («term_-_» `n "-" `i))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Cardinal.SetTheory.Cofinality.«term_^_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_-_» `n "-" `i)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_-_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `i
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 0, term))
  `p
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1 >? 1024, (none, [anonymous]) <=? (some 0, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 0, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Cardinal.SetTheory.Cofinality.«term_^_» `p "^" («term_-_» `n "-" `i)) []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1022, (some 1023, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 70, (some 71, term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(«term_/_»
   (Term.app
    (Term.proj
     (Term.paren "(" [(Cardinal.SetTheory.Cofinality.«term_^_» `p "^" («term_-_» `n "-" `i)) []] ")")
     "."
     `choose)
    [(Term.paren "(" [(Init.Logic.«term_+_» `j "+" (numLit "1")) []] ")")])
   "/"
   (Term.paren
    "("
    [(Cardinal.SetTheory.Cofinality.«term_^_»
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
          [(Init.Logic.«term_+_» `j "+" (numLit "1")) "," (Term.app `Nat.succ_posₓ [`j])]
          "⟩")])))
     []]
    ")"))
  []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 999 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 999, (some 999, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Init.Coe.«term↑_»
   "↑"
   (Term.paren
    "("
    [(Finset.Data.Finset.Fold.«term_*_»
      (Term.paren
       "("
       [(«term_/_»
         (Term.app
          (Term.proj
           (Term.paren "(" [(Cardinal.SetTheory.Cofinality.«term_^_» `p "^" («term_-_» `n "-" `i)) []] ")")
           "."
           `choose)
          [(Term.paren "(" [(Init.Logic.«term_+_» `j "+" (numLit "1")) []] ")")])
         "/"
         (Term.paren
          "("
          [(Cardinal.SetTheory.Cofinality.«term_^_»
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
                [(Init.Logic.«term_+_» `j "+" (numLit "1")) "," (Term.app `Nat.succ_posₓ [`j])]
                "⟩")])))
           []]
          ")"))
        []]
       ")")
      "*"
      (Cardinal.SetTheory.Cofinality.«term_^_»
       (Init.Coe.«term↑_» "↑" `p)
       "^"
       («term_-_»
        `j
        "-"
        (Term.app
         (WittVector.RingTheory.WittVector.Frobenius.termv "v")
         [`p
          (Term.anonymousCtor
           "⟨"
           [(Init.Logic.«term_+_» `j "+" (numLit "1")) "," (Term.app `Nat.succ_posₓ [`j])]
           "⟩")]))))
     [(Term.typeAscription ":" (termℕ "ℕ"))]]
    ")"))
  []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `C
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Finset.Data.Finset.Fold.«term_*_»
   (Cardinal.SetTheory.Cofinality.«term_^_»
    (Cardinal.SetTheory.Cofinality.«term_^_» (Term.app `X [`i]) "^" `p)
    "^"
    («term_-_»
     (Cardinal.SetTheory.Cofinality.«term_^_» `p "^" («term_-_» `n "-" `i))
     "-"
     (Init.Logic.«term_+_» `j "+" (numLit "1"))))
   "*"
   (Cardinal.SetTheory.Cofinality.«term_^_»
    (Term.app `frobenius_poly_aux [`p `i])
    "^"
    (Init.Logic.«term_+_» `j "+" (numLit "1"))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Cardinal.SetTheory.Cofinality.«term_^_»
   (Term.app `frobenius_poly_aux [`p `i])
   "^"
   (Init.Logic.«term_+_» `j "+" (numLit "1")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Cardinal.SetTheory.Cofinality.«term_^_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Logic.«term_+_» `j "+" (numLit "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "1")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `j
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 0, term))
  (Term.app `frobenius_poly_aux [`p `i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `i
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `p
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `frobenius_poly_aux
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1 >? 1022, (some 1023, term) <=? (some 0, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 0, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Cardinal.SetTheory.Cofinality.«term_^_»
   (Cardinal.SetTheory.Cofinality.«term_^_» (Term.app `X [`i]) "^" `p)
   "^"
   («term_-_»
    (Cardinal.SetTheory.Cofinality.«term_^_» `p "^" («term_-_» `n "-" `i))
    "-"
    (Init.Logic.«term_+_» `j "+" (numLit "1"))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Cardinal.SetTheory.Cofinality.«term_^_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_-_»
   (Cardinal.SetTheory.Cofinality.«term_^_» `p "^" («term_-_» `n "-" `i))
   "-"
   (Init.Logic.«term_+_» `j "+" (numLit "1")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_-_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Logic.«term_+_» `j "+" (numLit "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "1")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `j
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
  (Cardinal.SetTheory.Cofinality.«term_^_» `p "^" («term_-_» `n "-" `i))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Cardinal.SetTheory.Cofinality.«term_^_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_-_» `n "-" `i)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_-_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `i
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 0, term))
  `p
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1 >? 1024, (none, [anonymous]) <=? (some 0, term)
[PrettyPrinter.parenthesize] ...precedences are 65 >? 0, (some 0, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Cardinal.SetTheory.Cofinality.«term_^_» `p "^" («term_-_» `n "-" `i)) []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 65, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 0, term))
  (Cardinal.SetTheory.Cofinality.«term_^_» (Term.app `X [`i]) "^" `p)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Cardinal.SetTheory.Cofinality.«term_^_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `p
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 0, term))
  (Term.app `X [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `i
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `X
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1 >? 1022, (some 1023, term) <=? (some 0, term)
[PrettyPrinter.parenthesize] ...precedences are 1 >? 0, (some 0, term) <=? (some 0, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Cardinal.SetTheory.Cofinality.«term_^_» (Term.app `X [`i]) "^" `p) []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 0, (some 0, term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Cardinal.SetTheory.Cofinality.«term_^_»
   (Term.paren "(" [(Cardinal.SetTheory.Cofinality.«term_^_» (Term.app `X [`i]) "^" `p) []] ")")
   "^"
   («term_-_»
    (Term.paren "(" [(Cardinal.SetTheory.Cofinality.«term_^_» `p "^" («term_-_» `n "-" `i)) []] ")")
    "-"
    (Init.Logic.«term_+_» `j "+" (numLit "1"))))
  []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Finset.Data.Finset.Fold.«term_*_»
   (Term.paren
    "("
    [(Cardinal.SetTheory.Cofinality.«term_^_»
      (Term.paren "(" [(Cardinal.SetTheory.Cofinality.«term_^_» (Term.app `X [`i]) "^" `p) []] ")")
      "^"
      («term_-_»
       (Term.paren "(" [(Cardinal.SetTheory.Cofinality.«term_^_» `p "^" («term_-_» `n "-" `i)) []] ")")
       "-"
       (Init.Logic.«term_+_» `j "+" (numLit "1"))))
     []]
    ")")
   "*"
   (Cardinal.SetTheory.Cofinality.«term_^_»
    (Term.app `frobenius_poly_aux [`p `i])
    "^"
    (Init.Logic.«term_+_» `j "+" (numLit "1"))))
  []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `range [(Cardinal.SetTheory.Cofinality.«term_^_» `p "^" («term_-_» `n "-" `i))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Cardinal.SetTheory.Cofinality.«term_^_»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Cardinal.SetTheory.Cofinality.«term_^_»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Cardinal.SetTheory.Cofinality.«term_^_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Cardinal.SetTheory.Cofinality.«term_^_»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Cardinal.SetTheory.Cofinality.«term_^_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Cardinal.SetTheory.Cofinality.«term_^_» `p "^" («term_-_» `n "-" `i))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Cardinal.SetTheory.Cofinality.«term_^_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_-_» `n "-" `i)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_-_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `i
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 0, term))
  `p
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1 >? 1024, (none, [anonymous]) <=? (some 0, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 0, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Cardinal.SetTheory.Cofinality.«term_^_» `p "^" («term_-_» `n "-" `i)) []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `range
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.explicitBinders', expected 'Mathlib.ExtendedBinder.extBinders'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.constant.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.constant'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  frobenius_poly_aux_eq
  ( n : ℕ )
    :
      frobenius_poly_aux p n
        =
        X n + 1
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
              X i ^ p ^ p ^ n - i - j + 1 * frobenius_poly_aux p i ^ j + 1
                *
                C
                  ↑
                    (
                      p ^ n - i . choose j + 1 / p ^ n - i - v p ⟨ j + 1 , Nat.succ_posₓ j ⟩
                          *
                          ↑ p ^ j - v p ⟨ j + 1 , Nat.succ_posₓ j ⟩
                        : ℕ
                      )
  := by rw [ frobenius_poly_aux , ← Finₓ.sum_univ_eq_sum_range ]

/--  The polynomials that give the coefficients of `frobenius x`,
in terms of the coefficients of `x`. -/
def frobenius_poly (n : ℕ) : MvPolynomial ℕ ℤ :=
  (X n^p)+C (↑p)*frobenius_poly_aux p n

/--  A key divisibility fact for the proof of `witt_vector.map_frobenius_poly`. -/
theorem map_frobenius_poly.key₁ (n j : ℕ) (hj : j < (p^n)) : (p^n - v p ⟨j+1, j.succ_pos⟩) ∣ (p^n).choose (j+1) := by
  apply multiplicity.pow_dvd_of_le_multiplicity
  have aux : (multiplicity p ((p^n).choose (j+1))).Dom := by
    rw [← multiplicity.finite_iff_dom, multiplicity.finite_nat_iff]
    exact ⟨hp.1.ne_one, Nat.choose_pos hj⟩
  rw [← Enat.coe_get aux, Enat.coe_le_coe, tsub_le_iff_left, ← Enat.coe_le_coe, Nat.cast_add, pnat_multiplicity,
    Enat.coe_get, Enat.coe_get, add_commₓ]
  exact (hp.1.multiplicity_choose_prime_pow hj j.succ_pos).Ge

/--  A key numerical identity needed for the proof of `witt_vector.map_frobenius_poly`. -/
theorem map_frobenius_poly.key₂ {n i j : ℕ} (hi : i < n) (hj : j < (p^n - i)) :
    ((j - v p ⟨j+1, j.succ_pos⟩)+n) = (i+j)+n - i - v p ⟨j+1, j.succ_pos⟩ := by
  generalize h : v p ⟨j+1, j.succ_pos⟩ = m
  suffices m ≤ n - i ∧ m ≤ j by
    rw [tsub_add_eq_add_tsub this.2, add_commₓ i j, add_tsub_assoc_of_le (this.1.trans (Nat.sub_leₓ n i)), add_assocₓ,
      tsub_right_comm, add_commₓ i,
      tsub_add_cancel_of_le (le_tsub_of_add_le_right ((le_tsub_iff_left hi.le).mp this.1))]
  constructor
  ·
    rw [← h, ← Enat.coe_le_coe, pnat_multiplicity, Enat.coe_get, ← hp.1.multiplicity_choose_prime_pow hj j.succ_pos]
    apply le_add_left
    rfl
  ·
    obtain ⟨c, hc⟩ : (p^m) ∣ j+1
    ·
      rw [← h]
      exact multiplicity.pow_multiplicity_dvd _
    obtain ⟨c, rfl⟩ : ∃ k : ℕ, c = k+1
    ·
      apply Nat.exists_eq_succ_of_ne_zero
      rintro rfl
      simpa only using hc
    rw [mul_addₓ, mul_oneₓ] at hc
    apply Nat.le_of_lt_succₓ
    calc m < (p^m) := Nat.lt_pow_self hp.1.one_lt m _ ≤ j+1 := by
      rw [← tsub_eq_of_eq_add_rev hc]
      apply Nat.sub_leₓ

theorem map_frobenius_poly (n : ℕ) :
    MvPolynomial.map (Int.castRingHom ℚ) (frobenius_poly p n) = frobenius_poly_rat p n := by
  rw [frobenius_poly, RingHom.map_add, RingHom.map_mul, RingHom.map_pow, map_C, map_X, RingHom.eq_int_cast,
    Int.cast_coe_nat, frobenius_poly_rat]
  apply Nat.strong_induction_onₓ n
  clear n
  intro n IH
  rw [X_in_terms_of_W_eq]
  simp only [AlgHom.map_sum, AlgHom.map_sub, AlgHom.map_mul, AlgHom.map_pow, bind₁_C_right]
  have h1 : ((↑p^n)*⅟ (↑p : ℚ)^n) = 1 := by
    rw [← mul_powₓ, mul_inv_of_self, one_pow]
  rw [bind₁_X_right, Function.comp_app, witt_polynomial_eq_sum_C_mul_X_pow, sum_range_succ, sum_range_succ, tsub_self,
    add_tsub_cancel_left, pow_zeroₓ, pow_oneₓ, pow_oneₓ, sub_mul, add_mulₓ, add_mulₓ, mul_right_commₓ,
    mul_right_commₓ (C (↑p^n+1)), ← C_mul, ← C_mul, pow_succₓ, mul_assocₓ (↑p) (↑p^n), h1, mul_oneₓ, C_1, one_mulₓ,
    add_commₓ _ (X n^p), add_assocₓ, ← add_sub, add_right_injₓ, frobenius_poly_aux_eq, RingHom.map_sub, map_X, mul_sub,
    sub_eq_add_neg, add_commₓ _ (C (↑p)*X (n+1)), ← add_sub, add_right_injₓ, neg_eq_iff_neg_eq, neg_sub]
  simp only [RingHom.map_sum, mul_sum, sum_mul, ← sum_sub_distrib]
  apply sum_congr rfl
  intro i hi
  rw [mem_range] at hi
  rw [← IH i hi]
  clear IH
  rw [add_commₓ (X i^p), add_pow, sum_range_succ', pow_zeroₓ, tsub_zero, Nat.choose_zero_right, one_mulₓ, Nat.cast_one,
    mul_oneₓ, mul_addₓ, add_mulₓ, Nat.succ_subₓ (le_of_ltₓ hi), Nat.succ_eq_add_one (n - i), pow_succₓ, pow_mulₓ,
    add_sub_cancel, mul_sum, sum_mul]
  apply sum_congr rfl
  intro j hj
  rw [mem_range] at hj
  rw [RingHom.map_mul, RingHom.map_mul, RingHom.map_pow, RingHom.map_pow, RingHom.map_pow, RingHom.map_pow,
    RingHom.map_pow, map_C, map_X, mul_powₓ]
  rw [mul_commₓ (C (↑p)^i), mul_commₓ _ ((X i^p)^_), mul_commₓ (C (↑p)^j+1), mul_commₓ (C (↑p))]
  simp only [mul_assocₓ]
  apply congr_argₓ
  apply congr_argₓ
  rw [← C_eq_coe_nat]
  simp only [← RingHom.map_pow, ← C_mul]
  rw [C_inj]
  simp only [inv_of_eq_inv, RingHom.eq_int_cast, inv_pow₀, Int.cast_coe_nat, Nat.cast_mul]
  rw [Rat.coe_nat_div _ _ (map_frobenius_poly.key₁ p (n - i) j hj)]
  simp only [Nat.cast_pow, pow_addₓ, pow_oneₓ]
  suffices
    ((((p^n - i).choose (j+1)*p^j - v p ⟨j+1, j.succ_pos⟩)*p)*p^n : ℚ) =
      (((p^j)*p)*(p^n - i).choose (j+1)*p^i)*p^n - i - v p ⟨j+1, j.succ_pos⟩by
    have aux : ∀ k : ℕ, (p^k : ℚ) ≠ 0 := by
      intro
      apply pow_ne_zero
      exact_mod_cast hp.1.ne_zero
    simpa [aux, -one_div] with field_simps using this.symm
  rw [mul_commₓ _ (p : ℚ), mul_assocₓ, mul_assocₓ, ← pow_addₓ, map_frobenius_poly.key₂ p hi hj]
  ring_exp

theorem frobenius_poly_zmod (n : ℕ) : MvPolynomial.map (Int.castRingHom (Zmod p)) (frobenius_poly p n) = (X n^p) := by
  rw [frobenius_poly, RingHom.map_add, RingHom.map_pow, RingHom.map_mul, map_X, map_C]
  simp only [Int.cast_coe_nat, add_zeroₓ, RingHom.eq_int_cast, Zmod.nat_cast_self, zero_mul, C_0]

@[simp]
theorem bind₁_frobenius_poly_witt_polynomial (n : ℕ) :
    bind₁ (frobenius_poly p) (wittPolynomial p ℤ n) = wittPolynomial p ℤ (n+1) := by
  apply MvPolynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
  simp only [map_bind₁, map_frobenius_poly, bind₁_frobenius_poly_rat_witt_polynomial, map_witt_polynomial]

variable {p}

/--  `frobenius_fun` is the function underlying the ring endomorphism
`frobenius : 𝕎 R →+* frobenius 𝕎 R`. -/
def frobenius_fun (x : 𝕎 R) : 𝕎 R :=
  mk p $ fun n => MvPolynomial.aeval x.coeff (frobenius_poly p n)

theorem coeff_frobenius_fun (x : 𝕎 R) (n : ℕ) :
    coeff (frobenius_fun x) n = MvPolynomial.aeval x.coeff (frobenius_poly p n) := by
  rw [frobenius_fun, coeff_mk]

variable (p)

/--  `frobenius_fun` is tautologically a polynomial function.

See also `frobenius_is_poly`. -/
@[is_poly]
theorem frobenius_fun_is_poly : is_poly p fun R _Rcr => @frobenius_fun p R _ _Rcr :=
  ⟨⟨frobenius_poly p, by
      intros
      funext n
      apply coeff_frobenius_fun⟩⟩

variable {p}

@[ghost_simps]
theorem ghost_component_frobenius_fun (n : ℕ) (x : 𝕎 R) :
    ghost_component n (frobenius_fun x) = ghost_component (n+1) x := by
  simp only [ghost_component_apply, frobenius_fun, coeff_mk, ← bind₁_frobenius_poly_witt_polynomial, aeval_bind₁]

/-- 
If `R` has characteristic `p`, then there is a ring endomorphism
that raises `r : R` to the power `p`.
By applying `witt_vector.map` to this endomorphism,
we obtain a ring endomorphism `frobenius R p : 𝕎 R →+* 𝕎 R`.

The underlying function of this morphism is `witt_vector.frobenius_fun`.
-/
def frobenius : 𝕎 R →+* 𝕎 R :=
  { toFun := frobenius_fun,
    map_zero' := by
      refine'
        is_poly.ext ((frobenius_fun_is_poly p).comp WittVector.zero_is_poly)
          (WittVector.zero_is_poly.comp (frobenius_fun_is_poly p)) _ _ 0
      ghost_simp,
    map_one' := by
      refine'
        is_poly.ext ((frobenius_fun_is_poly p).comp WittVector.one_is_poly)
          (WittVector.one_is_poly.comp (frobenius_fun_is_poly p)) _ _ 0
      ghost_simp,
    map_add' := by
      ghost_calc _ _ <;> ghost_simp,
    map_mul' := by
      ghost_calc _ _ <;> ghost_simp }

theorem coeff_frobenius (x : 𝕎 R) (n : ℕ) : coeff (frobenius x) n = MvPolynomial.aeval x.coeff (frobenius_poly p n) :=
  coeff_frobenius_fun _ _

@[ghost_simps]
theorem ghost_component_frobenius (n : ℕ) (x : 𝕎 R) : ghost_component n (frobenius x) = ghost_component (n+1) x :=
  ghost_component_frobenius_fun _ _

variable (p)

/--  `frobenius` is tautologically a polynomial function. -/
@[is_poly]
theorem frobenius_is_poly : is_poly p fun R _Rcr => @frobenius p R _ _Rcr :=
  frobenius_fun_is_poly _

section CharP

variable [CharP R p]

@[simp]
theorem coeff_frobenius_char_p (x : 𝕎 R) (n : ℕ) : coeff (frobenius x) n = (x.coeff n^p) := by
  rw [coeff_frobenius]
  calc
    aeval (fun k => x.coeff k) (frobenius_poly p n) =
      aeval (fun k => x.coeff k) (MvPolynomial.map (Int.castRingHom (Zmod p)) (frobenius_poly p n)) :=
    _ _ = aeval (fun k => x.coeff k) (X n^p : MvPolynomial ℕ (Zmod p)) := _ _ = (x.coeff n^p) := _
  ·
    conv_rhs => rw [aeval_eq_eval₂_hom, eval₂_hom_map_hom]
    apply eval₂_hom_congr (RingHom.ext_int _ _) rfl rfl
  ·
    rw [frobenius_poly_zmod]
  ·
    rw [AlgHom.map_pow, aeval_X]

theorem frobenius_eq_map_frobenius : @frobenius p R _ _ = map (_root_.frobenius R p) := by
  ext x n
  simp only [coeff_frobenius_char_p, map_coeff, frobenius_def]

@[simp]
theorem frobenius_zmodp (x : 𝕎 (Zmod p)) : frobenius x = x := by
  simp only [ext_iff, coeff_frobenius_char_p, Zmod.pow_card, eq_self_iff_true, forall_const]

end CharP

end WittVector

