import Mathbin.RingTheory.Polynomial.Chebyshev
import Mathbin.RingTheory.Localization
import Mathbin.Data.Zmod.Basic
import Mathbin.Algebra.CharP.Invertible

/-!
# Dickson polynomials

The (generalised) Dickson polynomials are a family of polynomials indexed by `ℕ × ℕ`,
with coefficients in a commutative ring `R` depending on an element `a∈R`. More precisely, the
they satisfy the recursion `dickson k a (n + 2) = X * (dickson k a n + 1) - a * (dickson k a n)`
with starting values `dickson k a 0 = 3 - k` and `dickson k a 1 = X`. In the literature,
`dickson k a n` is called the `n`-th Dickson polynomial of the `k`-th kind associated to the
parameter `a : R`. They are closely related to the Chebyshev polynomials in the case that `a=1`.
When `a=0` they are just the family of monomials `X ^ n`.

## Main definition

* `polynomial.dickson`: the generalised Dickson polynomials.

## Main statements

* `polynomial.dickson_one_one_mul`, the `(m * n)`-th Dickson polynomial of the first kind for
  parameter `1 : R` is the composition of the `m`-th and `n`-th Dickson polynomials of the first
  kind for `1 : R`.
* `polynomial.dickson_one_one_char_p`, for a prime number `p`, the `p`-th Dickson polynomial of the
  first kind associated to parameter `1 : R` is congruent to `X ^ p` modulo `p`.

## References

* [R. Lidl, G. L. Mullen and G. Turnwald, _Dickson polynomials_][MR1237403]

## TODO

* Redefine `dickson` in terms of `linear_recurrence`.
* Show that `dickson 2 1` is equal to the characteristic polynomial of the adjacency matrix of a
  type A Dynkin diagram.
* Prove that the adjacency matrices of simply laced Dynkin diagrams are precisely the adjacency
  matrices of simple connected graphs which annihilate `dickson 2 1`.
-/


noncomputable section

namespace Polynomial

variable {R S : Type _} [CommRingₓ R] [CommRingₓ S] (k : ℕ) (a : R)

/--  `dickson` is the `n`the (generalised) Dickson polynomial of the `k`-th kind associated to the
element `a ∈ R`. -/
noncomputable def dickson : ℕ → Polynomial R
  | 0 => 3 - k
  | 1 => X
  | n+2 => (X*dickson (n+1)) - C a*dickson n

@[simp]
theorem dickson_zero : dickson k a 0 = 3 - k :=
  rfl

@[simp]
theorem dickson_one : dickson k a 1 = X :=
  rfl

theorem dickson_two : dickson k a 2 = (X^2) - C a*3 - k := by
  simp only [dickson, sq]

@[simp]
theorem dickson_add_two (n : ℕ) : dickson k a (n+2) = (X*dickson k a (n+1)) - C a*dickson k a n := by
  rw [dickson]

theorem dickson_of_two_le {n : ℕ} (h : 2 ≤ n) : dickson k a n = (X*dickson k a (n - 1)) - C a*dickson k a (n - 2) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [add_commₓ]
  exact dickson_add_two k a n

variable {R S k a}

theorem map_dickson (f : R →+* S) : ∀ n : ℕ, map f (dickson k a n) = dickson k (f a) n
  | 0 => by
    simp only [dickson_zero, map_sub, map_nat_cast, bit1, bit0, map_add, map_one]
  | 1 => by
    simp only [dickson_one, map_X]
  | n+2 => by
    simp only [dickson_add_two, map_sub, map_mul, map_X, map_C]
    rw [map_dickson, map_dickson]

variable {R}

@[simp]
theorem dickson_two_zero : ∀ n : ℕ, dickson 2 (0 : R) n = (X^n)
  | 0 => by
    simp only [dickson_zero, pow_zeroₓ]
    norm_num
  | 1 => by
    simp only [dickson_one, pow_oneₓ]
  | n+2 => by
    simp only [dickson_add_two, C_0, zero_mul, sub_zero]
    rw [dickson_two_zero, pow_addₓ X (n+1) 1, mul_commₓ, pow_oneₓ]

section Dickson

/-!

### A Lambda structure on `polynomial ℤ`

Mathlib doesn't currently know what a Lambda ring is.
But once it does, we can endow `polynomial ℤ` with a Lambda structure
in terms of the `dickson 1 1` polynomials defined below.
There is exactly one other Lambda structure on `polynomial ℤ` in terms of binomial polynomials.

-/


variable {R}

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [] [] [] [] [] [])
 (Command.theorem
  "theorem"
  (Command.declId `dickson_one_one_eval_add_inv [])
  (Command.declSig
   [(Term.explicitBinder "(" [`x `y] [":" `R] [] ")")
    (Term.explicitBinder
     "("
     [`h]
     [":" («term_=_» (Finset.Data.Finset.Fold.«term_*_» `x "*" `y) "=" (numLit "1"))]
     []
     ")")]
   (Term.typeSpec
    ":"
    (Term.forall
     "∀"
     [(Term.simpleBinder [`n] [])]
     ","
     («term_=_»
      (Term.app
       (Term.proj
        (Term.app `dickson [(numLit "1") (Term.paren "(" [(numLit "1") [(Term.typeAscription ":" `R)]] ")") `n])
        "."
        `eval)
       [(Init.Logic.«term_+_» `x "+" `y)])
      "="
      (Init.Logic.«term_+_»
       (Cardinal.SetTheory.Cofinality.«term_^_» `x "^" `n)
       "+"
       (Cardinal.SetTheory.Cofinality.«term_^_» `y "^" `n))))))
  (Command.declValEqns
   (Term.matchAltsWhereDecls
    (Term.matchAlts
     [(Term.matchAlt
       "|"
       [(numLit "0")]
       "=>"
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group
            (Tactic.simp
             "simp"
             []
             ["only"]
             ["["
              [(Tactic.simpLemma [] [] `bit0)
               ","
               (Tactic.simpLemma [] [] `eval_one)
               ","
               (Tactic.simpLemma [] [] `eval_add)
               ","
               (Tactic.simpLemma [] [] `pow_zeroₓ)
               ","
               (Tactic.simpLemma [] [] `dickson_zero)]
              "]"]
             [])
            [])
           (group (Lean.Tactic.normNum "norm_num" [] []) [])]))))
      (Term.matchAlt
       "|"
       [(numLit "1")]
       "=>"
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group
            (Tactic.simp
             "simp"
             []
             ["only"]
             ["["
              [(Tactic.simpLemma [] [] `eval_X)
               ","
               (Tactic.simpLemma [] [] `dickson_one)
               ","
               (Tactic.simpLemma [] [] `pow_oneₓ)]
              "]"]
             [])
            [])]))))
      (Term.matchAlt
       "|"
       [(Init.Logic.«term_+_» `n "+" (numLit "2"))]
       "=>"
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group
            (Tactic.simp
             "simp"
             []
             ["only"]
             ["["
              [(Tactic.simpLemma [] [] `eval_sub)
               ","
               (Tactic.simpLemma [] [] `eval_mul)
               ","
               (Tactic.simpLemma [] [] `dickson_one_one_eval_add_inv)
               ","
               (Tactic.simpLemma [] [] `eval_X)
               ","
               (Tactic.simpLemma [] [] `dickson_add_two)
               ","
               (Tactic.simpLemma [] [] `C_1)
               ","
               (Tactic.simpLemma [] [] `eval_one)]
              "]"]
             [])
            [])
           (group
            (Mathlib.Tactic.Conv.convLHS
             "conv_lhs"
             []
             []
             "=>"
             (Tactic.Conv.convSeq
              (Tactic.Conv.convSeq1Indented
               [(group
                 (Tactic.Conv.simp
                  "simp"
                  []
                  ["only"]
                  ["["
                   [(Tactic.simpLemma [] [] `pow_succₓ)
                    ","
                    (Tactic.simpLemma [] [] `add_mulₓ)
                    ","
                    (Tactic.simpLemma [] [] `mul_addₓ)
                    ","
                    (Tactic.simpLemma [] [] `h)
                    ","
                    (Tactic.simpLemma [] ["←"] `mul_assocₓ)
                    ","
                    (Tactic.simpLemma [] [] (Term.app `mul_commₓ [`y `x]))
                    ","
                    (Tactic.simpLemma [] [] `one_mulₓ)]
                   "]"]
                  [])
                 [])])))
            [])
           (group (Tactic.ringExp "ring_exp" []) [])]))))])
    []))
  []
  []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'Lean.Parser.Command.declaration.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.theorem.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValEqns', expected 'Lean.Parser.Command.declValSimple.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValEqns', expected 'Lean.Parser.Command.declValSimple'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValEqns', expected 'Lean.Parser.Command.declValEqns.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.matchAltsWhereDecls', expected 'Lean.Parser.Term.matchAltsWhereDecls.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.matchAlts', expected 'Lean.Parser.Term.matchAlts.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.matchAlt', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.matchAlt', expected 'Lean.Parser.Term.matchAlt.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.simp
        "simp"
        []
        ["only"]
        ["["
         [(Tactic.simpLemma [] [] `eval_sub)
          ","
          (Tactic.simpLemma [] [] `eval_mul)
          ","
          (Tactic.simpLemma [] [] `dickson_one_one_eval_add_inv)
          ","
          (Tactic.simpLemma [] [] `eval_X)
          ","
          (Tactic.simpLemma [] [] `dickson_add_two)
          ","
          (Tactic.simpLemma [] [] `C_1)
          ","
          (Tactic.simpLemma [] [] `eval_one)]
         "]"]
        [])
       [])
      (group
       (Mathlib.Tactic.Conv.convLHS
        "conv_lhs"
        []
        []
        "=>"
        (Tactic.Conv.convSeq
         (Tactic.Conv.convSeq1Indented
          [(group
            (Tactic.Conv.simp
             "simp"
             []
             ["only"]
             ["["
              [(Tactic.simpLemma [] [] `pow_succₓ)
               ","
               (Tactic.simpLemma [] [] `add_mulₓ)
               ","
               (Tactic.simpLemma [] [] `mul_addₓ)
               ","
               (Tactic.simpLemma [] [] `h)
               ","
               (Tactic.simpLemma [] ["←"] `mul_assocₓ)
               ","
               (Tactic.simpLemma [] [] (Term.app `mul_commₓ [`y `x]))
               ","
               (Tactic.simpLemma [] [] `one_mulₓ)]
              "]"]
             [])
            [])])))
       [])
      (group (Tactic.ringExp "ring_exp" []) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.ringExp "ring_exp" [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.ringExp', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Mathlib.Tactic.Conv.convLHS
   "conv_lhs"
   []
   []
   "=>"
   (Tactic.Conv.convSeq
    (Tactic.Conv.convSeq1Indented
     [(group
       (Tactic.Conv.simp
        "simp"
        []
        ["only"]
        ["["
         [(Tactic.simpLemma [] [] `pow_succₓ)
          ","
          (Tactic.simpLemma [] [] `add_mulₓ)
          ","
          (Tactic.simpLemma [] [] `mul_addₓ)
          ","
          (Tactic.simpLemma [] [] `h)
          ","
          (Tactic.simpLemma [] ["←"] `mul_assocₓ)
          ","
          (Tactic.simpLemma [] [] (Term.app `mul_commₓ [`y `x]))
          ","
          (Tactic.simpLemma [] [] `one_mulₓ)]
         "]"]
        [])
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Mathlib.Tactic.Conv.convLHS', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.Conv.simp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'only', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'only', expected 'Lean.Parser.Tactic.discharger'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.Conv.convSeq1Indented', expected 'Lean.Parser.Tactic.Conv.convSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValEqns', expected 'Lean.Parser.Command.whereStructInst.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValEqns', expected 'Lean.Parser.Command.whereStructInst'
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
  dickson_one_one_eval_add_inv
  ( x y : R ) ( h : x * y = 1 ) : ∀ n , dickson 1 ( 1 : R ) n . eval x + y = x ^ n + y ^ n
  | 0 => by simp only [ bit0 , eval_one , eval_add , pow_zeroₓ , dickson_zero ] norm_num
    | 1 => by simp only [ eval_X , dickson_one , pow_oneₓ ]
    |
      n + 2
      =>
      by
        simp only [ eval_sub , eval_mul , dickson_one_one_eval_add_inv , eval_X , dickson_add_two , C_1 , eval_one ]
          conv_lhs => simp only [ pow_succₓ , add_mulₓ , mul_addₓ , h , ← mul_assocₓ , mul_commₓ y x , one_mulₓ ]
          ring_exp

variable (R)

theorem dickson_one_one_eq_chebyshev_T [Invertible (2 : R)] :
    ∀ n, dickson 1 (1 : R) n = 2*(chebyshev.T R n).comp (C (⅟ 2)*X)
  | 0 => by
    simp only [chebyshev.T_zero, mul_oneₓ, one_comp, dickson_zero]
    norm_num
  | 1 => by
    rw [dickson_one, chebyshev.T_one, X_comp, ← mul_assocₓ, ← C_1, ← C_bit0, ← C_mul, mul_inv_of_self, C_1, one_mulₓ]
  | n+2 => by
    simp only [dickson_add_two, chebyshev.T_add_two, dickson_one_one_eq_chebyshev_T (n+1),
      dickson_one_one_eq_chebyshev_T n, sub_comp, mul_comp, add_comp, X_comp, bit0_comp, one_comp]
    simp only [← C_1, ← C_bit0, ← mul_assocₓ, ← C_mul, mul_inv_of_self]
    rw [C_1, one_mulₓ]
    ring

theorem chebyshev_T_eq_dickson_one_one [Invertible (2 : R)] (n : ℕ) :
    chebyshev.T R n = C (⅟ 2)*(dickson 1 1 n).comp (2*X) := by
  rw [dickson_one_one_eq_chebyshev_T]
  simp only [comp_assoc, mul_comp, C_comp, X_comp, ← mul_assocₓ, ← C_1, ← C_bit0, ← C_mul]
  rw [inv_of_mul_self, C_1, one_mulₓ, one_mulₓ, comp_X]

/--  The `(m * n)`-th Dickson polynomial of the first kind is the composition of the `m`-th and
`n`-th. -/
theorem dickson_one_one_mul (m n : ℕ) : dickson 1 (1 : R) (m*n) = (dickson 1 1 m).comp (dickson 1 1 n) := by
  have h : (1 : R) = Int.castRingHom R 1
  simp only [RingHom.eq_int_cast, Int.cast_one]
  rw [h]
  simp only [← map_dickson (Int.castRingHom R), ← map_comp]
  congr 1
  apply map_injective (Int.castRingHom ℚ) Int.cast_injective
  simp only [map_dickson, map_comp, RingHom.eq_int_cast, Int.cast_one, dickson_one_one_eq_chebyshev_T, chebyshev.T_mul,
    two_mul, ← add_comp]
  simp only [← two_mul, ← comp_assoc]
  apply eval₂_congr rfl rfl
  rw [comp_assoc]
  apply eval₂_congr rfl _ rfl
  rw [mul_comp, C_comp, X_comp, ← mul_assocₓ, ← C_1, ← C_bit0, ← C_mul, inv_of_mul_self, C_1, one_mulₓ]

theorem dickson_one_one_comp_comm (m n : ℕ) :
    (dickson 1 (1 : R) m).comp (dickson 1 1 n) = (dickson 1 1 n).comp (dickson 1 1 m) := by
  rw [← dickson_one_one_mul, mul_commₓ, dickson_one_one_mul]

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [] [] [] [] [] [])
 (Command.theorem
  "theorem"
  (Command.declId `dickson_one_one_zmod_p [])
  (Command.declSig
   [(Term.explicitBinder "(" [`p] [":" (termℕ "ℕ")] [] ")") (Term.instBinder "[" [] (Term.app `Fact [`p.prime]) "]")]
   (Term.typeSpec
    ":"
    («term_=_»
     (Term.app
      `dickson
      [(numLit "1") (Term.paren "(" [(numLit "1") [(Term.typeAscription ":" (Term.app `Zmod [`p]))]] ")") `p])
     "="
     (Cardinal.SetTheory.Cofinality.«term_^_» `X "^" `p))))
  (Command.declValSimple
   ":="
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group
        (Tactic.obtain
         "obtain"
         [(Tactic.rcasesPatMed
           [(Tactic.rcasesPat.tuple
             "⟨"
             [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `K)]) [])
              ","
              (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.ignore "_")]) [])
              ","
              (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.ignore "_")]) [])
              ","
              (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `H)]) [])]
             "⟩")])]
         [":"
          («term∃_,_»
           "∃"
           (Lean.explicitBinders
            [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `K)] ":" (Term.type "Type" []) ")")
             (Lean.bracketedExplicitBinders "(" [(Lean.binderIdent "_")] ":" (Term.app `Field [`K]) ")")])
           ","
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(group
                (Tactic.exact
                 "exact"
                 («term∃_,_»
                  "∃"
                  (Lean.explicitBinders
                   (Lean.unbracketedExplicitBinders [(Lean.binderIdent "_")] [":" (Term.app `CharP [`K `p])]))
                  ","
                  (Term.app `Infinite [`K])))
                [])]))))]
         [])
        [])
       (group
        (Tactic.«tactic·._»
         "·"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group
             (Tactic.tacticLet_
              "let"
              (Term.letDecl
               (Term.letIdDecl `K [] ":=" (Term.app `FractionRing [(Term.app `Polynomial [(Term.app `Zmod [`p])])]))))
             [])
            (group
             (Tactic.tacticLet_
              "let"
              (Term.letDecl
               (Term.letIdDecl
                `f
                [(Term.typeSpec ":" (Algebra.Ring.Basic.«term_→+*_» (Term.app `Zmod [`p]) " →+* " `K))]
                ":="
                (Term.app
                 (Term.proj
                  (Term.app `algebraMap [(Term.hole "_") (Term.app `FractionRing [(Term.hole "_")])])
                  "."
                  `comp)
                 [`C]))))
             [])
            (group
             (Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                []
                [(Term.typeSpec ":" (Term.app `CharP [`K `p]))]
                ":="
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(group
                     (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `f.char_p_iff_char_p)] "]") [])
                     [])
                    (group (Tactic.tacticInfer_instance "infer_instance") [])]))))))
             [])
            (group
             (Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                []
                [(Term.typeSpec ":" (Term.app `Infinite [`K]))]
                ":="
                (Term.app
                 `Infinite.of_injective
                 [(Term.app
                   `algebraMap
                   [(Term.app `Polynomial [(Term.app `Zmod [`p])])
                    (Term.app `FractionRing [(Term.app `Polynomial [(Term.app `Zmod [`p])])])])
                  (Term.app `IsFractionRing.injective [(Term.hole "_") (Term.hole "_")])]))))
             [])
            (group
             (Tactic.«tactic_<;>_»
              (Tactic.refine'
               "refine'"
               (Term.anonymousCtor "⟨" [`K "," (Term.hole "_") "," (Term.hole "_") "," (Term.hole "_")] "⟩"))
              "<;>"
              (Tactic.tacticInfer_instance "infer_instance"))
             [])])))
        [])
       (group (Tactic.skip "skip") [])
       (group
        (Tactic.apply
         "apply"
         (Term.app
          `map_injective
          [(Term.app `Zmod.castHom [(Term.app `dvd_refl [`p]) `K]) (Term.app `RingHom.injective [(Term.hole "_")])]))
        [])
       (group
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule [] `map_dickson) "," (Tactic.rwRule [] `Polynomial.map_pow) "," (Tactic.rwRule [] `map_X)]
          "]")
         [])
        [])
       (group (Tactic.apply "apply" `eq_of_infinite_eval_eq) [])
       (group
        (Tactic.apply
         "apply"
         (Term.app
          (Term.explicit "@" `Set.Infinite.mono)
          [(Term.hole "_")
           (Set.«term{_|_}»
            "{"
            (Mathlib.ExtendedBinder.extBinder `x [":" `K])
            "|"
            («term∃_,_»
             "∃"
             (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `y)] []))
             ","
             («term_∧_»
              («term_=_» `x "=" (Init.Logic.«term_+_» `y "+" (Init.Logic.«term_⁻¹» `y "⁻¹")))
              "∧"
              («term_≠_» `y "≠" (numLit "0"))))
            "}")]))
        [])
       (group
        (Tactic.«tactic·._»
         "·"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group
             (Tactic.rintro
              "rintro"
              [(Tactic.rintroPat.one (Tactic.rcasesPat.ignore "_"))
               (Tactic.rintroPat.one
                (Tactic.rcasesPat.tuple
                 "⟨"
                 [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `x)]) [])
                  ","
                  (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `rfl)]) [])
                  ","
                  (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hx)]) [])]
                 "⟩"))]
              [])
             [])
            (group
             (Tactic.simp
              "simp"
              []
              ["only"]
              ["["
               [(Tactic.simpLemma [] [] `eval_X)
                ","
                (Tactic.simpLemma [] [] `eval_pow)
                ","
                (Tactic.simpLemma [] [] `Set.mem_set_of_eq)
                ","
                (Tactic.simpLemma [] [] (Term.app (Term.explicit "@" `add_pow_char) [`K (Term.hole "_") `p]))
                ","
                (Tactic.simpLemma
                 []
                 []
                 (Term.app
                  `dickson_one_one_eval_add_inv
                  [(Term.hole "_") (Term.hole "_") (Term.app `mul_inv_cancel [`hx])]))
                ","
                (Tactic.simpLemma [] [] `inv_pow₀)
                ","
                (Tactic.simpLemma [] [] `Zmod.cast_hom_apply)
                ","
                (Tactic.simpLemma [] [] `Zmod.cast_one')]
               "]"]
              [])
             [])])))
        [])
       (group
        (Tactic.«tactic·._»
         "·"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group (Tactic.intro "intro" [`h]) [])
            (group
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `Set.infinite_univ_iff)] "]")
              [(Tactic.location "at" (Tactic.locationHyp [`H] []))])
             [])
            (group (Tactic.apply "apply" `H) [])
            (group
             (Tactic.tacticSuffices_
              "suffices"
              (Term.sufficesDecl
               []
               («term_=_»
                (Term.paren "(" [`Set.Univ [(Term.typeAscription ":" (Term.app `Set [`K]))]] ")")
                "="
                (Init.Control.Monad.«term_>>=_»
                 (Set.«term{_|_}»
                  "{"
                  (Mathlib.ExtendedBinder.extBinder `x [":" `K])
                  "|"
                  («term∃_,_»
                   "∃"
                   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `y)] [":" `K]))
                   ","
                   («term_∧_»
                    («term_=_» `x "=" (Init.Logic.«term_+_» `y "+" (Init.Logic.«term_⁻¹» `y "⁻¹")))
                    "∧"
                    («term_≠_» `y "≠" (numLit "0"))))
                  "}")
                 " >>= "
                 (Term.fun
                  "fun"
                  (Term.basicFun
                   [(Term.simpleBinder [`x] [])]
                   "=>"
                   (Set.«term{_|_}»
                    "{"
                    `y
                    "|"
                    («term_∨_»
                     («term_=_» `x "=" (Init.Logic.«term_+_» `y "+" (Init.Logic.«term_⁻¹» `y "⁻¹")))
                     "∨"
                     («term_=_» `y "=" (numLit "0")))
                    "}")))))
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `this)] "]") []) [])
                   (group (Tactic.clear "clear" [`this]) [])
                   (group
                    (Tactic.refine'
                     "refine'"
                     (Term.app
                      `h.bUnion
                      [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`x `hx] [])] "=>" (Term.hole "_")))]))
                    [])
                   (group
                    (Tactic.tacticLet_
                     "let"
                     (Term.letDecl
                      (Term.letIdDecl
                       `φ
                       [(Term.typeSpec ":" (Term.app `Polynomial [`K]))]
                       ":="
                       (Init.Logic.«term_+_»
                        («term_-_»
                         (Cardinal.SetTheory.Cofinality.«term_^_» `X "^" (numLit "2"))
                         "-"
                         (Finset.Data.Finset.Fold.«term_*_» (Term.app `C [`x]) "*" `X))
                        "+"
                        (numLit "1")))))
                    [])
                   (group
                    (Tactic.tacticHave_
                     "have"
                     (Term.haveDecl
                      (Term.haveIdDecl
                       [`hφ []]
                       [(Term.typeSpec ":" («term_≠_» `φ "≠" (numLit "0")))]
                       ":="
                       (Term.byTactic
                        "by"
                        (Tactic.tacticSeq
                         (Tactic.tacticSeq1Indented
                          [(group (Tactic.intro "intro" [`H]) [])
                           (group
                            (Tactic.tacticHave_
                             "have"
                             (Term.haveDecl
                              (Term.haveIdDecl
                               []
                               [(Term.typeSpec ":" («term_=_» (Term.app `φ.eval [(numLit "0")]) "=" (numLit "0")))]
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
                                      [(Tactic.rwRule [] `H) "," (Tactic.rwRule [] `eval_zero)]
                                      "]")
                                     [])
                                    [])]))))))
                            [])
                           (group
                            (Tactic.simpa
                             "simpa"
                             []
                             []
                             ["["
                              [(Tactic.simpLemma [] [] `eval_X)
                               ","
                               (Tactic.simpLemma [] [] `eval_one)
                               ","
                               (Tactic.simpLemma [] [] `eval_pow)
                               ","
                               (Tactic.simpLemma [] [] `eval_sub)
                               ","
                               (Tactic.simpLemma [] [] `sub_zero)
                               ","
                               (Tactic.simpLemma [] [] `eval_add)
                               ","
                               (Tactic.simpLemma [] [] `eval_mul)
                               ","
                               (Tactic.simpLemma [] [] `mul_zero)
                               ","
                               (Tactic.simpLemma [] [] `sq)
                               ","
                               (Tactic.simpLemma [] [] `zero_addₓ)
                               ","
                               (Tactic.simpLemma [] [] `one_ne_zero)]
                              "]"]
                             []
                             [])
                            [])]))))))
                    [])
                   (group (Tactic.classical "classical") [])
                   (group
                    (Tactic.convert
                     "convert"
                     []
                     (Term.proj
                      (Term.proj
                       (Init.Core.«term_∪_» `φ.roots " ∪ " (Set.«term{_}» "{" [(numLit "0")] "}"))
                       "."
                       `toFinset)
                      "."
                      `finite_to_set)
                     ["using" (numLit "1")])
                    [])
                   (group (Tactic.ext1 "ext1" [(Tactic.rcasesPat.one `y)]) [])
                   (group
                    (Tactic.simp
                     "simp"
                     []
                     ["only"]
                     ["["
                      [(Tactic.simpLemma [] [] `Multiset.mem_to_finset)
                       ","
                       (Tactic.simpLemma [] [] `Set.mem_set_of_eq)
                       ","
                       (Tactic.simpLemma [] [] `Finset.mem_coe)
                       ","
                       (Tactic.simpLemma [] [] `Multiset.mem_union)
                       ","
                       (Tactic.simpLemma [] [] (Term.app `mem_roots [`hφ]))
                       ","
                       (Tactic.simpLemma [] [] `is_root)
                       ","
                       (Tactic.simpLemma [] [] `eval_add)
                       ","
                       (Tactic.simpLemma [] [] `eval_sub)
                       ","
                       (Tactic.simpLemma [] [] `eval_pow)
                       ","
                       (Tactic.simpLemma [] [] `eval_mul)
                       ","
                       (Tactic.simpLemma [] [] `eval_X)
                       ","
                       (Tactic.simpLemma [] [] `eval_C)
                       ","
                       (Tactic.simpLemma [] [] `eval_one)
                       ","
                       (Tactic.simpLemma [] [] `Multiset.mem_singleton)]
                      "]"]
                     [])
                    [])
                   (group (Tactic.byCases' "by_cases'" [`hy ":"] («term_=_» `y "=" (numLit "0"))) [])
                   (group
                    (Tactic.«tactic·._»
                     "·"
                     (Tactic.tacticSeq
                      (Tactic.tacticSeq1Indented
                       [(group
                         (Tactic.simp
                          "simp"
                          []
                          ["only"]
                          ["["
                           [(Tactic.simpLemma [] [] `hy)
                            ","
                            (Tactic.simpLemma [] [] `eq_self_iff_true)
                            ","
                            (Tactic.simpLemma [] [] `or_trueₓ)]
                           "]"]
                          [])
                         [])])))
                    [])
                   (group (Tactic.apply "apply" (Term.app `or_congr [(Term.hole "_") `Iff.rfl])) [])
                   (group
                    (Tactic.rwSeq
                     "rw"
                     []
                     (Tactic.rwRuleSeq
                      "["
                      [(Tactic.rwRule ["←"] (Term.app `mul_left_inj' [`hy]))
                       ","
                       (Tactic.rwRule [] `eq_comm)
                       ","
                       (Tactic.rwRule ["←"] `sub_eq_zero)
                       ","
                       (Tactic.rwRule [] `add_mulₓ)
                       ","
                       (Tactic.rwRule [] (Term.app `inv_mul_cancel [`hy]))]
                      "]")
                     [])
                    [])
                   (group (Tactic.apply "apply" `eq_iff_eq_cancel_right.mpr) [])
                   (group (Tactic.Ring.tacticRing "ring") [])])))))
             [])
            (group
             (Tactic.«tactic·._»
              "·"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(group
                  (Tactic.apply "apply" (Term.proj (Term.app `Set.eq_univ_of_forall [(Term.hole "_")]) "." `symm))
                  [])
                 (group (Tactic.intro "intro" [`x]) [])
                 (group
                  (Tactic.simp
                   "simp"
                   []
                   ["only"]
                   ["["
                    [(Tactic.simpLemma [] [] `exists_prop)
                     ","
                     (Tactic.simpLemma [] [] `Set.mem_Union)
                     ","
                     (Tactic.simpLemma [] [] `Set.bind_def)
                     ","
                     (Tactic.simpLemma [] [] `Ne.def)
                     ","
                     (Tactic.simpLemma [] [] `Set.mem_set_of_eq)]
                    "]"]
                   [])
                  [])
                 (group (Tactic.byCases' "by_cases'" [`hx ":"] («term_=_» `x "=" (numLit "0"))) [])
                 (group
                  (Tactic.«tactic·._»
                   "·"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented
                     [(group
                       (Tactic.simp
                        "simp"
                        []
                        ["only"]
                        ["["
                         [(Tactic.simpLemma [] [] `hx)
                          ","
                          (Tactic.simpLemma [] [] `and_trueₓ)
                          ","
                          (Tactic.simpLemma [] [] `eq_self_iff_true)
                          ","
                          (Tactic.simpLemma [] [] `inv_zero)
                          ","
                          (Tactic.simpLemma [] [] `or_trueₓ)]
                         "]"]
                        [])
                       [])
                      (group
                       (Tactic.exact
                        "exact"
                        (Term.anonymousCtor "⟨" [(Term.hole "_") "," (numLit "1") "," `rfl "," `one_ne_zero] "⟩"))
                       [])])))
                  [])
                 (group
                  (Tactic.«tactic·._»
                   "·"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented
                     [(group
                       (Tactic.simp
                        "simp"
                        []
                        ["only"]
                        ["["
                         [(Tactic.simpLemma [] [] `hx)
                          ","
                          (Tactic.simpLemma [] [] `or_falseₓ)
                          ","
                          (Tactic.simpLemma [] [] `exists_eq_right)]
                         "]"]
                        [])
                       [])
                      (group
                       (Tactic.exact "exact" (Term.anonymousCtor "⟨" [(Term.hole "_") "," `rfl "," `hx] "⟩"))
                       [])])))
                  [])])))
             [])])))
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
       (Tactic.obtain
        "obtain"
        [(Tactic.rcasesPatMed
          [(Tactic.rcasesPat.tuple
            "⟨"
            [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `K)]) [])
             ","
             (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.ignore "_")]) [])
             ","
             (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.ignore "_")]) [])
             ","
             (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `H)]) [])]
            "⟩")])]
        [":"
         («term∃_,_»
          "∃"
          (Lean.explicitBinders
           [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `K)] ":" (Term.type "Type" []) ")")
            (Lean.bracketedExplicitBinders "(" [(Lean.binderIdent "_")] ":" (Term.app `Field [`K]) ")")])
          ","
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group
               (Tactic.exact
                "exact"
                («term∃_,_»
                 "∃"
                 (Lean.explicitBinders
                  (Lean.unbracketedExplicitBinders [(Lean.binderIdent "_")] [":" (Term.app `CharP [`K `p])]))
                 ","
                 (Term.app `Infinite [`K])))
               [])]))))]
        [])
       [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group
            (Tactic.tacticLet_
             "let"
             (Term.letDecl
              (Term.letIdDecl `K [] ":=" (Term.app `FractionRing [(Term.app `Polynomial [(Term.app `Zmod [`p])])]))))
            [])
           (group
            (Tactic.tacticLet_
             "let"
             (Term.letDecl
              (Term.letIdDecl
               `f
               [(Term.typeSpec ":" (Algebra.Ring.Basic.«term_→+*_» (Term.app `Zmod [`p]) " →+* " `K))]
               ":="
               (Term.app
                (Term.proj
                 (Term.app `algebraMap [(Term.hole "_") (Term.app `FractionRing [(Term.hole "_")])])
                 "."
                 `comp)
                [`C]))))
            [])
           (group
            (Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               []
               [(Term.typeSpec ":" (Term.app `CharP [`K `p]))]
               ":="
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(group
                    (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `f.char_p_iff_char_p)] "]") [])
                    [])
                   (group (Tactic.tacticInfer_instance "infer_instance") [])]))))))
            [])
           (group
            (Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               []
               [(Term.typeSpec ":" (Term.app `Infinite [`K]))]
               ":="
               (Term.app
                `Infinite.of_injective
                [(Term.app
                  `algebraMap
                  [(Term.app `Polynomial [(Term.app `Zmod [`p])])
                   (Term.app `FractionRing [(Term.app `Polynomial [(Term.app `Zmod [`p])])])])
                 (Term.app `IsFractionRing.injective [(Term.hole "_") (Term.hole "_")])]))))
            [])
           (group
            (Tactic.«tactic_<;>_»
             (Tactic.refine'
              "refine'"
              (Term.anonymousCtor "⟨" [`K "," (Term.hole "_") "," (Term.hole "_") "," (Term.hole "_")] "⟩"))
             "<;>"
             (Tactic.tacticInfer_instance "infer_instance"))
            [])])))
       [])
      (group (Tactic.skip "skip") [])
      (group
       (Tactic.apply
        "apply"
        (Term.app
         `map_injective
         [(Term.app `Zmod.castHom [(Term.app `dvd_refl [`p]) `K]) (Term.app `RingHom.injective [(Term.hole "_")])]))
       [])
      (group
       (Tactic.rwSeq
        "rw"
        []
        (Tactic.rwRuleSeq
         "["
         [(Tactic.rwRule [] `map_dickson) "," (Tactic.rwRule [] `Polynomial.map_pow) "," (Tactic.rwRule [] `map_X)]
         "]")
        [])
       [])
      (group (Tactic.apply "apply" `eq_of_infinite_eval_eq) [])
      (group
       (Tactic.apply
        "apply"
        (Term.app
         (Term.explicit "@" `Set.Infinite.mono)
         [(Term.hole "_")
          (Set.«term{_|_}»
           "{"
           (Mathlib.ExtendedBinder.extBinder `x [":" `K])
           "|"
           («term∃_,_»
            "∃"
            (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `y)] []))
            ","
            («term_∧_»
             («term_=_» `x "=" (Init.Logic.«term_+_» `y "+" (Init.Logic.«term_⁻¹» `y "⁻¹")))
             "∧"
             («term_≠_» `y "≠" (numLit "0"))))
           "}")]))
       [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group
            (Tactic.rintro
             "rintro"
             [(Tactic.rintroPat.one (Tactic.rcasesPat.ignore "_"))
              (Tactic.rintroPat.one
               (Tactic.rcasesPat.tuple
                "⟨"
                [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `x)]) [])
                 ","
                 (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `rfl)]) [])
                 ","
                 (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hx)]) [])]
                "⟩"))]
             [])
            [])
           (group
            (Tactic.simp
             "simp"
             []
             ["only"]
             ["["
              [(Tactic.simpLemma [] [] `eval_X)
               ","
               (Tactic.simpLemma [] [] `eval_pow)
               ","
               (Tactic.simpLemma [] [] `Set.mem_set_of_eq)
               ","
               (Tactic.simpLemma [] [] (Term.app (Term.explicit "@" `add_pow_char) [`K (Term.hole "_") `p]))
               ","
               (Tactic.simpLemma
                []
                []
                (Term.app
                 `dickson_one_one_eval_add_inv
                 [(Term.hole "_") (Term.hole "_") (Term.app `mul_inv_cancel [`hx])]))
               ","
               (Tactic.simpLemma [] [] `inv_pow₀)
               ","
               (Tactic.simpLemma [] [] `Zmod.cast_hom_apply)
               ","
               (Tactic.simpLemma [] [] `Zmod.cast_one')]
              "]"]
             [])
            [])])))
       [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group (Tactic.intro "intro" [`h]) [])
           (group
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `Set.infinite_univ_iff)] "]")
             [(Tactic.location "at" (Tactic.locationHyp [`H] []))])
            [])
           (group (Tactic.apply "apply" `H) [])
           (group
            (Tactic.tacticSuffices_
             "suffices"
             (Term.sufficesDecl
              []
              («term_=_»
               (Term.paren "(" [`Set.Univ [(Term.typeAscription ":" (Term.app `Set [`K]))]] ")")
               "="
               (Init.Control.Monad.«term_>>=_»
                (Set.«term{_|_}»
                 "{"
                 (Mathlib.ExtendedBinder.extBinder `x [":" `K])
                 "|"
                 («term∃_,_»
                  "∃"
                  (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `y)] [":" `K]))
                  ","
                  («term_∧_»
                   («term_=_» `x "=" (Init.Logic.«term_+_» `y "+" (Init.Logic.«term_⁻¹» `y "⁻¹")))
                   "∧"
                   («term_≠_» `y "≠" (numLit "0"))))
                 "}")
                " >>= "
                (Term.fun
                 "fun"
                 (Term.basicFun
                  [(Term.simpleBinder [`x] [])]
                  "=>"
                  (Set.«term{_|_}»
                   "{"
                   `y
                   "|"
                   («term_∨_»
                    («term_=_» `x "=" (Init.Logic.«term_+_» `y "+" (Init.Logic.«term_⁻¹» `y "⁻¹")))
                    "∨"
                    («term_=_» `y "=" (numLit "0")))
                   "}")))))
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `this)] "]") []) [])
                  (group (Tactic.clear "clear" [`this]) [])
                  (group
                   (Tactic.refine'
                    "refine'"
                    (Term.app
                     `h.bUnion
                     [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`x `hx] [])] "=>" (Term.hole "_")))]))
                   [])
                  (group
                   (Tactic.tacticLet_
                    "let"
                    (Term.letDecl
                     (Term.letIdDecl
                      `φ
                      [(Term.typeSpec ":" (Term.app `Polynomial [`K]))]
                      ":="
                      (Init.Logic.«term_+_»
                       («term_-_»
                        (Cardinal.SetTheory.Cofinality.«term_^_» `X "^" (numLit "2"))
                        "-"
                        (Finset.Data.Finset.Fold.«term_*_» (Term.app `C [`x]) "*" `X))
                       "+"
                       (numLit "1")))))
                   [])
                  (group
                   (Tactic.tacticHave_
                    "have"
                    (Term.haveDecl
                     (Term.haveIdDecl
                      [`hφ []]
                      [(Term.typeSpec ":" («term_≠_» `φ "≠" (numLit "0")))]
                      ":="
                      (Term.byTactic
                       "by"
                       (Tactic.tacticSeq
                        (Tactic.tacticSeq1Indented
                         [(group (Tactic.intro "intro" [`H]) [])
                          (group
                           (Tactic.tacticHave_
                            "have"
                            (Term.haveDecl
                             (Term.haveIdDecl
                              []
                              [(Term.typeSpec ":" («term_=_» (Term.app `φ.eval [(numLit "0")]) "=" (numLit "0")))]
                              ":="
                              (Term.byTactic
                               "by"
                               (Tactic.tacticSeq
                                (Tactic.tacticSeq1Indented
                                 [(group
                                   (Tactic.rwSeq
                                    "rw"
                                    []
                                    (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `H) "," (Tactic.rwRule [] `eval_zero)] "]")
                                    [])
                                   [])]))))))
                           [])
                          (group
                           (Tactic.simpa
                            "simpa"
                            []
                            []
                            ["["
                             [(Tactic.simpLemma [] [] `eval_X)
                              ","
                              (Tactic.simpLemma [] [] `eval_one)
                              ","
                              (Tactic.simpLemma [] [] `eval_pow)
                              ","
                              (Tactic.simpLemma [] [] `eval_sub)
                              ","
                              (Tactic.simpLemma [] [] `sub_zero)
                              ","
                              (Tactic.simpLemma [] [] `eval_add)
                              ","
                              (Tactic.simpLemma [] [] `eval_mul)
                              ","
                              (Tactic.simpLemma [] [] `mul_zero)
                              ","
                              (Tactic.simpLemma [] [] `sq)
                              ","
                              (Tactic.simpLemma [] [] `zero_addₓ)
                              ","
                              (Tactic.simpLemma [] [] `one_ne_zero)]
                             "]"]
                            []
                            [])
                           [])]))))))
                   [])
                  (group (Tactic.classical "classical") [])
                  (group
                   (Tactic.convert
                    "convert"
                    []
                    (Term.proj
                     (Term.proj
                      (Init.Core.«term_∪_» `φ.roots " ∪ " (Set.«term{_}» "{" [(numLit "0")] "}"))
                      "."
                      `toFinset)
                     "."
                     `finite_to_set)
                    ["using" (numLit "1")])
                   [])
                  (group (Tactic.ext1 "ext1" [(Tactic.rcasesPat.one `y)]) [])
                  (group
                   (Tactic.simp
                    "simp"
                    []
                    ["only"]
                    ["["
                     [(Tactic.simpLemma [] [] `Multiset.mem_to_finset)
                      ","
                      (Tactic.simpLemma [] [] `Set.mem_set_of_eq)
                      ","
                      (Tactic.simpLemma [] [] `Finset.mem_coe)
                      ","
                      (Tactic.simpLemma [] [] `Multiset.mem_union)
                      ","
                      (Tactic.simpLemma [] [] (Term.app `mem_roots [`hφ]))
                      ","
                      (Tactic.simpLemma [] [] `is_root)
                      ","
                      (Tactic.simpLemma [] [] `eval_add)
                      ","
                      (Tactic.simpLemma [] [] `eval_sub)
                      ","
                      (Tactic.simpLemma [] [] `eval_pow)
                      ","
                      (Tactic.simpLemma [] [] `eval_mul)
                      ","
                      (Tactic.simpLemma [] [] `eval_X)
                      ","
                      (Tactic.simpLemma [] [] `eval_C)
                      ","
                      (Tactic.simpLemma [] [] `eval_one)
                      ","
                      (Tactic.simpLemma [] [] `Multiset.mem_singleton)]
                     "]"]
                    [])
                   [])
                  (group (Tactic.byCases' "by_cases'" [`hy ":"] («term_=_» `y "=" (numLit "0"))) [])
                  (group
                   (Tactic.«tactic·._»
                    "·"
                    (Tactic.tacticSeq
                     (Tactic.tacticSeq1Indented
                      [(group
                        (Tactic.simp
                         "simp"
                         []
                         ["only"]
                         ["["
                          [(Tactic.simpLemma [] [] `hy)
                           ","
                           (Tactic.simpLemma [] [] `eq_self_iff_true)
                           ","
                           (Tactic.simpLemma [] [] `or_trueₓ)]
                          "]"]
                         [])
                        [])])))
                   [])
                  (group (Tactic.apply "apply" (Term.app `or_congr [(Term.hole "_") `Iff.rfl])) [])
                  (group
                   (Tactic.rwSeq
                    "rw"
                    []
                    (Tactic.rwRuleSeq
                     "["
                     [(Tactic.rwRule ["←"] (Term.app `mul_left_inj' [`hy]))
                      ","
                      (Tactic.rwRule [] `eq_comm)
                      ","
                      (Tactic.rwRule ["←"] `sub_eq_zero)
                      ","
                      (Tactic.rwRule [] `add_mulₓ)
                      ","
                      (Tactic.rwRule [] (Term.app `inv_mul_cancel [`hy]))]
                     "]")
                    [])
                   [])
                  (group (Tactic.apply "apply" `eq_iff_eq_cancel_right.mpr) [])
                  (group (Tactic.Ring.tacticRing "ring") [])])))))
            [])
           (group
            (Tactic.«tactic·._»
             "·"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(group
                 (Tactic.apply "apply" (Term.proj (Term.app `Set.eq_univ_of_forall [(Term.hole "_")]) "." `symm))
                 [])
                (group (Tactic.intro "intro" [`x]) [])
                (group
                 (Tactic.simp
                  "simp"
                  []
                  ["only"]
                  ["["
                   [(Tactic.simpLemma [] [] `exists_prop)
                    ","
                    (Tactic.simpLemma [] [] `Set.mem_Union)
                    ","
                    (Tactic.simpLemma [] [] `Set.bind_def)
                    ","
                    (Tactic.simpLemma [] [] `Ne.def)
                    ","
                    (Tactic.simpLemma [] [] `Set.mem_set_of_eq)]
                   "]"]
                  [])
                 [])
                (group (Tactic.byCases' "by_cases'" [`hx ":"] («term_=_» `x "=" (numLit "0"))) [])
                (group
                 (Tactic.«tactic·._»
                  "·"
                  (Tactic.tacticSeq
                   (Tactic.tacticSeq1Indented
                    [(group
                      (Tactic.simp
                       "simp"
                       []
                       ["only"]
                       ["["
                        [(Tactic.simpLemma [] [] `hx)
                         ","
                         (Tactic.simpLemma [] [] `and_trueₓ)
                         ","
                         (Tactic.simpLemma [] [] `eq_self_iff_true)
                         ","
                         (Tactic.simpLemma [] [] `inv_zero)
                         ","
                         (Tactic.simpLemma [] [] `or_trueₓ)]
                        "]"]
                       [])
                      [])
                     (group
                      (Tactic.exact
                       "exact"
                       (Term.anonymousCtor "⟨" [(Term.hole "_") "," (numLit "1") "," `rfl "," `one_ne_zero] "⟩"))
                      [])])))
                 [])
                (group
                 (Tactic.«tactic·._»
                  "·"
                  (Tactic.tacticSeq
                   (Tactic.tacticSeq1Indented
                    [(group
                      (Tactic.simp
                       "simp"
                       []
                       ["only"]
                       ["["
                        [(Tactic.simpLemma [] [] `hx)
                         ","
                         (Tactic.simpLemma [] [] `or_falseₓ)
                         ","
                         (Tactic.simpLemma [] [] `exists_eq_right)]
                        "]"]
                       [])
                      [])
                     (group
                      (Tactic.exact "exact" (Term.anonymousCtor "⟨" [(Term.hole "_") "," `rfl "," `hx] "⟩"))
                      [])])))
                 [])])))
            [])])))
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.«tactic·._»
   "·"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group (Tactic.intro "intro" [`h]) [])
      (group
       (Tactic.rwSeq
        "rw"
        []
        (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `Set.infinite_univ_iff)] "]")
        [(Tactic.location "at" (Tactic.locationHyp [`H] []))])
       [])
      (group (Tactic.apply "apply" `H) [])
      (group
       (Tactic.tacticSuffices_
        "suffices"
        (Term.sufficesDecl
         []
         («term_=_»
          (Term.paren "(" [`Set.Univ [(Term.typeAscription ":" (Term.app `Set [`K]))]] ")")
          "="
          (Init.Control.Monad.«term_>>=_»
           (Set.«term{_|_}»
            "{"
            (Mathlib.ExtendedBinder.extBinder `x [":" `K])
            "|"
            («term∃_,_»
             "∃"
             (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `y)] [":" `K]))
             ","
             («term_∧_»
              («term_=_» `x "=" (Init.Logic.«term_+_» `y "+" (Init.Logic.«term_⁻¹» `y "⁻¹")))
              "∧"
              («term_≠_» `y "≠" (numLit "0"))))
            "}")
           " >>= "
           (Term.fun
            "fun"
            (Term.basicFun
             [(Term.simpleBinder [`x] [])]
             "=>"
             (Set.«term{_|_}»
              "{"
              `y
              "|"
              («term_∨_»
               («term_=_» `x "=" (Init.Logic.«term_+_» `y "+" (Init.Logic.«term_⁻¹» `y "⁻¹")))
               "∨"
               («term_=_» `y "=" (numLit "0")))
              "}")))))
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `this)] "]") []) [])
             (group (Tactic.clear "clear" [`this]) [])
             (group
              (Tactic.refine'
               "refine'"
               (Term.app
                `h.bUnion
                [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`x `hx] [])] "=>" (Term.hole "_")))]))
              [])
             (group
              (Tactic.tacticLet_
               "let"
               (Term.letDecl
                (Term.letIdDecl
                 `φ
                 [(Term.typeSpec ":" (Term.app `Polynomial [`K]))]
                 ":="
                 (Init.Logic.«term_+_»
                  («term_-_»
                   (Cardinal.SetTheory.Cofinality.«term_^_» `X "^" (numLit "2"))
                   "-"
                   (Finset.Data.Finset.Fold.«term_*_» (Term.app `C [`x]) "*" `X))
                  "+"
                  (numLit "1")))))
              [])
             (group
              (Tactic.tacticHave_
               "have"
               (Term.haveDecl
                (Term.haveIdDecl
                 [`hφ []]
                 [(Term.typeSpec ":" («term_≠_» `φ "≠" (numLit "0")))]
                 ":="
                 (Term.byTactic
                  "by"
                  (Tactic.tacticSeq
                   (Tactic.tacticSeq1Indented
                    [(group (Tactic.intro "intro" [`H]) [])
                     (group
                      (Tactic.tacticHave_
                       "have"
                       (Term.haveDecl
                        (Term.haveIdDecl
                         []
                         [(Term.typeSpec ":" («term_=_» (Term.app `φ.eval [(numLit "0")]) "=" (numLit "0")))]
                         ":="
                         (Term.byTactic
                          "by"
                          (Tactic.tacticSeq
                           (Tactic.tacticSeq1Indented
                            [(group
                              (Tactic.rwSeq
                               "rw"
                               []
                               (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `H) "," (Tactic.rwRule [] `eval_zero)] "]")
                               [])
                              [])]))))))
                      [])
                     (group
                      (Tactic.simpa
                       "simpa"
                       []
                       []
                       ["["
                        [(Tactic.simpLemma [] [] `eval_X)
                         ","
                         (Tactic.simpLemma [] [] `eval_one)
                         ","
                         (Tactic.simpLemma [] [] `eval_pow)
                         ","
                         (Tactic.simpLemma [] [] `eval_sub)
                         ","
                         (Tactic.simpLemma [] [] `sub_zero)
                         ","
                         (Tactic.simpLemma [] [] `eval_add)
                         ","
                         (Tactic.simpLemma [] [] `eval_mul)
                         ","
                         (Tactic.simpLemma [] [] `mul_zero)
                         ","
                         (Tactic.simpLemma [] [] `sq)
                         ","
                         (Tactic.simpLemma [] [] `zero_addₓ)
                         ","
                         (Tactic.simpLemma [] [] `one_ne_zero)]
                        "]"]
                       []
                       [])
                      [])]))))))
              [])
             (group (Tactic.classical "classical") [])
             (group
              (Tactic.convert
               "convert"
               []
               (Term.proj
                (Term.proj (Init.Core.«term_∪_» `φ.roots " ∪ " (Set.«term{_}» "{" [(numLit "0")] "}")) "." `toFinset)
                "."
                `finite_to_set)
               ["using" (numLit "1")])
              [])
             (group (Tactic.ext1 "ext1" [(Tactic.rcasesPat.one `y)]) [])
             (group
              (Tactic.simp
               "simp"
               []
               ["only"]
               ["["
                [(Tactic.simpLemma [] [] `Multiset.mem_to_finset)
                 ","
                 (Tactic.simpLemma [] [] `Set.mem_set_of_eq)
                 ","
                 (Tactic.simpLemma [] [] `Finset.mem_coe)
                 ","
                 (Tactic.simpLemma [] [] `Multiset.mem_union)
                 ","
                 (Tactic.simpLemma [] [] (Term.app `mem_roots [`hφ]))
                 ","
                 (Tactic.simpLemma [] [] `is_root)
                 ","
                 (Tactic.simpLemma [] [] `eval_add)
                 ","
                 (Tactic.simpLemma [] [] `eval_sub)
                 ","
                 (Tactic.simpLemma [] [] `eval_pow)
                 ","
                 (Tactic.simpLemma [] [] `eval_mul)
                 ","
                 (Tactic.simpLemma [] [] `eval_X)
                 ","
                 (Tactic.simpLemma [] [] `eval_C)
                 ","
                 (Tactic.simpLemma [] [] `eval_one)
                 ","
                 (Tactic.simpLemma [] [] `Multiset.mem_singleton)]
                "]"]
               [])
              [])
             (group (Tactic.byCases' "by_cases'" [`hy ":"] («term_=_» `y "=" (numLit "0"))) [])
             (group
              (Tactic.«tactic·._»
               "·"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(group
                   (Tactic.simp
                    "simp"
                    []
                    ["only"]
                    ["["
                     [(Tactic.simpLemma [] [] `hy)
                      ","
                      (Tactic.simpLemma [] [] `eq_self_iff_true)
                      ","
                      (Tactic.simpLemma [] [] `or_trueₓ)]
                     "]"]
                    [])
                   [])])))
              [])
             (group (Tactic.apply "apply" (Term.app `or_congr [(Term.hole "_") `Iff.rfl])) [])
             (group
              (Tactic.rwSeq
               "rw"
               []
               (Tactic.rwRuleSeq
                "["
                [(Tactic.rwRule ["←"] (Term.app `mul_left_inj' [`hy]))
                 ","
                 (Tactic.rwRule [] `eq_comm)
                 ","
                 (Tactic.rwRule ["←"] `sub_eq_zero)
                 ","
                 (Tactic.rwRule [] `add_mulₓ)
                 ","
                 (Tactic.rwRule [] (Term.app `inv_mul_cancel [`hy]))]
                "]")
               [])
              [])
             (group (Tactic.apply "apply" `eq_iff_eq_cancel_right.mpr) [])
             (group (Tactic.Ring.tacticRing "ring") [])])))))
       [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group (Tactic.apply "apply" (Term.proj (Term.app `Set.eq_univ_of_forall [(Term.hole "_")]) "." `symm)) [])
           (group (Tactic.intro "intro" [`x]) [])
           (group
            (Tactic.simp
             "simp"
             []
             ["only"]
             ["["
              [(Tactic.simpLemma [] [] `exists_prop)
               ","
               (Tactic.simpLemma [] [] `Set.mem_Union)
               ","
               (Tactic.simpLemma [] [] `Set.bind_def)
               ","
               (Tactic.simpLemma [] [] `Ne.def)
               ","
               (Tactic.simpLemma [] [] `Set.mem_set_of_eq)]
              "]"]
             [])
            [])
           (group (Tactic.byCases' "by_cases'" [`hx ":"] («term_=_» `x "=" (numLit "0"))) [])
           (group
            (Tactic.«tactic·._»
             "·"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(group
                 (Tactic.simp
                  "simp"
                  []
                  ["only"]
                  ["["
                   [(Tactic.simpLemma [] [] `hx)
                    ","
                    (Tactic.simpLemma [] [] `and_trueₓ)
                    ","
                    (Tactic.simpLemma [] [] `eq_self_iff_true)
                    ","
                    (Tactic.simpLemma [] [] `inv_zero)
                    ","
                    (Tactic.simpLemma [] [] `or_trueₓ)]
                   "]"]
                  [])
                 [])
                (group
                 (Tactic.exact
                  "exact"
                  (Term.anonymousCtor "⟨" [(Term.hole "_") "," (numLit "1") "," `rfl "," `one_ne_zero] "⟩"))
                 [])])))
            [])
           (group
            (Tactic.«tactic·._»
             "·"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(group
                 (Tactic.simp
                  "simp"
                  []
                  ["only"]
                  ["["
                   [(Tactic.simpLemma [] [] `hx)
                    ","
                    (Tactic.simpLemma [] [] `or_falseₓ)
                    ","
                    (Tactic.simpLemma [] [] `exists_eq_right)]
                   "]"]
                  [])
                 [])
                (group (Tactic.exact "exact" (Term.anonymousCtor "⟨" [(Term.hole "_") "," `rfl "," `hx] "⟩")) [])])))
            [])])))
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.«tactic·._»', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.«tactic·._»
   "·"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group (Tactic.apply "apply" (Term.proj (Term.app `Set.eq_univ_of_forall [(Term.hole "_")]) "." `symm)) [])
      (group (Tactic.intro "intro" [`x]) [])
      (group
       (Tactic.simp
        "simp"
        []
        ["only"]
        ["["
         [(Tactic.simpLemma [] [] `exists_prop)
          ","
          (Tactic.simpLemma [] [] `Set.mem_Union)
          ","
          (Tactic.simpLemma [] [] `Set.bind_def)
          ","
          (Tactic.simpLemma [] [] `Ne.def)
          ","
          (Tactic.simpLemma [] [] `Set.mem_set_of_eq)]
         "]"]
        [])
       [])
      (group (Tactic.byCases' "by_cases'" [`hx ":"] («term_=_» `x "=" (numLit "0"))) [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group
            (Tactic.simp
             "simp"
             []
             ["only"]
             ["["
              [(Tactic.simpLemma [] [] `hx)
               ","
               (Tactic.simpLemma [] [] `and_trueₓ)
               ","
               (Tactic.simpLemma [] [] `eq_self_iff_true)
               ","
               (Tactic.simpLemma [] [] `inv_zero)
               ","
               (Tactic.simpLemma [] [] `or_trueₓ)]
              "]"]
             [])
            [])
           (group
            (Tactic.exact
             "exact"
             (Term.anonymousCtor "⟨" [(Term.hole "_") "," (numLit "1") "," `rfl "," `one_ne_zero] "⟩"))
            [])])))
       [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group
            (Tactic.simp
             "simp"
             []
             ["only"]
             ["["
              [(Tactic.simpLemma [] [] `hx)
               ","
               (Tactic.simpLemma [] [] `or_falseₓ)
               ","
               (Tactic.simpLemma [] [] `exists_eq_right)]
              "]"]
             [])
            [])
           (group (Tactic.exact "exact" (Term.anonymousCtor "⟨" [(Term.hole "_") "," `rfl "," `hx] "⟩")) [])])))
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.«tactic·._»', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.«tactic·._»
   "·"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.simp
        "simp"
        []
        ["only"]
        ["["
         [(Tactic.simpLemma [] [] `hx)
          ","
          (Tactic.simpLemma [] [] `or_falseₓ)
          ","
          (Tactic.simpLemma [] [] `exists_eq_right)]
         "]"]
        [])
       [])
      (group (Tactic.exact "exact" (Term.anonymousCtor "⟨" [(Term.hole "_") "," `rfl "," `hx] "⟩")) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.«tactic·._»', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.exact "exact" (Term.anonymousCtor "⟨" [(Term.hole "_") "," `rfl "," `hx] "⟩"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.exact', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor "⟨" [(Term.hole "_") "," `rfl "," `hx] "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hx
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `rfl
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.simp
   "simp"
   []
   ["only"]
   ["["
    [(Tactic.simpLemma [] [] `hx) "," (Tactic.simpLemma [] [] `or_falseₓ) "," (Tactic.simpLemma [] [] `exists_eq_right)]
    "]"]
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `exists_eq_right
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `or_falseₓ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hx
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'only', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.«tactic·._»
   "·"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.simp
        "simp"
        []
        ["only"]
        ["["
         [(Tactic.simpLemma [] [] `hx)
          ","
          (Tactic.simpLemma [] [] `and_trueₓ)
          ","
          (Tactic.simpLemma [] [] `eq_self_iff_true)
          ","
          (Tactic.simpLemma [] [] `inv_zero)
          ","
          (Tactic.simpLemma [] [] `or_trueₓ)]
         "]"]
        [])
       [])
      (group
       (Tactic.exact "exact" (Term.anonymousCtor "⟨" [(Term.hole "_") "," (numLit "1") "," `rfl "," `one_ne_zero] "⟩"))
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.«tactic·._»', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.exact "exact" (Term.anonymousCtor "⟨" [(Term.hole "_") "," (numLit "1") "," `rfl "," `one_ne_zero] "⟩"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.exact', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor "⟨" [(Term.hole "_") "," (numLit "1") "," `rfl "," `one_ne_zero] "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `one_ne_zero
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `rfl
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "1")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.simp
   "simp"
   []
   ["only"]
   ["["
    [(Tactic.simpLemma [] [] `hx)
     ","
     (Tactic.simpLemma [] [] `and_trueₓ)
     ","
     (Tactic.simpLemma [] [] `eq_self_iff_true)
     ","
     (Tactic.simpLemma [] [] `inv_zero)
     ","
     (Tactic.simpLemma [] [] `or_trueₓ)]
    "]"]
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `or_trueₓ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `inv_zero
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `eq_self_iff_true
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `and_trueₓ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hx
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'only', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.byCases' "by_cases'" [`hx ":"] («term_=_» `x "=" (numLit "0")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.byCases'', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_=_» `x "=" (numLit "0"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "0")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  `x
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«:»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.simp
   "simp"
   []
   ["only"]
   ["["
    [(Tactic.simpLemma [] [] `exists_prop)
     ","
     (Tactic.simpLemma [] [] `Set.mem_Union)
     ","
     (Tactic.simpLemma [] [] `Set.bind_def)
     ","
     (Tactic.simpLemma [] [] `Ne.def)
     ","
     (Tactic.simpLemma [] [] `Set.mem_set_of_eq)]
    "]"]
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Set.mem_set_of_eq
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Ne.def
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Set.bind_def
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Set.mem_Union
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `exists_prop
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'only', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.intro "intro" [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.intro', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `x
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.apply "apply" (Term.proj (Term.app `Set.eq_univ_of_forall [(Term.hole "_")]) "." `symm))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.apply', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.proj (Term.app `Set.eq_univ_of_forall [(Term.hole "_")]) "." `symm)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `Set.eq_univ_of_forall [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Set.eq_univ_of_forall
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app `Set.eq_univ_of_forall [(Term.hole "_")]) []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.tacticSuffices_
   "suffices"
   (Term.sufficesDecl
    []
    («term_=_»
     (Term.paren "(" [`Set.Univ [(Term.typeAscription ":" (Term.app `Set [`K]))]] ")")
     "="
     (Init.Control.Monad.«term_>>=_»
      (Set.«term{_|_}»
       "{"
       (Mathlib.ExtendedBinder.extBinder `x [":" `K])
       "|"
       («term∃_,_»
        "∃"
        (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `y)] [":" `K]))
        ","
        («term_∧_»
         («term_=_» `x "=" (Init.Logic.«term_+_» `y "+" (Init.Logic.«term_⁻¹» `y "⁻¹")))
         "∧"
         («term_≠_» `y "≠" (numLit "0"))))
       "}")
      " >>= "
      (Term.fun
       "fun"
       (Term.basicFun
        [(Term.simpleBinder [`x] [])]
        "=>"
        (Set.«term{_|_}»
         "{"
         `y
         "|"
         («term_∨_»
          («term_=_» `x "=" (Init.Logic.«term_+_» `y "+" (Init.Logic.«term_⁻¹» `y "⁻¹")))
          "∨"
          («term_=_» `y "=" (numLit "0")))
         "}")))))
    (Term.byTactic
     "by"
     (Tactic.tacticSeq
      (Tactic.tacticSeq1Indented
       [(group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `this)] "]") []) [])
        (group (Tactic.clear "clear" [`this]) [])
        (group
         (Tactic.refine'
          "refine'"
          (Term.app
           `h.bUnion
           [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`x `hx] [])] "=>" (Term.hole "_")))]))
         [])
        (group
         (Tactic.tacticLet_
          "let"
          (Term.letDecl
           (Term.letIdDecl
            `φ
            [(Term.typeSpec ":" (Term.app `Polynomial [`K]))]
            ":="
            (Init.Logic.«term_+_»
             («term_-_»
              (Cardinal.SetTheory.Cofinality.«term_^_» `X "^" (numLit "2"))
              "-"
              (Finset.Data.Finset.Fold.«term_*_» (Term.app `C [`x]) "*" `X))
             "+"
             (numLit "1")))))
         [])
        (group
         (Tactic.tacticHave_
          "have"
          (Term.haveDecl
           (Term.haveIdDecl
            [`hφ []]
            [(Term.typeSpec ":" («term_≠_» `φ "≠" (numLit "0")))]
            ":="
            (Term.byTactic
             "by"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(group (Tactic.intro "intro" [`H]) [])
                (group
                 (Tactic.tacticHave_
                  "have"
                  (Term.haveDecl
                   (Term.haveIdDecl
                    []
                    [(Term.typeSpec ":" («term_=_» (Term.app `φ.eval [(numLit "0")]) "=" (numLit "0")))]
                    ":="
                    (Term.byTactic
                     "by"
                     (Tactic.tacticSeq
                      (Tactic.tacticSeq1Indented
                       [(group
                         (Tactic.rwSeq
                          "rw"
                          []
                          (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `H) "," (Tactic.rwRule [] `eval_zero)] "]")
                          [])
                         [])]))))))
                 [])
                (group
                 (Tactic.simpa
                  "simpa"
                  []
                  []
                  ["["
                   [(Tactic.simpLemma [] [] `eval_X)
                    ","
                    (Tactic.simpLemma [] [] `eval_one)
                    ","
                    (Tactic.simpLemma [] [] `eval_pow)
                    ","
                    (Tactic.simpLemma [] [] `eval_sub)
                    ","
                    (Tactic.simpLemma [] [] `sub_zero)
                    ","
                    (Tactic.simpLemma [] [] `eval_add)
                    ","
                    (Tactic.simpLemma [] [] `eval_mul)
                    ","
                    (Tactic.simpLemma [] [] `mul_zero)
                    ","
                    (Tactic.simpLemma [] [] `sq)
                    ","
                    (Tactic.simpLemma [] [] `zero_addₓ)
                    ","
                    (Tactic.simpLemma [] [] `one_ne_zero)]
                   "]"]
                  []
                  [])
                 [])]))))))
         [])
        (group (Tactic.classical "classical") [])
        (group
         (Tactic.convert
          "convert"
          []
          (Term.proj
           (Term.proj (Init.Core.«term_∪_» `φ.roots " ∪ " (Set.«term{_}» "{" [(numLit "0")] "}")) "." `toFinset)
           "."
           `finite_to_set)
          ["using" (numLit "1")])
         [])
        (group (Tactic.ext1 "ext1" [(Tactic.rcasesPat.one `y)]) [])
        (group
         (Tactic.simp
          "simp"
          []
          ["only"]
          ["["
           [(Tactic.simpLemma [] [] `Multiset.mem_to_finset)
            ","
            (Tactic.simpLemma [] [] `Set.mem_set_of_eq)
            ","
            (Tactic.simpLemma [] [] `Finset.mem_coe)
            ","
            (Tactic.simpLemma [] [] `Multiset.mem_union)
            ","
            (Tactic.simpLemma [] [] (Term.app `mem_roots [`hφ]))
            ","
            (Tactic.simpLemma [] [] `is_root)
            ","
            (Tactic.simpLemma [] [] `eval_add)
            ","
            (Tactic.simpLemma [] [] `eval_sub)
            ","
            (Tactic.simpLemma [] [] `eval_pow)
            ","
            (Tactic.simpLemma [] [] `eval_mul)
            ","
            (Tactic.simpLemma [] [] `eval_X)
            ","
            (Tactic.simpLemma [] [] `eval_C)
            ","
            (Tactic.simpLemma [] [] `eval_one)
            ","
            (Tactic.simpLemma [] [] `Multiset.mem_singleton)]
           "]"]
          [])
         [])
        (group (Tactic.byCases' "by_cases'" [`hy ":"] («term_=_» `y "=" (numLit "0"))) [])
        (group
         (Tactic.«tactic·._»
          "·"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(group
              (Tactic.simp
               "simp"
               []
               ["only"]
               ["["
                [(Tactic.simpLemma [] [] `hy)
                 ","
                 (Tactic.simpLemma [] [] `eq_self_iff_true)
                 ","
                 (Tactic.simpLemma [] [] `or_trueₓ)]
                "]"]
               [])
              [])])))
         [])
        (group (Tactic.apply "apply" (Term.app `or_congr [(Term.hole "_") `Iff.rfl])) [])
        (group
         (Tactic.rwSeq
          "rw"
          []
          (Tactic.rwRuleSeq
           "["
           [(Tactic.rwRule ["←"] (Term.app `mul_left_inj' [`hy]))
            ","
            (Tactic.rwRule [] `eq_comm)
            ","
            (Tactic.rwRule ["←"] `sub_eq_zero)
            ","
            (Tactic.rwRule [] `add_mulₓ)
            ","
            (Tactic.rwRule [] (Term.app `inv_mul_cancel [`hy]))]
           "]")
          [])
         [])
        (group (Tactic.apply "apply" `eq_iff_eq_cancel_right.mpr) [])
        (group (Tactic.Ring.tacticRing "ring") [])])))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSuffices_', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.sufficesDecl', expected 'Lean.Parser.Term.sufficesDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.fromTerm.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.fromTerm'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.Ring.tacticRing "ring")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Tactic.Ring.tacticRing', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, tactic))
  (Tactic.apply "apply" `eq_iff_eq_cancel_right.mpr)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.apply', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `eq_iff_eq_cancel_right.mpr
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.rwSeq
   "rw"
   []
   (Tactic.rwRuleSeq
    "["
    [(Tactic.rwRule ["←"] (Term.app `mul_left_inj' [`hy]))
     ","
     (Tactic.rwRule [] `eq_comm)
     ","
     (Tactic.rwRule ["←"] `sub_eq_zero)
     ","
     (Tactic.rwRule [] `add_mulₓ)
     ","
     (Tactic.rwRule [] (Term.app `inv_mul_cancel [`hy]))]
    "]")
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwSeq', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `inv_mul_cancel [`hy])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hy
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `inv_mul_cancel
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `add_mulₓ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `sub_eq_zero
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«←»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `eq_comm
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `mul_left_inj' [`hy])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hy
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `mul_left_inj'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«←»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.apply "apply" (Term.app `or_congr [(Term.hole "_") `Iff.rfl]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.apply', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `or_congr [(Term.hole "_") `Iff.rfl])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Iff.rfl
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `or_congr
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.«tactic·._»
   "·"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.simp
        "simp"
        []
        ["only"]
        ["["
         [(Tactic.simpLemma [] [] `hy)
          ","
          (Tactic.simpLemma [] [] `eq_self_iff_true)
          ","
          (Tactic.simpLemma [] [] `or_trueₓ)]
         "]"]
        [])
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.«tactic·._»', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.simp
   "simp"
   []
   ["only"]
   ["["
    [(Tactic.simpLemma [] [] `hy) "," (Tactic.simpLemma [] [] `eq_self_iff_true) "," (Tactic.simpLemma [] [] `or_trueₓ)]
    "]"]
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `or_trueₓ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `eq_self_iff_true
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hy
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'only', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.byCases' "by_cases'" [`hy ":"] («term_=_» `y "=" (numLit "0")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.byCases'', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_=_» `y "=" (numLit "0"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "0")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  `y
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«:»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.simp
   "simp"
   []
   ["only"]
   ["["
    [(Tactic.simpLemma [] [] `Multiset.mem_to_finset)
     ","
     (Tactic.simpLemma [] [] `Set.mem_set_of_eq)
     ","
     (Tactic.simpLemma [] [] `Finset.mem_coe)
     ","
     (Tactic.simpLemma [] [] `Multiset.mem_union)
     ","
     (Tactic.simpLemma [] [] (Term.app `mem_roots [`hφ]))
     ","
     (Tactic.simpLemma [] [] `is_root)
     ","
     (Tactic.simpLemma [] [] `eval_add)
     ","
     (Tactic.simpLemma [] [] `eval_sub)
     ","
     (Tactic.simpLemma [] [] `eval_pow)
     ","
     (Tactic.simpLemma [] [] `eval_mul)
     ","
     (Tactic.simpLemma [] [] `eval_X)
     ","
     (Tactic.simpLemma [] [] `eval_C)
     ","
     (Tactic.simpLemma [] [] `eval_one)
     ","
     (Tactic.simpLemma [] [] `Multiset.mem_singleton)]
    "]"]
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Multiset.mem_singleton
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `eval_one
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `eval_C
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `eval_X
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `eval_mul
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `eval_pow
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `eval_sub
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `eval_add
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `is_root
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `mem_roots [`hφ])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hφ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `mem_roots
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Multiset.mem_union
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Finset.mem_coe
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Set.mem_set_of_eq
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Multiset.mem_to_finset
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'only', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.ext1 "ext1" [(Tactic.rcasesPat.one `y)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.ext1', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.convert
   "convert"
   []
   (Term.proj
    (Term.proj (Init.Core.«term_∪_» `φ.roots " ∪ " (Set.«term{_}» "{" [(numLit "0")] "}")) "." `toFinset)
    "."
    `finite_to_set)
   ["using" (numLit "1")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.convert', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.proj
   (Term.proj (Init.Core.«term_∪_» `φ.roots " ∪ " (Set.«term{_}» "{" [(numLit "0")] "}")) "." `toFinset)
   "."
   `finite_to_set)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.proj (Init.Core.«term_∪_» `φ.roots " ∪ " (Set.«term{_}» "{" [(numLit "0")] "}")) "." `toFinset)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Init.Core.«term_∪_» `φ.roots " ∪ " (Set.«term{_}» "{" [(numLit "0")] "}"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Core.«term_∪_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Set.«term{_}» "{" [(numLit "0")] "}")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_}»', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "0")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
  `φ.roots
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 65, (some 66, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Init.Core.«term_∪_» `φ.roots " ∪ " (Set.«term{_}» "{" [(numLit "0")] "}")) []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.classical "classical")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.classical', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, tactic))
  (Tactic.tacticHave_
   "have"
   (Term.haveDecl
    (Term.haveIdDecl
     [`hφ []]
     [(Term.typeSpec ":" («term_≠_» `φ "≠" (numLit "0")))]
     ":="
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(group (Tactic.intro "intro" [`H]) [])
         (group
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             []
             [(Term.typeSpec ":" («term_=_» (Term.app `φ.eval [(numLit "0")]) "=" (numLit "0")))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(group
                  (Tactic.rwSeq
                   "rw"
                   []
                   (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `H) "," (Tactic.rwRule [] `eval_zero)] "]")
                   [])
                  [])]))))))
          [])
         (group
          (Tactic.simpa
           "simpa"
           []
           []
           ["["
            [(Tactic.simpLemma [] [] `eval_X)
             ","
             (Tactic.simpLemma [] [] `eval_one)
             ","
             (Tactic.simpLemma [] [] `eval_pow)
             ","
             (Tactic.simpLemma [] [] `eval_sub)
             ","
             (Tactic.simpLemma [] [] `sub_zero)
             ","
             (Tactic.simpLemma [] [] `eval_add)
             ","
             (Tactic.simpLemma [] [] `eval_mul)
             ","
             (Tactic.simpLemma [] [] `mul_zero)
             ","
             (Tactic.simpLemma [] [] `sq)
             ","
             (Tactic.simpLemma [] [] `zero_addₓ)
             ","
             (Tactic.simpLemma [] [] `one_ne_zero)]
            "]"]
           []
           [])
          [])]))))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticHave_', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveDecl', expected 'Lean.Parser.Term.haveDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveIdDecl.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group (Tactic.intro "intro" [`H]) [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          []
          [(Term.typeSpec ":" («term_=_» (Term.app `φ.eval [(numLit "0")]) "=" (numLit "0")))]
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group
               (Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `H) "," (Tactic.rwRule [] `eval_zero)] "]")
                [])
               [])]))))))
       [])
      (group
       (Tactic.simpa
        "simpa"
        []
        []
        ["["
         [(Tactic.simpLemma [] [] `eval_X)
          ","
          (Tactic.simpLemma [] [] `eval_one)
          ","
          (Tactic.simpLemma [] [] `eval_pow)
          ","
          (Tactic.simpLemma [] [] `eval_sub)
          ","
          (Tactic.simpLemma [] [] `sub_zero)
          ","
          (Tactic.simpLemma [] [] `eval_add)
          ","
          (Tactic.simpLemma [] [] `eval_mul)
          ","
          (Tactic.simpLemma [] [] `mul_zero)
          ","
          (Tactic.simpLemma [] [] `sq)
          ","
          (Tactic.simpLemma [] [] `zero_addₓ)
          ","
          (Tactic.simpLemma [] [] `one_ne_zero)]
         "]"]
        []
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
  (Tactic.simpa
   "simpa"
   []
   []
   ["["
    [(Tactic.simpLemma [] [] `eval_X)
     ","
     (Tactic.simpLemma [] [] `eval_one)
     ","
     (Tactic.simpLemma [] [] `eval_pow)
     ","
     (Tactic.simpLemma [] [] `eval_sub)
     ","
     (Tactic.simpLemma [] [] `sub_zero)
     ","
     (Tactic.simpLemma [] [] `eval_add)
     ","
     (Tactic.simpLemma [] [] `eval_mul)
     ","
     (Tactic.simpLemma [] [] `mul_zero)
     ","
     (Tactic.simpLemma [] [] `sq)
     ","
     (Tactic.simpLemma [] [] `zero_addₓ)
     ","
     (Tactic.simpLemma [] [] `one_ne_zero)]
    "]"]
   []
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpa', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `one_ne_zero
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `zero_addₓ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `sq
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `mul_zero
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `eval_mul
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `eval_add
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `sub_zero
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `eval_sub
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `eval_pow
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `eval_one
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `eval_X
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.tacticHave_
   "have"
   (Term.haveDecl
    (Term.haveIdDecl
     []
     [(Term.typeSpec ":" («term_=_» (Term.app `φ.eval [(numLit "0")]) "=" (numLit "0")))]
     ":="
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(group
          (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `H) "," (Tactic.rwRule [] `eval_zero)] "]") [])
          [])]))))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticHave_', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveDecl', expected 'Lean.Parser.Term.haveDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveIdDecl.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `H) "," (Tactic.rwRule [] `eval_zero)] "]") [])
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `H) "," (Tactic.rwRule [] `eval_zero)] "]") [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwSeq', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `eval_zero
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `H
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_=_» (Term.app `φ.eval [(numLit "0")]) "=" (numLit "0"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "0")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Term.app `φ.eval [(numLit "0")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "0")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `φ.eval
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.intro "intro" [`H])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.intro', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `H
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_≠_» `φ "≠" (numLit "0"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_≠_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "0")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  `φ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.tacticLet_
   "let"
   (Term.letDecl
    (Term.letIdDecl
     `φ
     [(Term.typeSpec ":" (Term.app `Polynomial [`K]))]
     ":="
     (Init.Logic.«term_+_»
      («term_-_»
       (Cardinal.SetTheory.Cofinality.«term_^_» `X "^" (numLit "2"))
       "-"
       (Finset.Data.Finset.Fold.«term_*_» (Term.app `C [`x]) "*" `X))
      "+"
      (numLit "1")))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticLet_', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letDecl', expected 'Lean.Parser.Term.letDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letIdDecl', expected 'Lean.Parser.Term.letIdDecl.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Logic.«term_+_»
   («term_-_»
    (Cardinal.SetTheory.Cofinality.«term_^_» `X "^" (numLit "2"))
    "-"
    (Finset.Data.Finset.Fold.«term_*_» (Term.app `C [`x]) "*" `X))
   "+"
   (numLit "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "1")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  («term_-_»
   (Cardinal.SetTheory.Cofinality.«term_^_» `X "^" (numLit "2"))
   "-"
   (Finset.Data.Finset.Fold.«term_*_» (Term.app `C [`x]) "*" `X))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_-_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Finset.Data.Finset.Fold.«term_*_» (Term.app `C [`x]) "*" `X)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `X
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.app `C [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `x
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `C
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
  (Cardinal.SetTheory.Cofinality.«term_^_» `X "^" (numLit "2"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Cardinal.SetTheory.Cofinality.«term_^_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "2")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 0, term))
  `X
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1 >? 1024, (none, [anonymous]) <=? (some 0, term)
[PrettyPrinter.parenthesize] ...precedences are 65 >? 0, (some 0, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Cardinal.SetTheory.Cofinality.«term_^_» `X "^" (numLit "2")) []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 65, (some 0, term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(«term_-_»
   (Term.paren "(" [(Cardinal.SetTheory.Cofinality.«term_^_» `X "^" (numLit "2")) []] ")")
   "-"
   (Finset.Data.Finset.Fold.«term_*_» (Term.app `C [`x]) "*" `X))
  []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Polynomial [`K])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `K
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Polynomial
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.refine'
   "refine'"
   (Term.app `h.bUnion [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`x `hx] [])] "=>" (Term.hole "_")))]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.refine'', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `h.bUnion [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`x `hx] [])] "=>" (Term.hole "_")))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`x `hx] [])] "=>" (Term.hole "_")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.strictImplicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.implicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.instBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.simpleBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `h.bUnion
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.clear "clear" [`this])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.clear', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `this
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `this)] "]") [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwSeq', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `this
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, [anonymous]))
  («term_=_»
   (Term.paren "(" [`Set.Univ [(Term.typeAscription ":" (Term.app `Set [`K]))]] ")")
   "="
   (Init.Control.Monad.«term_>>=_»
    (Set.«term{_|_}»
     "{"
     (Mathlib.ExtendedBinder.extBinder `x [":" `K])
     "|"
     («term∃_,_»
      "∃"
      (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `y)] [":" `K]))
      ","
      («term_∧_»
       («term_=_» `x "=" (Init.Logic.«term_+_» `y "+" (Init.Logic.«term_⁻¹» `y "⁻¹")))
       "∧"
       («term_≠_» `y "≠" (numLit "0"))))
     "}")
    " >>= "
    (Term.fun
     "fun"
     (Term.basicFun
      [(Term.simpleBinder [`x] [])]
      "=>"
      (Set.«term{_|_}»
       "{"
       `y
       "|"
       («term_∨_»
        («term_=_» `x "=" (Init.Logic.«term_+_» `y "+" (Init.Logic.«term_⁻¹» `y "⁻¹")))
        "∨"
        («term_=_» `y "=" (numLit "0")))
       "}")))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Control.Monad.«term_>>=_»
   (Set.«term{_|_}»
    "{"
    (Mathlib.ExtendedBinder.extBinder `x [":" `K])
    "|"
    («term∃_,_»
     "∃"
     (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `y)] [":" `K]))
     ","
     («term_∧_»
      («term_=_» `x "=" (Init.Logic.«term_+_» `y "+" (Init.Logic.«term_⁻¹» `y "⁻¹")))
      "∧"
      («term_≠_» `y "≠" (numLit "0"))))
    "}")
   " >>= "
   (Term.fun
    "fun"
    (Term.basicFun
     [(Term.simpleBinder [`x] [])]
     "=>"
     (Set.«term{_|_}»
      "{"
      `y
      "|"
      («term_∨_»
       («term_=_» `x "=" (Init.Logic.«term_+_» `y "+" (Init.Logic.«term_⁻¹» `y "⁻¹")))
       "∨"
       («term_=_» `y "=" (numLit "0")))
      "}"))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Control.Monad.«term_>>=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [`x] [])]
    "=>"
    (Set.«term{_|_}»
     "{"
     `y
     "|"
     («term_∨_»
      («term_=_» `x "=" (Init.Logic.«term_+_» `y "+" (Init.Logic.«term_⁻¹» `y "⁻¹")))
      "∨"
      («term_=_» `y "=" (numLit "0")))
     "}")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Set.«term{_|_}»
   "{"
   `y
   "|"
   («term_∨_»
    («term_=_» `x "=" (Init.Logic.«term_+_» `y "+" (Init.Logic.«term_⁻¹» `y "⁻¹")))
    "∨"
    («term_=_» `y "=" (numLit "0")))
   "}")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_∨_»
   («term_=_» `x "=" (Init.Logic.«term_+_» `y "+" (Init.Logic.«term_⁻¹» `y "⁻¹")))
   "∨"
   («term_=_» `y "=" (numLit "0")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_∨_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_=_» `y "=" (numLit "0"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "0")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  `y
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 30 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 30, term))
  («term_=_» `x "=" (Init.Logic.«term_+_» `y "+" (Init.Logic.«term_⁻¹» `y "⁻¹")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Logic.«term_+_» `y "+" (Init.Logic.«term_⁻¹» `y "⁻¹"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Logic.«term_⁻¹» `y "⁻¹")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_⁻¹»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `y
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `y
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  `x
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 31 >? 50, (some 0, term) <=? (some 30, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(«term_=_» `x "=" (Init.Logic.«term_+_» `y "+" (Init.Logic.«term_⁻¹» `y "⁻¹"))) []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 30, (some 30, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Mathlib.ExtendedBinder.extBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
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
  dickson_one_one_zmod_p
  ( p : ℕ ) [ Fact p.prime ] : dickson 1 ( 1 : Zmod p ) p = X ^ p
  :=
    by
      obtain ⟨ K , _ , _ , H ⟩ : ∃ ( K : Type ) ( _ : Field K ) , by exact ∃ _ : CharP K p , Infinite K
        ·
          let K := FractionRing Polynomial Zmod p
            let f : Zmod p →+* K := algebraMap _ FractionRing _ . comp C
            have : CharP K p := by rw [ ← f.char_p_iff_char_p ] infer_instance
            have
              : Infinite K
                :=
                Infinite.of_injective
                  algebraMap Polynomial Zmod p FractionRing Polynomial Zmod p IsFractionRing.injective _ _
            refine' ⟨ K , _ , _ , _ ⟩ <;> infer_instance
        skip
        apply map_injective Zmod.castHom dvd_refl p K RingHom.injective _
        rw [ map_dickson , Polynomial.map_pow , map_X ]
        apply eq_of_infinite_eval_eq
        apply @ Set.Infinite.mono _ { x : K | ∃ y , x = y + y ⁻¹ ∧ y ≠ 0 }
        ·
          rintro _ ⟨ x , rfl , hx ⟩
            simp
              only
              [
                eval_X
                  ,
                  eval_pow
                  ,
                  Set.mem_set_of_eq
                  ,
                  @ add_pow_char K _ p
                  ,
                  dickson_one_one_eval_add_inv _ _ mul_inv_cancel hx
                  ,
                  inv_pow₀
                  ,
                  Zmod.cast_hom_apply
                  ,
                  Zmod.cast_one'
                ]
        ·
          intro h
            rw [ ← Set.infinite_univ_iff ] at H
            apply H
            suffices
              ( Set.Univ : Set K )
                  =
                  { x : K | ∃ y : K , x = y + y ⁻¹ ∧ y ≠ 0 } >>= fun x => { y | x = y + y ⁻¹ ∨ y = 0 }
                by
                  rw [ this ]
                    clear this
                    refine' h.bUnion fun x hx => _
                    let φ : Polynomial K := X ^ 2 - C x * X + 1
                    have
                      hφ
                        : φ ≠ 0
                        :=
                        by
                          intro H
                            have : φ.eval 0 = 0 := by rw [ H , eval_zero ]
                            simpa
                              [
                                eval_X
                                  ,
                                  eval_one
                                  ,
                                  eval_pow
                                  ,
                                  eval_sub
                                  ,
                                  sub_zero
                                  ,
                                  eval_add
                                  ,
                                  eval_mul
                                  ,
                                  mul_zero
                                  ,
                                  sq
                                  ,
                                  zero_addₓ
                                  ,
                                  one_ne_zero
                                ]
                    classical
                    convert φ.roots ∪ { 0 } . toFinset . finite_to_set using 1
                    ext1 y
                    simp
                      only
                      [
                        Multiset.mem_to_finset
                          ,
                          Set.mem_set_of_eq
                          ,
                          Finset.mem_coe
                          ,
                          Multiset.mem_union
                          ,
                          mem_roots hφ
                          ,
                          is_root
                          ,
                          eval_add
                          ,
                          eval_sub
                          ,
                          eval_pow
                          ,
                          eval_mul
                          ,
                          eval_X
                          ,
                          eval_C
                          ,
                          eval_one
                          ,
                          Multiset.mem_singleton
                        ]
                    by_cases' hy : y = 0
                    · simp only [ hy , eq_self_iff_true , or_trueₓ ]
                    apply or_congr _ Iff.rfl
                    rw [ ← mul_left_inj' hy , eq_comm , ← sub_eq_zero , add_mulₓ , inv_mul_cancel hy ]
                    apply eq_iff_eq_cancel_right.mpr
                    ring
            ·
              apply Set.eq_univ_of_forall _ . symm
                intro x
                simp only [ exists_prop , Set.mem_Union , Set.bind_def , Ne.def , Set.mem_set_of_eq ]
                by_cases' hx : x = 0
                ·
                  simp only [ hx , and_trueₓ , eq_self_iff_true , inv_zero , or_trueₓ ]
                    exact ⟨ _ , 1 , rfl , one_ne_zero ⟩
                · simp only [ hx , or_falseₓ , exists_eq_right ] exact ⟨ _ , rfl , hx ⟩

theorem dickson_one_one_char_p (p : ℕ) [Fact p.prime] [CharP R p] : dickson 1 (1 : R) p = (X^p) := by
  have h : (1 : R) = Zmod.castHom (dvd_refl p) R 1
  simp only [Zmod.cast_hom_apply, Zmod.cast_one']
  rw [h, ← map_dickson (Zmod.castHom (dvd_refl p) R), dickson_one_one_zmod_p, Polynomial.map_pow, map_X]

end Dickson

end Polynomial

