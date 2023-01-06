/-
Copyright (c) 2022 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis, Heather Macbeth

! This file was ported from Lean 3 source module ring_theory.witt_vector.mul_coeff
! leanprover-community/mathlib commit 18a5306c091183ac90884daa9373fa3b178e8607
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.RingTheory.WittVector.Truncated
import Mathbin.Data.MvPolynomial.Supported

/-!
# Leading terms of Witt vector multiplication

The goal of this file is to study the leading terms of the formula for the `n+1`st coefficient
of a product of Witt vectors `x` and `y` over a ring of characteristic `p`.
We aim to isolate the `n+1`st coefficients of `x` and `y`, and express the rest of the product
in terms of a function of the lower coefficients.

For most of this file we work with terms of type `mv_polynomial (fin 2 × ℕ) ℤ`.
We will eventually evaluate them in `k`, but first we must take care of a calculation
that needs to happen in characteristic 0.

## Main declarations

* `witt_vector.nth_mul_coeff`: expresses the coefficient of a product of Witt vectors
  in terms of the previous coefficients of the multiplicands.

-/


noncomputable section

namespace WittVector

variable (p : ℕ) [hp : Fact p.Prime]

variable {k : Type _} [CommRing k]

-- mathport name: expr𝕎
local notation "𝕎" => WittVector p

open Finset MvPolynomial

open BigOperators

/-- ```
(∑ i in range n, (y.coeff i)^(p^(n-i)) * p^i.val) *
  (∑ i in range n, (y.coeff i)^(p^(n-i)) * p^i.val)
```
-/
def wittPolyProd (n : ℕ) : MvPolynomial (Fin 2 × ℕ) ℤ :=
  rename (Prod.mk (0 : Fin 2)) (wittPolynomial p ℤ n) *
    rename (Prod.mk (1 : Fin 2)) (wittPolynomial p ℤ n)
#align witt_vector.witt_poly_prod WittVector.wittPolyProd

include hp

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem witt_poly_prod_vars (n : ℕ) : (wittPolyProd p n).vars ⊆ univ ×ˢ range (n + 1) :=
  by
  rw [witt_poly_prod]
  apply subset.trans (vars_mul _ _)
  apply union_subset <;>
    · apply subset.trans (vars_rename _ _)
      simp [witt_polynomial_vars, image_subset_iff]
#align witt_vector.witt_poly_prod_vars WittVector.witt_poly_prod_vars

/-- The "remainder term" of `witt_vector.witt_poly_prod`. See `mul_poly_of_interest_aux2`. -/
def wittPolyProdRemainder (n : ℕ) : MvPolynomial (Fin 2 × ℕ) ℤ :=
  ∑ i in range n, p ^ i * wittMul p i ^ p ^ (n - i)
#align witt_vector.witt_poly_prod_remainder WittVector.wittPolyProdRemainder

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem witt_poly_prod_remainder_vars (n : ℕ) :
    (wittPolyProdRemainder p n).vars ⊆ univ ×ˢ range n :=
  by
  rw [witt_poly_prod_remainder]
  apply subset.trans (vars_sum_subset _ _)
  rw [bUnion_subset]
  intro x hx
  apply subset.trans (vars_mul _ _)
  apply union_subset
  · apply subset.trans (vars_pow _ _)
    have : (p : MvPolynomial (Fin 2 × ℕ) ℤ) = C (p : ℤ) := by simp only [Int.cast_ofNat, eq_intCast]
    rw [this, vars_C]
    apply empty_subset
  · apply subset.trans (vars_pow _ _)
    apply subset.trans (witt_mul_vars _ _)
    apply product_subset_product (subset.refl _)
    simp only [mem_range, range_subset] at hx⊢
    exact hx
#align witt_vector.witt_poly_prod_remainder_vars WittVector.witt_poly_prod_remainder_vars

omit hp

/-- `remainder p n` represents the remainder term from `mul_poly_of_interest_aux3`.
`witt_poly_prod p (n+1)` will have variables up to `n+1`,
but `remainder` will only have variables up to `n`.
-/
def remainder (n : ℕ) : MvPolynomial (Fin 2 × ℕ) ℤ :=
  (∑ x : ℕ in range (n + 1),
      (rename (Prod.mk 0)) ((monomial (Finsupp.single x (p ^ (n + 1 - x)))) (↑p ^ x))) *
    ∑ x : ℕ in range (n + 1),
      (rename (Prod.mk 1)) ((monomial (Finsupp.single x (p ^ (n + 1 - x)))) (↑p ^ x))
#align witt_vector.remainder WittVector.remainder

include hp

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem remainder_vars (n : ℕ) : (remainder p n).vars ⊆ univ ×ˢ range (n + 1) :=
  by
  rw [remainder]
  apply subset.trans (vars_mul _ _)
  apply union_subset <;>
    · apply subset.trans (vars_sum_subset _ _)
      rw [bUnion_subset]
      intro x hx
      rw [rename_monomial, vars_monomial, Finsupp.map_domain_single]
      · apply subset.trans Finsupp.support_single_subset
        simp [hx]
      · apply pow_ne_zero
        exact_mod_cast hp.out.ne_zero
#align witt_vector.remainder_vars WittVector.remainder_vars

/-- This is the polynomial whose degree we want to get a handle on. -/
def polyOfInterest (n : ℕ) : MvPolynomial (Fin 2 × ℕ) ℤ :=
  wittMul p (n + 1) + p ^ (n + 1) * x (0, n + 1) * x (1, n + 1) -
      x (0, n + 1) * rename (Prod.mk (1 : Fin 2)) (wittPolynomial p ℤ (n + 1)) -
    x (1, n + 1) * rename (Prod.mk (0 : Fin 2)) (wittPolynomial p ℤ (n + 1))
#align witt_vector.poly_of_interest WittVector.polyOfInterest

theorem mul_poly_of_interest_aux1 (n : ℕ) :
    (∑ i in range (n + 1), p ^ i * wittMul p i ^ p ^ (n - i) : MvPolynomial (Fin 2 × ℕ) ℤ) =
      wittPolyProd p n :=
  by
  simp only [witt_poly_prod]
  convert witt_structure_int_prop p (X (0 : Fin 2) * X 1) n using 1
  · simp only [wittPolynomial, witt_mul]
    rw [AlgHom.map_sum]
    congr 1 with i
    congr 1
    have hsupp : (Finsupp.single i (p ^ (n - i))).support = {i} :=
      by
      rw [Finsupp.support_eq_singleton]
      simp only [and_true_iff, Finsupp.single_eq_same, eq_self_iff_true, Ne.def]
      exact pow_ne_zero _ hp.out.ne_zero
    simp only [bind₁_monomial, hsupp, Int.cast_ofNat, prod_singleton, eq_intCast,
      Finsupp.single_eq_same, C_pow, mul_eq_mul_left_iff, true_or_iff, eq_self_iff_true]
  · simp only [map_mul, bind₁_X_right]
#align witt_vector.mul_poly_of_interest_aux1 WittVector.mul_poly_of_interest_aux1

theorem mul_poly_of_interest_aux2 (n : ℕ) :
    (p ^ n * wittMul p n : MvPolynomial (Fin 2 × ℕ) ℤ) + wittPolyProdRemainder p n =
      wittPolyProd p n :=
  by
  convert mul_poly_of_interest_aux1 p n
  rw [sum_range_succ, add_comm, Nat.sub_self, pow_zero, pow_one]
  rfl
#align witt_vector.mul_poly_of_interest_aux2 WittVector.mul_poly_of_interest_aux2

omit hp

theorem mul_poly_of_interest_aux3 (n : ℕ) :
    wittPolyProd p (n + 1) =
      -(p ^ (n + 1) * x (0, n + 1)) * (p ^ (n + 1) * x (1, n + 1)) +
            p ^ (n + 1) * x (0, n + 1) * rename (Prod.mk (1 : Fin 2)) (wittPolynomial p ℤ (n + 1)) +
          p ^ (n + 1) * x (1, n + 1) * rename (Prod.mk (0 : Fin 2)) (wittPolynomial p ℤ (n + 1)) +
        remainder p n :=
  by
  -- a useful auxiliary fact
  have mvpz : (p ^ (n + 1) : MvPolynomial (Fin 2 × ℕ) ℤ) = MvPolynomial.c (↑p ^ (n + 1)) := by
    simp only [Int.cast_ofNat, eq_intCast, C_pow, eq_self_iff_true]
  -- unfold definitions and peel off the last entries of the sums.
  rw [witt_poly_prod, wittPolynomial, AlgHom.map_sum, AlgHom.map_sum, sum_range_succ]
  -- these are sums up to `n+2`, so be careful to only unfold to `n+1`.
  conv_lhs =>
    congr
    skip
    rw [sum_range_succ]
  simp only [add_mul, mul_add, tsub_self, pow_zero, AlgHom.map_sum]
  -- rearrange so that the first summand on rhs and lhs is `remainder`, and peel off
  conv_rhs => rw [add_comm]
  simp only [add_assoc]
  apply congr_arg (Add.add _)
  conv_rhs => rw [sum_range_succ]
  -- the rest is equal with proper unfolding and `ring`
  simp only [rename_monomial, ← C_mul_X_pow_eq_monomial, map_mul, rename_C, pow_one, rename_X]
  simp only [mvpz, Int.cast_ofNat, map_pow, eq_intCast, rename_X, pow_one, tsub_self, pow_zero]
  ring1
#align witt_vector.mul_poly_of_interest_aux3 WittVector.mul_poly_of_interest_aux3

include hp

theorem mul_poly_of_interest_aux4 (n : ℕ) :
    (p ^ (n + 1) * wittMul p (n + 1) : MvPolynomial (Fin 2 × ℕ) ℤ) =
      -(p ^ (n + 1) * x (0, n + 1)) * (p ^ (n + 1) * x (1, n + 1)) +
            p ^ (n + 1) * x (0, n + 1) * rename (Prod.mk (1 : Fin 2)) (wittPolynomial p ℤ (n + 1)) +
          p ^ (n + 1) * x (1, n + 1) * rename (Prod.mk (0 : Fin 2)) (wittPolynomial p ℤ (n + 1)) +
        (remainder p n - wittPolyProdRemainder p (n + 1)) :=
  by
  rw [← add_sub_assoc, eq_sub_iff_add_eq, mul_poly_of_interest_aux2]
  exact mul_poly_of_interest_aux3 _ _
#align witt_vector.mul_poly_of_interest_aux4 WittVector.mul_poly_of_interest_aux4

theorem mul_poly_of_interest_aux5 (n : ℕ) :
    (p ^ (n + 1) : MvPolynomial (Fin 2 × ℕ) ℤ) * polyOfInterest p n =
      remainder p n - wittPolyProdRemainder p (n + 1) :=
  by
  simp only [poly_of_interest, mul_sub, mul_add, sub_eq_iff_eq_add']
  rw [mul_poly_of_interest_aux4 p n]
  ring
#align witt_vector.mul_poly_of_interest_aux5 WittVector.mul_poly_of_interest_aux5

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem mul_poly_of_interest_vars (n : ℕ) :
    ((p ^ (n + 1) : MvPolynomial (Fin 2 × ℕ) ℤ) * polyOfInterest p n).vars ⊆
      univ ×ˢ range (n + 1) :=
  by
  rw [mul_poly_of_interest_aux5]
  apply subset.trans (vars_sub_subset _ _)
  apply union_subset
  · apply remainder_vars
  · apply witt_poly_prod_remainder_vars
#align witt_vector.mul_poly_of_interest_vars WittVector.mul_poly_of_interest_vars

theorem poly_of_interest_vars_eq (n : ℕ) :
    (polyOfInterest p n).vars =
      ((p ^ (n + 1) : MvPolynomial (Fin 2 × ℕ) ℤ) *
          (wittMul p (n + 1) + p ^ (n + 1) * x (0, n + 1) * x (1, n + 1) -
              x (0, n + 1) * rename (Prod.mk (1 : Fin 2)) (wittPolynomial p ℤ (n + 1)) -
            x (1, n + 1) * rename (Prod.mk (0 : Fin 2)) (wittPolynomial p ℤ (n + 1)))).vars :=
  by
  have : (p ^ (n + 1) : MvPolynomial (Fin 2 × ℕ) ℤ) = C (p ^ (n + 1) : ℤ) := by
    simp only [Int.cast_ofNat, eq_intCast, C_pow, eq_self_iff_true]
  rw [poly_of_interest, this, vars_C_mul]
  apply pow_ne_zero
  exact_mod_cast hp.out.ne_zero
#align witt_vector.poly_of_interest_vars_eq WittVector.poly_of_interest_vars_eq

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem poly_of_interest_vars (n : ℕ) : (polyOfInterest p n).vars ⊆ univ ×ˢ range (n + 1) := by
  rw [poly_of_interest_vars_eq] <;> apply mul_poly_of_interest_vars
#align witt_vector.poly_of_interest_vars WittVector.poly_of_interest_vars

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `peval_poly_of_interest [])
      (Command.declSig
       [(Term.explicitBinder "(" [`n] [":" (termℕ "ℕ")] [] ")")
        (Term.explicitBinder
         "("
         [`x `y]
         [":" (Term.app (WittVector.RingTheory.WittVector.MulCoeff.term𝕎 "𝕎") [`k])]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app
          `peval
          [(Term.app `polyOfInterest [`p `n])
           (Matrix.Data.Fin.VecNotation.«term![_,»
            "!["
            [(Term.fun "fun" (Term.basicFun [`i] [] "=>" (Term.app (Term.proj `x "." `coeff) [`i])))
             ","
             (Term.fun
              "fun"
              (Term.basicFun [`i] [] "=>" (Term.app (Term.proj `y "." `coeff) [`i])))]
            "]")])
         "="
         («term_-_»
          («term_-_»
           («term_+_»
            (Term.app (Term.proj («term_*_» `x "*" `y) "." `coeff) [(«term_+_» `n "+" (num "1"))])
            "+"
            («term_*_»
             («term_*_»
              («term_^_» `p "^" («term_+_» `n "+" (num "1")))
              "*"
              (Term.app (Term.proj `x "." `coeff) [(«term_+_» `n "+" (num "1"))]))
             "*"
             (Term.app (Term.proj `y "." `coeff) [(«term_+_» `n "+" (num "1"))])))
           "-"
           («term_*_»
            (Term.app (Term.proj `y "." `coeff) [(«term_+_» `n "+" (num "1"))])
            "*"
            (BigOperators.Algebra.BigOperators.Basic.finset.sum
             "∑"
             (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
             " in "
             (Term.app `range [(«term_+_» («term_+_» `n "+" (num "1")) "+" (num "1"))])
             ", "
             («term_*_»
              («term_^_» `p "^" `i)
              "*"
              («term_^_»
               (Term.app (Term.proj `x "." `coeff) [`i])
               "^"
               («term_^_» `p "^" («term_-_» («term_+_» `n "+" (num "1")) "-" `i)))))))
          "-"
          («term_*_»
           (Term.app (Term.proj `x "." `coeff) [(«term_+_» `n "+" (num "1"))])
           "*"
           (BigOperators.Algebra.BigOperators.Basic.finset.sum
            "∑"
            (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
            " in "
            (Term.app `range [(«term_+_» («term_+_» `n "+" (num "1")) "+" (num "1"))])
            ", "
            («term_*_»
             («term_^_» `p "^" `i)
             "*"
             («term_^_»
              (Term.app (Term.proj `y "." `coeff) [`i])
              "^"
              («term_^_» `p "^" («term_-_» («term_+_» `n "+" (num "1")) "-" `i))))))))))
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
             [(Tactic.simpLemma [] [] `poly_of_interest)
              ","
              (Tactic.simpLemma [] [] `peval)
              ","
              (Tactic.simpLemma [] [] `map_nat_cast)
              ","
              (Tactic.simpLemma [] [] `Matrix.head_cons)
              ","
              (Tactic.simpLemma [] [] `map_pow)
              ","
              (Tactic.simpLemma [] [] `Function.uncurry_apply_pair)
              ","
              (Tactic.simpLemma [] [] `aeval_X)
              ","
              (Tactic.simpLemma [] [] `Matrix.cons_val_one)
              ","
              (Tactic.simpLemma [] [] `map_mul)
              ","
              (Tactic.simpLemma [] [] `Matrix.cons_val_zero)
              ","
              (Tactic.simpLemma [] [] `map_sub)]
             "]"]
            [])
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [] `sub_sub)
              ","
              (Tactic.rwRule
               []
               (Term.app `add_comm [(«term_*_» (Term.hole "_") "*" (Term.hole "_"))]))
              ","
              (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `sub_sub)]
             "]")
            [])
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`mvpz []]
              [(Term.typeSpec
                ":"
                («term_=_»
                 (Term.typeAscription
                  "("
                  `p
                  ":"
                  [(Term.app `MvPolynomial [(termℕ "ℕ") (termℤ "ℤ")])]
                  ")")
                 "="
                 (Term.app `MvPolynomial.c [(coeNotation "↑" `p)])))]
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
                    [(Tactic.rwRule [] `eq_intCast) "," (Tactic.rwRule [] `Int.cast_ofNat)]
                    "]")
                   [])]))))))
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              []
              [(Term.typeSpec
                ":"
                (Term.forall
                 "∀"
                 [(Term.explicitBinder
                   "("
                   [`f]
                   [":" (Algebra.Hom.Ring.«term_→+*_» (termℤ "ℤ") " →+* " `k)]
                   []
                   ")")
                  (Term.explicitBinder "(" [`g] [":" (Term.arrow (termℕ "ℕ") "→" `k)] [] ")")]
                 []
                 ","
                 («term_=_» (Term.app `eval₂ [`f `g `p]) "=" (Term.app `f [`p]))))]
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Tactic.intros "intros" [])
                  []
                  (Tactic.rwSeq
                   "rw"
                   []
                   (Tactic.rwRuleSeq
                    "["
                    [(Tactic.rwRule [] `mvpz) "," (Tactic.rwRule [] `MvPolynomial.eval₂_C)]
                    "]")
                   [])]))))))
           []
           (Tactic.simp
            "simp"
            []
            []
            []
            ["["
             [(Tactic.simpLemma [] [] `witt_polynomial_eq_sum_C_mul_X_pow)
              ","
              (Tactic.simpLemma [] [] `aeval)
              ","
              (Tactic.simpLemma [] [] `eval₂_rename)
              ","
              (Tactic.simpLemma [] [] `this)
              ","
              (Tactic.simpLemma [] [] `mul_coeff)
              ","
              (Tactic.simpLemma [] [] `peval)
              ","
              (Tactic.simpLemma [] [] `map_nat_cast)
              ","
              (Tactic.simpLemma [] [] `map_add)
              ","
              (Tactic.simpLemma [] [] `map_pow)
              ","
              (Tactic.simpLemma [] [] `map_mul)]
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
            [(Tactic.simpLemma [] [] `poly_of_interest)
             ","
             (Tactic.simpLemma [] [] `peval)
             ","
             (Tactic.simpLemma [] [] `map_nat_cast)
             ","
             (Tactic.simpLemma [] [] `Matrix.head_cons)
             ","
             (Tactic.simpLemma [] [] `map_pow)
             ","
             (Tactic.simpLemma [] [] `Function.uncurry_apply_pair)
             ","
             (Tactic.simpLemma [] [] `aeval_X)
             ","
             (Tactic.simpLemma [] [] `Matrix.cons_val_one)
             ","
             (Tactic.simpLemma [] [] `map_mul)
             ","
             (Tactic.simpLemma [] [] `Matrix.cons_val_zero)
             ","
             (Tactic.simpLemma [] [] `map_sub)]
            "]"]
           [])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `sub_sub)
             ","
             (Tactic.rwRule
              []
              (Term.app `add_comm [(«term_*_» (Term.hole "_") "*" (Term.hole "_"))]))
             ","
             (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `sub_sub)]
            "]")
           [])
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`mvpz []]
             [(Term.typeSpec
               ":"
               («term_=_»
                (Term.typeAscription
                 "("
                 `p
                 ":"
                 [(Term.app `MvPolynomial [(termℕ "ℕ") (termℤ "ℤ")])]
                 ")")
                "="
                (Term.app `MvPolynomial.c [(coeNotation "↑" `p)])))]
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
                   [(Tactic.rwRule [] `eq_intCast) "," (Tactic.rwRule [] `Int.cast_ofNat)]
                   "]")
                  [])]))))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             []
             [(Term.typeSpec
               ":"
               (Term.forall
                "∀"
                [(Term.explicitBinder
                  "("
                  [`f]
                  [":" (Algebra.Hom.Ring.«term_→+*_» (termℤ "ℤ") " →+* " `k)]
                  []
                  ")")
                 (Term.explicitBinder "(" [`g] [":" (Term.arrow (termℕ "ℕ") "→" `k)] [] ")")]
                []
                ","
                («term_=_» (Term.app `eval₂ [`f `g `p]) "=" (Term.app `f [`p]))))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.intros "intros" [])
                 []
                 (Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule [] `mvpz) "," (Tactic.rwRule [] `MvPolynomial.eval₂_C)]
                   "]")
                  [])]))))))
          []
          (Tactic.simp
           "simp"
           []
           []
           []
           ["["
            [(Tactic.simpLemma [] [] `witt_polynomial_eq_sum_C_mul_X_pow)
             ","
             (Tactic.simpLemma [] [] `aeval)
             ","
             (Tactic.simpLemma [] [] `eval₂_rename)
             ","
             (Tactic.simpLemma [] [] `this)
             ","
             (Tactic.simpLemma [] [] `mul_coeff)
             ","
             (Tactic.simpLemma [] [] `peval)
             ","
             (Tactic.simpLemma [] [] `map_nat_cast)
             ","
             (Tactic.simpLemma [] [] `map_add)
             ","
             (Tactic.simpLemma [] [] `map_pow)
             ","
             (Tactic.simpLemma [] [] `map_mul)]
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
        [(Tactic.simpLemma [] [] `witt_polynomial_eq_sum_C_mul_X_pow)
         ","
         (Tactic.simpLemma [] [] `aeval)
         ","
         (Tactic.simpLemma [] [] `eval₂_rename)
         ","
         (Tactic.simpLemma [] [] `this)
         ","
         (Tactic.simpLemma [] [] `mul_coeff)
         ","
         (Tactic.simpLemma [] [] `peval)
         ","
         (Tactic.simpLemma [] [] `map_nat_cast)
         ","
         (Tactic.simpLemma [] [] `map_add)
         ","
         (Tactic.simpLemma [] [] `map_pow)
         ","
         (Tactic.simpLemma [] [] `map_mul)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `map_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `map_pow
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `map_add
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `map_nat_cast
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `peval
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_coeff
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
      `eval₂_rename
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `aeval
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `witt_polynomial_eq_sum_C_mul_X_pow
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
           (Term.forall
            "∀"
            [(Term.explicitBinder
              "("
              [`f]
              [":" (Algebra.Hom.Ring.«term_→+*_» (termℤ "ℤ") " →+* " `k)]
              []
              ")")
             (Term.explicitBinder "(" [`g] [":" (Term.arrow (termℕ "ℕ") "→" `k)] [] ")")]
            []
            ","
            («term_=_» (Term.app `eval₂ [`f `g `p]) "=" (Term.app `f [`p]))))]
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.intros "intros" [])
             []
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [] `mvpz) "," (Tactic.rwRule [] `MvPolynomial.eval₂_C)]
               "]")
              [])]))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.intros "intros" [])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `mvpz) "," (Tactic.rwRule [] `MvPolynomial.eval₂_C)]
            "]")
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `mvpz) "," (Tactic.rwRule [] `MvPolynomial.eval₂_C)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `MvPolynomial.eval₂_C
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mvpz
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.intros "intros" [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.forall
       "∀"
       [(Term.explicitBinder
         "("
         [`f]
         [":" (Algebra.Hom.Ring.«term_→+*_» (termℤ "ℤ") " →+* " `k)]
         []
         ")")
        (Term.explicitBinder "(" [`g] [":" (Term.arrow (termℕ "ℕ") "→" `k)] [] ")")]
       []
       ","
       («term_=_» (Term.app `eval₂ [`f `g `p]) "=" (Term.app `f [`p])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_» (Term.app `eval₂ [`f `g `p]) "=" (Term.app `f [`p]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `f [`p])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app `eval₂ [`f `g `p])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `eval₂
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.arrow (termℕ "ℕ") "→" `k)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k
[PrettyPrinter.parenthesize] ...precedences are 25 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
      (termℕ "ℕ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 25, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 25, (some 25, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Algebra.Hom.Ring.«term_→+*_» (termℤ "ℤ") " →+* " `k)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k
[PrettyPrinter.parenthesize] ...precedences are 25 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
      (termℤ "ℤ")
[PrettyPrinter.parenthesize] ...precedences are 26 >? 1024, (none, [anonymous]) <=? (some 25, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 25, (some 25, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`mvpz []]
         [(Term.typeSpec
           ":"
           («term_=_»
            (Term.typeAscription
             "("
             `p
             ":"
             [(Term.app `MvPolynomial [(termℕ "ℕ") (termℤ "ℤ")])]
             ")")
            "="
            (Term.app `MvPolynomial.c [(coeNotation "↑" `p)])))]
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
               [(Tactic.rwRule [] `eq_intCast) "," (Tactic.rwRule [] `Int.cast_ofNat)]
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
            [(Tactic.rwRule [] `eq_intCast) "," (Tactic.rwRule [] `Int.cast_ofNat)]
            "]")
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `eq_intCast) "," (Tactic.rwRule [] `Int.cast_ofNat)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Int.cast_ofNat
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `eq_intCast
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Term.typeAscription "(" `p ":" [(Term.app `MvPolynomial [(termℕ "ℕ") (termℤ "ℤ")])] ")")
       "="
       (Term.app `MvPolynomial.c [(coeNotation "↑" `p)]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `MvPolynomial.c [(coeNotation "↑" `p)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'coeNotation', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'coeNotation', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (coeNotation "↑" `p)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 1024,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `MvPolynomial.c
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.typeAscription "(" `p ":" [(Term.app `MvPolynomial [(termℕ "ℕ") (termℤ "ℤ")])] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `MvPolynomial [(termℕ "ℕ") (termℤ "ℤ")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'termℤ', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'termℤ', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (termℤ "ℤ")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'termℕ', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'termℕ', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (termℕ "ℕ")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `MvPolynomial
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `sub_sub)
         ","
         (Tactic.rwRule [] (Term.app `add_comm [(«term_*_» (Term.hole "_") "*" (Term.hole "_"))]))
         ","
         (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `sub_sub)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `sub_sub
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `add_comm [(«term_*_» (Term.hole "_") "*" (Term.hole "_"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_*_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_*_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_» (Term.hole "_") "*" (Term.hole "_"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_*_» (Term.hole "_") "*" (Term.hole "_"))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `add_comm
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `sub_sub
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
        [(Tactic.simpLemma [] [] `poly_of_interest)
         ","
         (Tactic.simpLemma [] [] `peval)
         ","
         (Tactic.simpLemma [] [] `map_nat_cast)
         ","
         (Tactic.simpLemma [] [] `Matrix.head_cons)
         ","
         (Tactic.simpLemma [] [] `map_pow)
         ","
         (Tactic.simpLemma [] [] `Function.uncurry_apply_pair)
         ","
         (Tactic.simpLemma [] [] `aeval_X)
         ","
         (Tactic.simpLemma [] [] `Matrix.cons_val_one)
         ","
         (Tactic.simpLemma [] [] `map_mul)
         ","
         (Tactic.simpLemma [] [] `Matrix.cons_val_zero)
         ","
         (Tactic.simpLemma [] [] `map_sub)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `map_sub
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Matrix.cons_val_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `map_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Matrix.cons_val_one
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `aeval_X
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Function.uncurry_apply_pair
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `map_pow
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Matrix.head_cons
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `map_nat_cast
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `peval
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `poly_of_interest
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app
        `peval
        [(Term.app `polyOfInterest [`p `n])
         (Matrix.Data.Fin.VecNotation.«term![_,»
          "!["
          [(Term.fun "fun" (Term.basicFun [`i] [] "=>" (Term.app (Term.proj `x "." `coeff) [`i])))
           ","
           (Term.fun "fun" (Term.basicFun [`i] [] "=>" (Term.app (Term.proj `y "." `coeff) [`i])))]
          "]")])
       "="
       («term_-_»
        («term_-_»
         («term_+_»
          (Term.app (Term.proj («term_*_» `x "*" `y) "." `coeff) [(«term_+_» `n "+" (num "1"))])
          "+"
          («term_*_»
           («term_*_»
            («term_^_» `p "^" («term_+_» `n "+" (num "1")))
            "*"
            (Term.app (Term.proj `x "." `coeff) [(«term_+_» `n "+" (num "1"))]))
           "*"
           (Term.app (Term.proj `y "." `coeff) [(«term_+_» `n "+" (num "1"))])))
         "-"
         («term_*_»
          (Term.app (Term.proj `y "." `coeff) [(«term_+_» `n "+" (num "1"))])
          "*"
          (BigOperators.Algebra.BigOperators.Basic.finset.sum
           "∑"
           (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
           " in "
           (Term.app `range [(«term_+_» («term_+_» `n "+" (num "1")) "+" (num "1"))])
           ", "
           («term_*_»
            («term_^_» `p "^" `i)
            "*"
            («term_^_»
             (Term.app (Term.proj `x "." `coeff) [`i])
             "^"
             («term_^_» `p "^" («term_-_» («term_+_» `n "+" (num "1")) "-" `i)))))))
        "-"
        («term_*_»
         (Term.app (Term.proj `x "." `coeff) [(«term_+_» `n "+" (num "1"))])
         "*"
         (BigOperators.Algebra.BigOperators.Basic.finset.sum
          "∑"
          (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
          " in "
          (Term.app `range [(«term_+_» («term_+_» `n "+" (num "1")) "+" (num "1"))])
          ", "
          («term_*_»
           («term_^_» `p "^" `i)
           "*"
           («term_^_»
            (Term.app (Term.proj `y "." `coeff) [`i])
            "^"
            («term_^_» `p "^" («term_-_» («term_+_» `n "+" (num "1")) "-" `i))))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_-_»
       («term_-_»
        («term_+_»
         (Term.app (Term.proj («term_*_» `x "*" `y) "." `coeff) [(«term_+_» `n "+" (num "1"))])
         "+"
         («term_*_»
          («term_*_»
           («term_^_» `p "^" («term_+_» `n "+" (num "1")))
           "*"
           (Term.app (Term.proj `x "." `coeff) [(«term_+_» `n "+" (num "1"))]))
          "*"
          (Term.app (Term.proj `y "." `coeff) [(«term_+_» `n "+" (num "1"))])))
        "-"
        («term_*_»
         (Term.app (Term.proj `y "." `coeff) [(«term_+_» `n "+" (num "1"))])
         "*"
         (BigOperators.Algebra.BigOperators.Basic.finset.sum
          "∑"
          (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
          " in "
          (Term.app `range [(«term_+_» («term_+_» `n "+" (num "1")) "+" (num "1"))])
          ", "
          («term_*_»
           («term_^_» `p "^" `i)
           "*"
           («term_^_»
            (Term.app (Term.proj `x "." `coeff) [`i])
            "^"
            («term_^_» `p "^" («term_-_» («term_+_» `n "+" (num "1")) "-" `i)))))))
       "-"
       («term_*_»
        (Term.app (Term.proj `x "." `coeff) [(«term_+_» `n "+" (num "1"))])
        "*"
        (BigOperators.Algebra.BigOperators.Basic.finset.sum
         "∑"
         (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
         " in "
         (Term.app `range [(«term_+_» («term_+_» `n "+" (num "1")) "+" (num "1"))])
         ", "
         («term_*_»
          («term_^_» `p "^" `i)
          "*"
          («term_^_»
           (Term.app (Term.proj `y "." `coeff) [`i])
           "^"
           («term_^_» `p "^" («term_-_» («term_+_» `n "+" (num "1")) "-" `i)))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_»
       (Term.app (Term.proj `x "." `coeff) [(«term_+_» `n "+" (num "1"))])
       "*"
       (BigOperators.Algebra.BigOperators.Basic.finset.sum
        "∑"
        (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
        " in "
        (Term.app `range [(«term_+_» («term_+_» `n "+" (num "1")) "+" (num "1"))])
        ", "
        («term_*_»
         («term_^_» `p "^" `i)
         "*"
         («term_^_»
          (Term.app (Term.proj `y "." `coeff) [`i])
          "^"
          («term_^_» `p "^" («term_-_» («term_+_» `n "+" (num "1")) "-" `i))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (BigOperators.Algebra.BigOperators.Basic.finset.sum
       "∑"
       (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
       " in "
       (Term.app `range [(«term_+_» («term_+_» `n "+" (num "1")) "+" (num "1"))])
       ", "
       («term_*_»
        («term_^_» `p "^" `i)
        "*"
        («term_^_»
         (Term.app (Term.proj `y "." `coeff) [`i])
         "^"
         («term_^_» `p "^" («term_-_» («term_+_» `n "+" (num "1")) "-" `i)))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_»
       («term_^_» `p "^" `i)
       "*"
       («term_^_»
        (Term.app (Term.proj `y "." `coeff) [`i])
        "^"
        («term_^_» `p "^" («term_-_» («term_+_» `n "+" (num "1")) "-" `i))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_»
       (Term.app (Term.proj `y "." `coeff) [`i])
       "^"
       («term_^_» `p "^" («term_-_» («term_+_» `n "+" (num "1")) "-" `i)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_» `p "^" («term_-_» («term_+_» `n "+" (num "1")) "-" `i))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_-_» («term_+_» `n "+" (num "1")) "-" `i)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      («term_+_» `n "+" (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `n
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 65 >? 65, (some 66, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_-_» («term_+_» `n "+" (num "1")) "-" `i)
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Term.app (Term.proj `y "." `coeff) [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `y "." `coeff)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `y
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1022, (some 1023, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      («term_^_» `p "^" `i)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 80, (some 80, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `range [(«term_+_» («term_+_» `n "+" (num "1")) "+" (num "1"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_+_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_+_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_» («term_+_» `n "+" (num "1")) "+" (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      («term_+_» `n "+" (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `n
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 65 >? 65, (some 66, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_+_» («term_+_» `n "+" (num "1")) "+" (num "1"))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `range
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (Term.app (Term.proj `x "." `coeff) [(«term_+_» `n "+" (num "1"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_+_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_+_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_» `n "+" (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `n
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_+_» `n "+" (num "1")) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `x "." `coeff)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1022, (some 1023, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 70, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      («term_-_»
       («term_+_»
        (Term.app (Term.proj («term_*_» `x "*" `y) "." `coeff) [(«term_+_» `n "+" (num "1"))])
        "+"
        («term_*_»
         («term_*_»
          («term_^_» `p "^" («term_+_» `n "+" (num "1")))
          "*"
          (Term.app (Term.proj `x "." `coeff) [(«term_+_» `n "+" (num "1"))]))
         "*"
         (Term.app (Term.proj `y "." `coeff) [(«term_+_» `n "+" (num "1"))])))
       "-"
       («term_*_»
        (Term.app (Term.proj `y "." `coeff) [(«term_+_» `n "+" (num "1"))])
        "*"
        (BigOperators.Algebra.BigOperators.Basic.finset.sum
         "∑"
         (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
         " in "
         (Term.app `range [(«term_+_» («term_+_» `n "+" (num "1")) "+" (num "1"))])
         ", "
         («term_*_»
          («term_^_» `p "^" `i)
          "*"
          («term_^_»
           (Term.app (Term.proj `x "." `coeff) [`i])
           "^"
           («term_^_» `p "^" («term_-_» («term_+_» `n "+" (num "1")) "-" `i)))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_»
       (Term.app (Term.proj `y "." `coeff) [(«term_+_» `n "+" (num "1"))])
       "*"
       (BigOperators.Algebra.BigOperators.Basic.finset.sum
        "∑"
        (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
        " in "
        (Term.app `range [(«term_+_» («term_+_» `n "+" (num "1")) "+" (num "1"))])
        ", "
        («term_*_»
         («term_^_» `p "^" `i)
         "*"
         («term_^_»
          (Term.app (Term.proj `x "." `coeff) [`i])
          "^"
          («term_^_» `p "^" («term_-_» («term_+_» `n "+" (num "1")) "-" `i))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (BigOperators.Algebra.BigOperators.Basic.finset.sum
       "∑"
       (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
       " in "
       (Term.app `range [(«term_+_» («term_+_» `n "+" (num "1")) "+" (num "1"))])
       ", "
       («term_*_»
        («term_^_» `p "^" `i)
        "*"
        («term_^_»
         (Term.app (Term.proj `x "." `coeff) [`i])
         "^"
         («term_^_» `p "^" («term_-_» («term_+_» `n "+" (num "1")) "-" `i)))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_»
       («term_^_» `p "^" `i)
       "*"
       («term_^_»
        (Term.app (Term.proj `x "." `coeff) [`i])
        "^"
        («term_^_» `p "^" («term_-_» («term_+_» `n "+" (num "1")) "-" `i))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_»
       (Term.app (Term.proj `x "." `coeff) [`i])
       "^"
       («term_^_» `p "^" («term_-_» («term_+_» `n "+" (num "1")) "-" `i)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_» `p "^" («term_-_» («term_+_» `n "+" (num "1")) "-" `i))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_-_» («term_+_» `n "+" (num "1")) "-" `i)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      («term_+_» `n "+" (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `n
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 65 >? 65, (some 66, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_-_» («term_+_» `n "+" (num "1")) "-" `i)
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Term.app (Term.proj `x "." `coeff) [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
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
[PrettyPrinter.parenthesize] ...precedences are 71 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      («term_^_» `p "^" `i)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 80, (some 80, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `range [(«term_+_» («term_+_» `n "+" (num "1")) "+" (num "1"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_+_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_+_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_» («term_+_» `n "+" (num "1")) "+" (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      («term_+_» `n "+" (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `n
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 65 >? 65, (some 66, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_+_» («term_+_» `n "+" (num "1")) "+" (num "1"))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `range
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (Term.app (Term.proj `y "." `coeff) [(«term_+_» `n "+" (num "1"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_+_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_+_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_» `n "+" (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `n
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_+_» `n "+" (num "1")) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `y "." `coeff)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `y
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1022, (some 1023, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 70, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      («term_+_»
       (Term.app (Term.proj («term_*_» `x "*" `y) "." `coeff) [(«term_+_» `n "+" (num "1"))])
       "+"
       («term_*_»
        («term_*_»
         («term_^_» `p "^" («term_+_» `n "+" (num "1")))
         "*"
         (Term.app (Term.proj `x "." `coeff) [(«term_+_» `n "+" (num "1"))]))
        "*"
        (Term.app (Term.proj `y "." `coeff) [(«term_+_» `n "+" (num "1"))])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_»
       («term_*_»
        («term_^_» `p "^" («term_+_» `n "+" (num "1")))
        "*"
        (Term.app (Term.proj `x "." `coeff) [(«term_+_» `n "+" (num "1"))]))
       "*"
       (Term.app (Term.proj `y "." `coeff) [(«term_+_» `n "+" (num "1"))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj `y "." `coeff) [(«term_+_» `n "+" (num "1"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_+_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_+_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_» `n "+" (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `n
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_+_» `n "+" (num "1")) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `y "." `coeff)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `y
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      («term_*_»
       («term_^_» `p "^" («term_+_» `n "+" (num "1")))
       "*"
       (Term.app (Term.proj `x "." `coeff) [(«term_+_» `n "+" (num "1"))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj `x "." `coeff) [(«term_+_» `n "+" (num "1"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_+_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_+_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_» `n "+" (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `n
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_+_» `n "+" (num "1")) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `x "." `coeff)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      («term_^_» `p "^" («term_+_» `n "+" (num "1")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_» `n "+" (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `n
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_+_» `n "+" (num "1")) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 80, (some 80, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 70, (some 71, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      (Term.app (Term.proj («term_*_» `x "*" `y) "." `coeff) [(«term_+_» `n "+" (num "1"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_+_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_+_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_» `n "+" (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `n
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_+_» `n "+" (num "1")) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj («term_*_» `x "*" `y) "." `coeff)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      («term_*_» `x "*" `y)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 70, (some 71, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_*_» `x "*" `y) ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1022, (some 1023, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 65 >? 65, (some 66, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 65 >? 65, (some 0, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_-_»
      («term_+_»
       (Term.app
        (Term.proj (Term.paren "(" («term_*_» `x "*" `y) ")") "." `coeff)
        [(Term.paren "(" («term_+_» `n "+" (num "1")) ")")])
       "+"
       («term_*_»
        («term_*_»
         («term_^_» `p "^" (Term.paren "(" («term_+_» `n "+" (num "1")) ")"))
         "*"
         (Term.app (Term.proj `x "." `coeff) [(Term.paren "(" («term_+_» `n "+" (num "1")) ")")]))
        "*"
        (Term.app (Term.proj `y "." `coeff) [(Term.paren "(" («term_+_» `n "+" (num "1")) ")")])))
      "-"
      («term_*_»
       (Term.app (Term.proj `y "." `coeff) [(Term.paren "(" («term_+_» `n "+" (num "1")) ")")])
       "*"
       (BigOperators.Algebra.BigOperators.Basic.finset.sum
        "∑"
        (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
        " in "
        (Term.app
         `range
         [(Term.paren "(" («term_+_» («term_+_» `n "+" (num "1")) "+" (num "1")) ")")])
        ", "
        («term_*_»
         («term_^_» `p "^" `i)
         "*"
         («term_^_»
          (Term.app (Term.proj `x "." `coeff) [`i])
          "^"
          («term_^_»
           `p
           "^"
           (Term.paren "(" («term_-_» («term_+_» `n "+" (num "1")) "-" `i) ")")))))))
     ")")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 65, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app
       `peval
       [(Term.app `polyOfInterest [`p `n])
        (Matrix.Data.Fin.VecNotation.«term![_,»
         "!["
         [(Term.fun "fun" (Term.basicFun [`i] [] "=>" (Term.app (Term.proj `x "." `coeff) [`i])))
          ","
          (Term.fun "fun" (Term.basicFun [`i] [] "=>" (Term.app (Term.proj `y "." `coeff) [`i])))]
         "]")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Matrix.Data.Fin.VecNotation.«term![_,»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Matrix.Data.Fin.VecNotation.«term![_,»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Matrix.Data.Fin.VecNotation.«term![_,»
       "!["
       [(Term.fun "fun" (Term.basicFun [`i] [] "=>" (Term.app (Term.proj `x "." `coeff) [`i])))
        ","
        (Term.fun "fun" (Term.basicFun [`i] [] "=>" (Term.app (Term.proj `y "." `coeff) [`i])))]
       "]")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun "fun" (Term.basicFun [`i] [] "=>" (Term.app (Term.proj `y "." `coeff) [`i])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj `y "." `coeff) [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `y "." `coeff)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `y
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun "fun" (Term.basicFun [`i] [] "=>" (Term.app (Term.proj `x "." `coeff) [`i])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj `x "." `coeff) [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `x "." `coeff)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.app `polyOfInterest [`p `n])
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
      `polyOfInterest
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `polyOfInterest [`p `n]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `peval
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 0, term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (WittVector.RingTheory.WittVector.MulCoeff.term𝕎 "𝕎") [`k])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (WittVector.RingTheory.WittVector.MulCoeff.term𝕎 "𝕎")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'WittVector.RingTheory.WittVector.MulCoeff.term𝕎', expected 'WittVector.RingTheory.WittVector.MulCoeff.term𝕎._@.RingTheory.WittVector.MulCoeff._hyg.6'
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
  peval_poly_of_interest
  ( n : ℕ ) ( x y : 𝕎 k )
    :
      peval polyOfInterest p n ![ fun i => x . coeff i , fun i => y . coeff i ]
        =
        x * y . coeff n + 1 + p ^ n + 1 * x . coeff n + 1 * y . coeff n + 1
            -
            y . coeff n + 1 * ∑ i in range n + 1 + 1 , p ^ i * x . coeff i ^ p ^ n + 1 - i
          -
          x . coeff n + 1 * ∑ i in range n + 1 + 1 , p ^ i * y . coeff i ^ p ^ n + 1 - i
  :=
    by
      simp
          only
          [
            poly_of_interest
              ,
              peval
              ,
              map_nat_cast
              ,
              Matrix.head_cons
              ,
              map_pow
              ,
              Function.uncurry_apply_pair
              ,
              aeval_X
              ,
              Matrix.cons_val_one
              ,
              map_mul
              ,
              Matrix.cons_val_zero
              ,
              map_sub
            ]
        rw [ sub_sub , add_comm _ * _ , ← sub_sub ]
        have
          mvpz
            : ( p : MvPolynomial ℕ ℤ ) = MvPolynomial.c ↑ p
            :=
            by rw [ eq_intCast , Int.cast_ofNat ]
        have
          : ∀ ( f : ℤ →+* k ) ( g : ℕ → k ) , eval₂ f g p = f p
            :=
            by intros rw [ mvpz , MvPolynomial.eval₂_C ]
        simp
          [
            witt_polynomial_eq_sum_C_mul_X_pow
              ,
              aeval
              ,
              eval₂_rename
              ,
              this
              ,
              mul_coeff
              ,
              peval
              ,
              map_nat_cast
              ,
              map_add
              ,
              map_pow
              ,
              map_mul
            ]
#align witt_vector.peval_poly_of_interest WittVector.peval_poly_of_interest

variable [CharP k p]

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment "/--" "The characteristic `p` version of `peval_poly_of_interest` -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `peval_poly_of_interest' [])
      (Command.declSig
       [(Term.explicitBinder "(" [`n] [":" (termℕ "ℕ")] [] ")")
        (Term.explicitBinder
         "("
         [`x `y]
         [":" (Term.app (WittVector.RingTheory.WittVector.MulCoeff.term𝕎 "𝕎") [`k])]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app
          `peval
          [(Term.app `polyOfInterest [`p `n])
           (Matrix.Data.Fin.VecNotation.«term![_,»
            "!["
            [(Term.fun "fun" (Term.basicFun [`i] [] "=>" (Term.app (Term.proj `x "." `coeff) [`i])))
             ","
             (Term.fun
              "fun"
              (Term.basicFun [`i] [] "=>" (Term.app (Term.proj `y "." `coeff) [`i])))]
            "]")])
         "="
         («term_-_»
          («term_-_»
           (Term.app (Term.proj («term_*_» `x "*" `y) "." `coeff) [(«term_+_» `n "+" (num "1"))])
           "-"
           («term_*_»
            (Term.app (Term.proj `y "." `coeff) [(«term_+_» `n "+" (num "1"))])
            "*"
            («term_^_»
             (Term.app (Term.proj `x "." `coeff) [(num "0")])
             "^"
             («term_^_» `p "^" («term_+_» `n "+" (num "1"))))))
          "-"
          («term_*_»
           (Term.app (Term.proj `x "." `coeff) [(«term_+_» `n "+" (num "1"))])
           "*"
           («term_^_»
            (Term.app (Term.proj `y "." `coeff) [(num "0")])
            "^"
            («term_^_» `p "^" («term_+_» `n "+" (num "1")))))))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `peval_poly_of_interest)] "]")
            [])
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              []
              [(Term.typeSpec
                ":"
                («term_=_» (Term.typeAscription "(" `p ":" [`k] ")") "=" (num "0")))]
              ":="
              (Term.app `CharP.cast_eq_zero [`k `p]))))
           []
           (Tactic.simp
            "simp"
            []
            []
            ["only"]
            ["["
             [(Tactic.simpLemma [] [] `this)
              ","
              (Tactic.simpLemma [] [] `add_zero)
              ","
              (Tactic.simpLemma [] [] `zero_mul)
              ","
              (Tactic.simpLemma [] [] `Nat.succ_ne_zero)
              ","
              (Tactic.simpLemma [] [] `Ne.def)
              ","
              (Tactic.simpLemma [] [] `not_false_iff)
              ","
              (Tactic.simpLemma [] [] `zero_pow')]
             "]"]
            [])
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`sum_zero_pow_mul_pow_p []]
              [(Term.typeSpec
                ":"
                (Term.forall
                 "∀"
                 [`y]
                 [(Term.typeSpec
                   ":"
                   (Term.app (WittVector.RingTheory.WittVector.MulCoeff.term𝕎 "𝕎") [`k]))]
                 ","
                 («term_=_»
                  (BigOperators.Algebra.BigOperators.Basic.finset.sum
                   "∑"
                   (Std.ExtendedBinder.extBinders
                    (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) [(group ":" (termℕ "ℕ"))]))
                   " in "
                   (Term.app `range [(«term_+_» («term_+_» `n "+" (num "1")) "+" (num "1"))])
                   ", "
                   («term_*_»
                    («term_^_» (num "0") "^" `x)
                    "*"
                    («term_^_»
                     (Term.app (Term.proj `y "." `coeff) [`x])
                     "^"
                     («term_^_» `p "^" («term_-_» («term_+_» `n "+" (num "1")) "-" `x)))))
                  "="
                  («term_^_»
                   (Term.app (Term.proj `y "." `coeff) [(num "0")])
                   "^"
                   («term_^_» `p "^" («term_+_» `n "+" (num "1")))))))]
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Tactic.intro "intro" [`y])
                  []
                  (Tactic.rwSeq
                   "rw"
                   []
                   (Tactic.rwRuleSeq
                    "["
                    [(Tactic.rwRule [] (Term.app `Finset.sum_eq_single_of_mem [(num "0")]))]
                    "]")
                   [])
                  []
                  (tactic__
                   (cdotTk (patternIgnore (token.«· » "·")))
                   [(Tactic.simp "simp" [] [] [] [] [])])
                  []
                  (tactic__
                   (cdotTk (patternIgnore (token.«· » "·")))
                   [(Tactic.simp "simp" [] [] [] [] [])])
                  []
                  (tactic__
                   (cdotTk (patternIgnore (token.«· » "·")))
                   [(Tactic.intro "intro" [`j (Term.hole "_") `hj])
                    []
                    (Tactic.simp
                     "simp"
                     []
                     []
                     []
                     ["["
                      [(Tactic.simpLemma
                        []
                        []
                        (Term.app `zero_pow [(Term.app `zero_lt_iff.mpr [`hj])]))]
                      "]"]
                     [])])]))))))
           []
           (Tactic.«tactic_<;>_»
            (Tactic.congr "congr" [])
            "<;>"
            (Tactic.apply "apply" `sum_zero_pow_mul_pow_p))])))
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
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `peval_poly_of_interest)] "]")
           [])
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             []
             [(Term.typeSpec
               ":"
               («term_=_» (Term.typeAscription "(" `p ":" [`k] ")") "=" (num "0")))]
             ":="
             (Term.app `CharP.cast_eq_zero [`k `p]))))
          []
          (Tactic.simp
           "simp"
           []
           []
           ["only"]
           ["["
            [(Tactic.simpLemma [] [] `this)
             ","
             (Tactic.simpLemma [] [] `add_zero)
             ","
             (Tactic.simpLemma [] [] `zero_mul)
             ","
             (Tactic.simpLemma [] [] `Nat.succ_ne_zero)
             ","
             (Tactic.simpLemma [] [] `Ne.def)
             ","
             (Tactic.simpLemma [] [] `not_false_iff)
             ","
             (Tactic.simpLemma [] [] `zero_pow')]
            "]"]
           [])
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`sum_zero_pow_mul_pow_p []]
             [(Term.typeSpec
               ":"
               (Term.forall
                "∀"
                [`y]
                [(Term.typeSpec
                  ":"
                  (Term.app (WittVector.RingTheory.WittVector.MulCoeff.term𝕎 "𝕎") [`k]))]
                ","
                («term_=_»
                 (BigOperators.Algebra.BigOperators.Basic.finset.sum
                  "∑"
                  (Std.ExtendedBinder.extBinders
                   (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) [(group ":" (termℕ "ℕ"))]))
                  " in "
                  (Term.app `range [(«term_+_» («term_+_» `n "+" (num "1")) "+" (num "1"))])
                  ", "
                  («term_*_»
                   («term_^_» (num "0") "^" `x)
                   "*"
                   («term_^_»
                    (Term.app (Term.proj `y "." `coeff) [`x])
                    "^"
                    («term_^_» `p "^" («term_-_» («term_+_» `n "+" (num "1")) "-" `x)))))
                 "="
                 («term_^_»
                  (Term.app (Term.proj `y "." `coeff) [(num "0")])
                  "^"
                  («term_^_» `p "^" («term_+_» `n "+" (num "1")))))))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.intro "intro" [`y])
                 []
                 (Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule [] (Term.app `Finset.sum_eq_single_of_mem [(num "0")]))]
                   "]")
                  [])
                 []
                 (tactic__
                  (cdotTk (patternIgnore (token.«· » "·")))
                  [(Tactic.simp "simp" [] [] [] [] [])])
                 []
                 (tactic__
                  (cdotTk (patternIgnore (token.«· » "·")))
                  [(Tactic.simp "simp" [] [] [] [] [])])
                 []
                 (tactic__
                  (cdotTk (patternIgnore (token.«· » "·")))
                  [(Tactic.intro "intro" [`j (Term.hole "_") `hj])
                   []
                   (Tactic.simp
                    "simp"
                    []
                    []
                    []
                    ["["
                     [(Tactic.simpLemma
                       []
                       []
                       (Term.app `zero_pow [(Term.app `zero_lt_iff.mpr [`hj])]))]
                     "]"]
                    [])])]))))))
          []
          (Tactic.«tactic_<;>_»
           (Tactic.congr "congr" [])
           "<;>"
           (Tactic.apply "apply" `sum_zero_pow_mul_pow_p))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.«tactic_<;>_»
       (Tactic.congr "congr" [])
       "<;>"
       (Tactic.apply "apply" `sum_zero_pow_mul_pow_p))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.apply "apply" `sum_zero_pow_mul_pow_p)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `sum_zero_pow_mul_pow_p
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 2 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
      (Tactic.congr "congr" [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`sum_zero_pow_mul_pow_p []]
         [(Term.typeSpec
           ":"
           (Term.forall
            "∀"
            [`y]
            [(Term.typeSpec
              ":"
              (Term.app (WittVector.RingTheory.WittVector.MulCoeff.term𝕎 "𝕎") [`k]))]
            ","
            («term_=_»
             (BigOperators.Algebra.BigOperators.Basic.finset.sum
              "∑"
              (Std.ExtendedBinder.extBinders
               (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) [(group ":" (termℕ "ℕ"))]))
              " in "
              (Term.app `range [(«term_+_» («term_+_» `n "+" (num "1")) "+" (num "1"))])
              ", "
              («term_*_»
               («term_^_» (num "0") "^" `x)
               "*"
               («term_^_»
                (Term.app (Term.proj `y "." `coeff) [`x])
                "^"
                («term_^_» `p "^" («term_-_» («term_+_» `n "+" (num "1")) "-" `x)))))
             "="
             («term_^_»
              (Term.app (Term.proj `y "." `coeff) [(num "0")])
              "^"
              («term_^_» `p "^" («term_+_» `n "+" (num "1")))))))]
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.intro "intro" [`y])
             []
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [] (Term.app `Finset.sum_eq_single_of_mem [(num "0")]))]
               "]")
              [])
             []
             (tactic__
              (cdotTk (patternIgnore (token.«· » "·")))
              [(Tactic.simp "simp" [] [] [] [] [])])
             []
             (tactic__
              (cdotTk (patternIgnore (token.«· » "·")))
              [(Tactic.simp "simp" [] [] [] [] [])])
             []
             (tactic__
              (cdotTk (patternIgnore (token.«· » "·")))
              [(Tactic.intro "intro" [`j (Term.hole "_") `hj])
               []
               (Tactic.simp
                "simp"
                []
                []
                []
                ["["
                 [(Tactic.simpLemma [] [] (Term.app `zero_pow [(Term.app `zero_lt_iff.mpr [`hj])]))]
                 "]"]
                [])])]))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.intro "intro" [`y])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] (Term.app `Finset.sum_eq_single_of_mem [(num "0")]))]
            "]")
           [])
          []
          (tactic__ (cdotTk (patternIgnore (token.«· » "·"))) [(Tactic.simp "simp" [] [] [] [] [])])
          []
          (tactic__ (cdotTk (patternIgnore (token.«· » "·"))) [(Tactic.simp "simp" [] [] [] [] [])])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.intro "intro" [`j (Term.hole "_") `hj])
            []
            (Tactic.simp
             "simp"
             []
             []
             []
             ["["
              [(Tactic.simpLemma [] [] (Term.app `zero_pow [(Term.app `zero_lt_iff.mpr [`hj])]))]
              "]"]
             [])])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.intro "intro" [`j (Term.hole "_") `hj])
        []
        (Tactic.simp
         "simp"
         []
         []
         []
         ["["
          [(Tactic.simpLemma [] [] (Term.app `zero_pow [(Term.app `zero_lt_iff.mpr [`hj])]))]
          "]"]
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       []
       ["[" [(Tactic.simpLemma [] [] (Term.app `zero_pow [(Term.app `zero_lt_iff.mpr [`hj])]))] "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `zero_pow [(Term.app `zero_lt_iff.mpr [`hj])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `zero_lt_iff.mpr [`hj])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hj
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `zero_lt_iff.mpr
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `zero_lt_iff.mpr [`hj]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `zero_pow
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.intro "intro" [`j (Term.hole "_") `hj])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hj
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      `j
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__ (cdotTk (patternIgnore (token.«· » "·"))) [(Tactic.simp "simp" [] [] [] [] [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] [] [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__ (cdotTk (patternIgnore (token.«· » "·"))) [(Tactic.simp "simp" [] [] [] [] [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] [] [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] (Term.app `Finset.sum_eq_single_of_mem [(num "0")]))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Finset.sum_eq_single_of_mem [(num "0")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Finset.sum_eq_single_of_mem
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.intro "intro" [`y])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.forall
       "∀"
       [`y]
       [(Term.typeSpec ":" (Term.app (WittVector.RingTheory.WittVector.MulCoeff.term𝕎 "𝕎") [`k]))]
       ","
       («term_=_»
        (BigOperators.Algebra.BigOperators.Basic.finset.sum
         "∑"
         (Std.ExtendedBinder.extBinders
          (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) [(group ":" (termℕ "ℕ"))]))
         " in "
         (Term.app `range [(«term_+_» («term_+_» `n "+" (num "1")) "+" (num "1"))])
         ", "
         («term_*_»
          («term_^_» (num "0") "^" `x)
          "*"
          («term_^_»
           (Term.app (Term.proj `y "." `coeff) [`x])
           "^"
           («term_^_» `p "^" («term_-_» («term_+_» `n "+" (num "1")) "-" `x)))))
        "="
        («term_^_»
         (Term.app (Term.proj `y "." `coeff) [(num "0")])
         "^"
         («term_^_» `p "^" («term_+_» `n "+" (num "1"))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (BigOperators.Algebra.BigOperators.Basic.finset.sum
        "∑"
        (Std.ExtendedBinder.extBinders
         (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) [(group ":" (termℕ "ℕ"))]))
        " in "
        (Term.app `range [(«term_+_» («term_+_» `n "+" (num "1")) "+" (num "1"))])
        ", "
        («term_*_»
         («term_^_» (num "0") "^" `x)
         "*"
         («term_^_»
          (Term.app (Term.proj `y "." `coeff) [`x])
          "^"
          («term_^_» `p "^" («term_-_» («term_+_» `n "+" (num "1")) "-" `x)))))
       "="
       («term_^_»
        (Term.app (Term.proj `y "." `coeff) [(num "0")])
        "^"
        («term_^_» `p "^" («term_+_» `n "+" (num "1")))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_»
       (Term.app (Term.proj `y "." `coeff) [(num "0")])
       "^"
       («term_^_» `p "^" («term_+_» `n "+" (num "1"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_» `p "^" («term_+_» `n "+" (num "1")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_» `n "+" (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `n
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_+_» `n "+" (num "1")) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Term.app (Term.proj `y "." `coeff) [(num "0")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `y "." `coeff)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `y
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1022, (some 1023, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (BigOperators.Algebra.BigOperators.Basic.finset.sum
       "∑"
       (Std.ExtendedBinder.extBinders
        (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) [(group ":" (termℕ "ℕ"))]))
       " in "
       (Term.app `range [(«term_+_» («term_+_» `n "+" (num "1")) "+" (num "1"))])
       ", "
       («term_*_»
        («term_^_» (num "0") "^" `x)
        "*"
        («term_^_»
         (Term.app (Term.proj `y "." `coeff) [`x])
         "^"
         («term_^_» `p "^" («term_-_» («term_+_» `n "+" (num "1")) "-" `x)))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_»
       («term_^_» (num "0") "^" `x)
       "*"
       («term_^_»
        (Term.app (Term.proj `y "." `coeff) [`x])
        "^"
        («term_^_» `p "^" («term_-_» («term_+_» `n "+" (num "1")) "-" `x))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_»
       (Term.app (Term.proj `y "." `coeff) [`x])
       "^"
       («term_^_» `p "^" («term_-_» («term_+_» `n "+" (num "1")) "-" `x)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_» `p "^" («term_-_» («term_+_» `n "+" (num "1")) "-" `x))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_-_» («term_+_» `n "+" (num "1")) "-" `x)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      («term_+_» `n "+" (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `n
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 65 >? 65, (some 66, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_-_» («term_+_» `n "+" (num "1")) "-" `x)
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Term.app (Term.proj `y "." `coeff) [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `y "." `coeff)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `y
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1022, (some 1023, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      («term_^_» (num "0") "^" `x)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 80, (some 80, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `range [(«term_+_» («term_+_» `n "+" (num "1")) "+" (num "1"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_+_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_+_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_» («term_+_» `n "+" (num "1")) "+" (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      («term_+_» `n "+" (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `n
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 65 >? 65, (some 66, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_+_» («term_+_» `n "+" (num "1")) "+" (num "1"))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `range
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (termℕ "ℕ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 0, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (BigOperators.Algebra.BigOperators.Basic.finset.sum
      "∑"
      (Std.ExtendedBinder.extBinders
       (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) [(group ":" (termℕ "ℕ"))]))
      " in "
      (Term.app
       `range
       [(Term.paren "(" («term_+_» («term_+_» `n "+" (num "1")) "+" (num "1")) ")")])
      ", "
      («term_*_»
       («term_^_» (num "0") "^" `x)
       "*"
       («term_^_»
        (Term.app (Term.proj `y "." `coeff) [`x])
        "^"
        («term_^_» `p "^" (Term.paren "(" («term_-_» («term_+_» `n "+" (num "1")) "-" `x) ")")))))
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (WittVector.RingTheory.WittVector.MulCoeff.term𝕎 "𝕎") [`k])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (WittVector.RingTheory.WittVector.MulCoeff.term𝕎 "𝕎")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'WittVector.RingTheory.WittVector.MulCoeff.term𝕎', expected 'WittVector.RingTheory.WittVector.MulCoeff.term𝕎._@.RingTheory.WittVector.MulCoeff._hyg.6'
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
/-- The characteristic `p` version of `peval_poly_of_interest` -/
  theorem
    peval_poly_of_interest'
    ( n : ℕ ) ( x y : 𝕎 k )
      :
        peval polyOfInterest p n ![ fun i => x . coeff i , fun i => y . coeff i ]
          =
          x * y . coeff n + 1 - y . coeff n + 1 * x . coeff 0 ^ p ^ n + 1
            -
            x . coeff n + 1 * y . coeff 0 ^ p ^ n + 1
    :=
      by
        rw [ peval_poly_of_interest ]
          have : ( p : k ) = 0 := CharP.cast_eq_zero k p
          simp
            only
            [ this , add_zero , zero_mul , Nat.succ_ne_zero , Ne.def , not_false_iff , zero_pow' ]
          have
            sum_zero_pow_mul_pow_p
              :
                ∀
                  y
                  : 𝕎 k
                  ,
                  ∑ x : ℕ in range n + 1 + 1 , 0 ^ x * y . coeff x ^ p ^ n + 1 - x
                    =
                    y . coeff 0 ^ p ^ n + 1
              :=
              by
                intro y
                  rw [ Finset.sum_eq_single_of_mem 0 ]
                  · simp
                  · simp
                  · intro j _ hj simp [ zero_pow zero_lt_iff.mpr hj ]
          congr <;> apply sum_zero_pow_mul_pow_p
#align witt_vector.peval_poly_of_interest' WittVector.peval_poly_of_interest'

variable (k)

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `nth_mul_coeff' [])
      (Command.declSig
       [(Term.explicitBinder "(" [`n] [":" (termℕ "ℕ")] [] ")")]
       (Term.typeSpec
        ":"
        («term∃_,_»
         "∃"
         (Lean.explicitBinders
          (Lean.unbracketedExplicitBinders
           [(Lean.binderIdent `f)]
           [":"
            (Term.arrow
             (Term.app `TruncatedWittVector [`p («term_+_» `n "+" (num "1")) `k])
             "→"
             (Term.arrow
              (Term.app `TruncatedWittVector [`p («term_+_» `n "+" (num "1")) `k])
              "→"
              `k))]))
         ","
         (Term.forall
          "∀"
          [`x `y]
          [(Term.typeSpec
            ":"
            (Term.app (WittVector.RingTheory.WittVector.MulCoeff.term𝕎 "𝕎") [`k]))]
          ","
          («term_=_»
           (Term.app
            `f
            [(Term.app `truncateFun [(«term_+_» `n "+" (num "1")) `x])
             (Term.app `truncateFun [(«term_+_» `n "+" (num "1")) `y])])
           "="
           («term_-_»
            («term_-_»
             (Term.app (Term.proj («term_*_» `x "*" `y) "." `coeff) [(«term_+_» `n "+" (num "1"))])
             "-"
             («term_*_»
              (Term.app (Term.proj `y "." `coeff) [(«term_+_» `n "+" (num "1"))])
              "*"
              («term_^_»
               (Term.app (Term.proj `x "." `coeff) [(num "0")])
               "^"
               («term_^_» `p "^" («term_+_» `n "+" (num "1"))))))
            "-"
            («term_*_»
             (Term.app (Term.proj `x "." `coeff) [(«term_+_» `n "+" (num "1"))])
             "*"
             («term_^_»
              (Term.app (Term.proj `y "." `coeff) [(num "0")])
              "^"
              («term_^_» `p "^" («term_+_» `n "+" (num "1")))))))))))
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
             [(Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `peval_poly_of_interest')]
             "]"]
            [])
           []
           (Std.Tactic.obtain
            "obtain"
            [(Std.Tactic.RCases.rcasesPatMed
              [(Std.Tactic.RCases.rcasesPat.tuple
                "⟨"
                [(Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `f₀)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hf₀)])
                  [])]
                "⟩")])]
            []
            [":="
             [(Term.app `exists_restrict_to_vars [`k (Term.app `poly_of_interest_vars [`p `n])])]])
           []
           (Tactic.tacticLet_
            "let"
            (Term.letDecl
             (Term.letIdDecl
              `f
              []
              [(Term.typeSpec
                ":"
                (Term.arrow
                 (Term.app `TruncatedWittVector [`p («term_+_» `n "+" (num "1")) `k])
                 "→"
                 (Term.arrow
                  (Term.app `TruncatedWittVector [`p («term_+_» `n "+" (num "1")) `k])
                  "→"
                  `k)))]
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Tactic.intro "intro" [`x `y])
                  []
                  (Tactic.apply "apply" `f₀)
                  []
                  (Std.Tactic.rintro
                   "rintro"
                   [(Std.Tactic.RCases.rintroPat.one
                     (Std.Tactic.RCases.rcasesPat.tuple
                      "⟨"
                      [(Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `a)])
                        [])
                       ","
                       (Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `ha)])
                        [])]
                      "⟩"))]
                   [])
                  []
                  (Tactic.apply
                   "apply"
                   (Term.app
                    `Function.uncurry
                    [(Matrix.Data.Fin.VecNotation.«term![_,» "![" [`x "," `y] "]")]))
                  []
                  (Tactic.simp
                   "simp"
                   []
                   []
                   ["only"]
                   ["["
                    [(Tactic.simpLemma [] [] `true_and_iff)
                     ","
                     (Tactic.simpLemma [] [] `Multiset.mem_cons)
                     ","
                     (Tactic.simpLemma [] [] `range_val)
                     ","
                     (Tactic.simpLemma [] [] `product_val)
                     ","
                     (Tactic.simpLemma [] [] `Multiset.mem_range)
                     ","
                     (Tactic.simpLemma [] [] `Multiset.mem_product)
                     ","
                     (Tactic.simpLemma [] [] `Multiset.range_succ)
                     ","
                     (Tactic.simpLemma [] [] `mem_univ_val)]
                    "]"]
                   [(Tactic.location "at" (Tactic.locationHyp [`ha] []))])
                  []
                  (Tactic.refine'
                   "refine'"
                   (Term.anonymousCtor
                    "⟨"
                    [`a.fst "," (Term.anonymousCtor "⟨" [`a.snd "," (Term.hole "_")] "⟩")]
                    "⟩"))
                  []
                  (Tactic.«tactic_<;>_»
                   (Tactic.cases'
                    "cases'"
                    [(Tactic.casesTarget [] `ha)]
                    []
                    ["with" [(Lean.binderIdent `ha) (Lean.binderIdent `ha)]])
                   "<;>"
                   (linarith "linarith" [] (linarithArgsRest [] ["only"] ["[" [`ha] "]"])))]))))))
           []
           (Mathlib.Tactic.«tacticUse_,,» "use" [`f])
           []
           (Tactic.intro "intro" [`x `y])
           []
           (Tactic.dsimp "dsimp" [] [] [] ["[" [(Tactic.simpLemma [] [] `peval)] "]"] [])
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq "[" [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `hf₀)] "]")
            [])
           []
           (Tactic.simp
            "simp"
            []
            []
            ["only"]
            ["["
             [(Tactic.simpLemma [] [] `f) "," (Tactic.simpLemma [] [] `Function.uncurry_apply_pair)]
             "]"]
            [])
           []
           (Tactic.congr "congr" [])
           []
           (Std.Tactic.Ext.«tacticExt___:_»
            "ext"
            [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `a))]
            [])
           []
           (Tactic.cases'
            "cases'"
            [(Tactic.casesTarget [] `a)]
            []
            ["with" [(Lean.binderIdent `a) (Lean.binderIdent `ha)]])
           []
           (Tactic.cases'
            "cases'"
            [(Tactic.casesTarget [] `a)]
            []
            ["with" [(Lean.binderIdent `i) (Lean.binderIdent `m)]])
           []
           (Tactic.simp
            "simp"
            []
            []
            ["only"]
            ["["
             [(Tactic.simpLemma [] [] `true_and_iff)
              ","
              (Tactic.simpLemma [] [] `Multiset.mem_cons)
              ","
              (Tactic.simpLemma [] [] `range_val)
              ","
              (Tactic.simpLemma [] [] `product_val)
              ","
              (Tactic.simpLemma [] [] `Multiset.mem_range)
              ","
              (Tactic.simpLemma [] [] `Multiset.mem_product)
              ","
              (Tactic.simpLemma [] [] `Multiset.range_succ)
              ","
              (Tactic.simpLemma [] [] `mem_univ_val)]
             "]"]
            [(Tactic.location "at" (Tactic.locationHyp [`ha] []))])
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`ha' []]
              [(Term.typeSpec ":" («term_<_» `m "<" («term_+_» `n "+" (num "1"))))]
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Tactic.«tactic_<;>_»
                   (Tactic.cases'
                    "cases'"
                    [(Tactic.casesTarget [] `ha)]
                    []
                    ["with" [(Lean.binderIdent `ha) (Lean.binderIdent `ha)]])
                   "<;>"
                   (linarith "linarith" [] (linarithArgsRest [] ["only"] ["[" [`ha] "]"])))]))))))
           []
           (Tactic.«tactic_<;>_»
            (Lean.Elab.Tactic.finCases "fin_cases" [`i] [])
            "<;>"
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
                []
                ["using"
                 (Term.app
                  `x.coeff_truncate_fun
                  [(Term.anonymousCtor "⟨" [`m "," `ha'] "⟩")])]))]))])))
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
            [(Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `peval_poly_of_interest')]
            "]"]
           [])
          []
          (Std.Tactic.obtain
           "obtain"
           [(Std.Tactic.RCases.rcasesPatMed
             [(Std.Tactic.RCases.rcasesPat.tuple
               "⟨"
               [(Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `f₀)])
                 [])
                ","
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hf₀)])
                 [])]
               "⟩")])]
           []
           [":="
            [(Term.app `exists_restrict_to_vars [`k (Term.app `poly_of_interest_vars [`p `n])])]])
          []
          (Tactic.tacticLet_
           "let"
           (Term.letDecl
            (Term.letIdDecl
             `f
             []
             [(Term.typeSpec
               ":"
               (Term.arrow
                (Term.app `TruncatedWittVector [`p («term_+_» `n "+" (num "1")) `k])
                "→"
                (Term.arrow
                 (Term.app `TruncatedWittVector [`p («term_+_» `n "+" (num "1")) `k])
                 "→"
                 `k)))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.intro "intro" [`x `y])
                 []
                 (Tactic.apply "apply" `f₀)
                 []
                 (Std.Tactic.rintro
                  "rintro"
                  [(Std.Tactic.RCases.rintroPat.one
                    (Std.Tactic.RCases.rcasesPat.tuple
                     "⟨"
                     [(Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `a)])
                       [])
                      ","
                      (Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `ha)])
                       [])]
                     "⟩"))]
                  [])
                 []
                 (Tactic.apply
                  "apply"
                  (Term.app
                   `Function.uncurry
                   [(Matrix.Data.Fin.VecNotation.«term![_,» "![" [`x "," `y] "]")]))
                 []
                 (Tactic.simp
                  "simp"
                  []
                  []
                  ["only"]
                  ["["
                   [(Tactic.simpLemma [] [] `true_and_iff)
                    ","
                    (Tactic.simpLemma [] [] `Multiset.mem_cons)
                    ","
                    (Tactic.simpLemma [] [] `range_val)
                    ","
                    (Tactic.simpLemma [] [] `product_val)
                    ","
                    (Tactic.simpLemma [] [] `Multiset.mem_range)
                    ","
                    (Tactic.simpLemma [] [] `Multiset.mem_product)
                    ","
                    (Tactic.simpLemma [] [] `Multiset.range_succ)
                    ","
                    (Tactic.simpLemma [] [] `mem_univ_val)]
                   "]"]
                  [(Tactic.location "at" (Tactic.locationHyp [`ha] []))])
                 []
                 (Tactic.refine'
                  "refine'"
                  (Term.anonymousCtor
                   "⟨"
                   [`a.fst "," (Term.anonymousCtor "⟨" [`a.snd "," (Term.hole "_")] "⟩")]
                   "⟩"))
                 []
                 (Tactic.«tactic_<;>_»
                  (Tactic.cases'
                   "cases'"
                   [(Tactic.casesTarget [] `ha)]
                   []
                   ["with" [(Lean.binderIdent `ha) (Lean.binderIdent `ha)]])
                  "<;>"
                  (linarith "linarith" [] (linarithArgsRest [] ["only"] ["[" [`ha] "]"])))]))))))
          []
          (Mathlib.Tactic.«tacticUse_,,» "use" [`f])
          []
          (Tactic.intro "intro" [`x `y])
          []
          (Tactic.dsimp "dsimp" [] [] [] ["[" [(Tactic.simpLemma [] [] `peval)] "]"] [])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `hf₀)] "]")
           [])
          []
          (Tactic.simp
           "simp"
           []
           []
           ["only"]
           ["["
            [(Tactic.simpLemma [] [] `f) "," (Tactic.simpLemma [] [] `Function.uncurry_apply_pair)]
            "]"]
           [])
          []
          (Tactic.congr "congr" [])
          []
          (Std.Tactic.Ext.«tacticExt___:_»
           "ext"
           [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `a))]
           [])
          []
          (Tactic.cases'
           "cases'"
           [(Tactic.casesTarget [] `a)]
           []
           ["with" [(Lean.binderIdent `a) (Lean.binderIdent `ha)]])
          []
          (Tactic.cases'
           "cases'"
           [(Tactic.casesTarget [] `a)]
           []
           ["with" [(Lean.binderIdent `i) (Lean.binderIdent `m)]])
          []
          (Tactic.simp
           "simp"
           []
           []
           ["only"]
           ["["
            [(Tactic.simpLemma [] [] `true_and_iff)
             ","
             (Tactic.simpLemma [] [] `Multiset.mem_cons)
             ","
             (Tactic.simpLemma [] [] `range_val)
             ","
             (Tactic.simpLemma [] [] `product_val)
             ","
             (Tactic.simpLemma [] [] `Multiset.mem_range)
             ","
             (Tactic.simpLemma [] [] `Multiset.mem_product)
             ","
             (Tactic.simpLemma [] [] `Multiset.range_succ)
             ","
             (Tactic.simpLemma [] [] `mem_univ_val)]
            "]"]
           [(Tactic.location "at" (Tactic.locationHyp [`ha] []))])
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`ha' []]
             [(Term.typeSpec ":" («term_<_» `m "<" («term_+_» `n "+" (num "1"))))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.«tactic_<;>_»
                  (Tactic.cases'
                   "cases'"
                   [(Tactic.casesTarget [] `ha)]
                   []
                   ["with" [(Lean.binderIdent `ha) (Lean.binderIdent `ha)]])
                  "<;>"
                  (linarith "linarith" [] (linarithArgsRest [] ["only"] ["[" [`ha] "]"])))]))))))
          []
          (Tactic.«tactic_<;>_»
           (Lean.Elab.Tactic.finCases "fin_cases" [`i] [])
           "<;>"
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
               []
               ["using"
                (Term.app
                 `x.coeff_truncate_fun
                 [(Term.anonymousCtor "⟨" [`m "," `ha'] "⟩")])]))]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.«tactic_<;>_»
       (Lean.Elab.Tactic.finCases "fin_cases" [`i] [])
       "<;>"
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
           []
           ["using"
            (Term.app `x.coeff_truncate_fun [(Term.anonymousCtor "⟨" [`m "," `ha'] "⟩")])]))]))
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
          []
          ["using"
           (Term.app `x.coeff_truncate_fun [(Term.anonymousCtor "⟨" [`m "," `ha'] "⟩")])]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Simpa.simpa
       "simpa"
       []
       []
       (Std.Tactic.Simpa.simpaArgsRest
        []
        []
        ["only"]
        []
        ["using" (Term.app `x.coeff_truncate_fun [(Term.anonymousCtor "⟨" [`m "," `ha'] "⟩")])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `x.coeff_truncate_fun [(Term.anonymousCtor "⟨" [`m "," `ha'] "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [`m "," `ha'] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ha'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `m
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `x.coeff_truncate_fun
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
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
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`ha' []]
         [(Term.typeSpec ":" («term_<_» `m "<" («term_+_» `n "+" (num "1"))))]
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.«tactic_<;>_»
              (Tactic.cases'
               "cases'"
               [(Tactic.casesTarget [] `ha)]
               []
               ["with" [(Lean.binderIdent `ha) (Lean.binderIdent `ha)]])
              "<;>"
              (linarith "linarith" [] (linarithArgsRest [] ["only"] ["[" [`ha] "]"])))]))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.«tactic_<;>_»
           (Tactic.cases'
            "cases'"
            [(Tactic.casesTarget [] `ha)]
            []
            ["with" [(Lean.binderIdent `ha) (Lean.binderIdent `ha)]])
           "<;>"
           (linarith "linarith" [] (linarithArgsRest [] ["only"] ["[" [`ha] "]"])))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.«tactic_<;>_»
       (Tactic.cases'
        "cases'"
        [(Tactic.casesTarget [] `ha)]
        []
        ["with" [(Lean.binderIdent `ha) (Lean.binderIdent `ha)]])
       "<;>"
       (linarith "linarith" [] (linarithArgsRest [] ["only"] ["[" [`ha] "]"])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (linarith "linarith" [] (linarithArgsRest [] ["only"] ["[" [`ha] "]"]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ha
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 2 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
      (Tactic.cases'
       "cases'"
       [(Tactic.casesTarget [] `ha)]
       []
       ["with" [(Lean.binderIdent `ha) (Lean.binderIdent `ha)]])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ha
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<_» `m "<" («term_+_» `n "+" (num "1")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_» `n "+" (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `n
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `m
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["["
        [(Tactic.simpLemma [] [] `true_and_iff)
         ","
         (Tactic.simpLemma [] [] `Multiset.mem_cons)
         ","
         (Tactic.simpLemma [] [] `range_val)
         ","
         (Tactic.simpLemma [] [] `product_val)
         ","
         (Tactic.simpLemma [] [] `Multiset.mem_range)
         ","
         (Tactic.simpLemma [] [] `Multiset.mem_product)
         ","
         (Tactic.simpLemma [] [] `Multiset.range_succ)
         ","
         (Tactic.simpLemma [] [] `mem_univ_val)]
        "]"]
       [(Tactic.location "at" (Tactic.locationHyp [`ha] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ha
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mem_univ_val
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Multiset.range_succ
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Multiset.mem_product
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Multiset.mem_range
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `product_val
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `range_val
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Multiset.mem_cons
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `true_and_iff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.cases'
       "cases'"
       [(Tactic.casesTarget [] `a)]
       []
       ["with" [(Lean.binderIdent `i) (Lean.binderIdent `m)]])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.cases'
       "cases'"
       [(Tactic.casesTarget [] `a)]
       []
       ["with" [(Lean.binderIdent `a) (Lean.binderIdent `ha)]])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Ext.«tacticExt___:_»
       "ext"
       [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `a))]
       [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.congr "congr" [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["["
        [(Tactic.simpLemma [] [] `f) "," (Tactic.simpLemma [] [] `Function.uncurry_apply_pair)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Function.uncurry_apply_pair
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `hf₀)] "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hf₀
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.dsimp "dsimp" [] [] [] ["[" [(Tactic.simpLemma [] [] `peval)] "]"] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `peval
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.intro "intro" [`x `y])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.«tacticUse_,,» "use" [`f])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticLet_
       "let"
       (Term.letDecl
        (Term.letIdDecl
         `f
         []
         [(Term.typeSpec
           ":"
           (Term.arrow
            (Term.app `TruncatedWittVector [`p («term_+_» `n "+" (num "1")) `k])
            "→"
            (Term.arrow
             (Term.app `TruncatedWittVector [`p («term_+_» `n "+" (num "1")) `k])
             "→"
             `k)))]
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.intro "intro" [`x `y])
             []
             (Tactic.apply "apply" `f₀)
             []
             (Std.Tactic.rintro
              "rintro"
              [(Std.Tactic.RCases.rintroPat.one
                (Std.Tactic.RCases.rcasesPat.tuple
                 "⟨"
                 [(Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `a)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `ha)])
                   [])]
                 "⟩"))]
              [])
             []
             (Tactic.apply
              "apply"
              (Term.app
               `Function.uncurry
               [(Matrix.Data.Fin.VecNotation.«term![_,» "![" [`x "," `y] "]")]))
             []
             (Tactic.simp
              "simp"
              []
              []
              ["only"]
              ["["
               [(Tactic.simpLemma [] [] `true_and_iff)
                ","
                (Tactic.simpLemma [] [] `Multiset.mem_cons)
                ","
                (Tactic.simpLemma [] [] `range_val)
                ","
                (Tactic.simpLemma [] [] `product_val)
                ","
                (Tactic.simpLemma [] [] `Multiset.mem_range)
                ","
                (Tactic.simpLemma [] [] `Multiset.mem_product)
                ","
                (Tactic.simpLemma [] [] `Multiset.range_succ)
                ","
                (Tactic.simpLemma [] [] `mem_univ_val)]
               "]"]
              [(Tactic.location "at" (Tactic.locationHyp [`ha] []))])
             []
             (Tactic.refine'
              "refine'"
              (Term.anonymousCtor
               "⟨"
               [`a.fst "," (Term.anonymousCtor "⟨" [`a.snd "," (Term.hole "_")] "⟩")]
               "⟩"))
             []
             (Tactic.«tactic_<;>_»
              (Tactic.cases'
               "cases'"
               [(Tactic.casesTarget [] `ha)]
               []
               ["with" [(Lean.binderIdent `ha) (Lean.binderIdent `ha)]])
              "<;>"
              (linarith "linarith" [] (linarithArgsRest [] ["only"] ["[" [`ha] "]"])))]))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.intro "intro" [`x `y])
          []
          (Tactic.apply "apply" `f₀)
          []
          (Std.Tactic.rintro
           "rintro"
           [(Std.Tactic.RCases.rintroPat.one
             (Std.Tactic.RCases.rcasesPat.tuple
              "⟨"
              [(Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `a)])
                [])
               ","
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `ha)])
                [])]
              "⟩"))]
           [])
          []
          (Tactic.apply
           "apply"
           (Term.app
            `Function.uncurry
            [(Matrix.Data.Fin.VecNotation.«term![_,» "![" [`x "," `y] "]")]))
          []
          (Tactic.simp
           "simp"
           []
           []
           ["only"]
           ["["
            [(Tactic.simpLemma [] [] `true_and_iff)
             ","
             (Tactic.simpLemma [] [] `Multiset.mem_cons)
             ","
             (Tactic.simpLemma [] [] `range_val)
             ","
             (Tactic.simpLemma [] [] `product_val)
             ","
             (Tactic.simpLemma [] [] `Multiset.mem_range)
             ","
             (Tactic.simpLemma [] [] `Multiset.mem_product)
             ","
             (Tactic.simpLemma [] [] `Multiset.range_succ)
             ","
             (Tactic.simpLemma [] [] `mem_univ_val)]
            "]"]
           [(Tactic.location "at" (Tactic.locationHyp [`ha] []))])
          []
          (Tactic.refine'
           "refine'"
           (Term.anonymousCtor
            "⟨"
            [`a.fst "," (Term.anonymousCtor "⟨" [`a.snd "," (Term.hole "_")] "⟩")]
            "⟩"))
          []
          (Tactic.«tactic_<;>_»
           (Tactic.cases'
            "cases'"
            [(Tactic.casesTarget [] `ha)]
            []
            ["with" [(Lean.binderIdent `ha) (Lean.binderIdent `ha)]])
           "<;>"
           (linarith "linarith" [] (linarithArgsRest [] ["only"] ["[" [`ha] "]"])))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.«tactic_<;>_»
       (Tactic.cases'
        "cases'"
        [(Tactic.casesTarget [] `ha)]
        []
        ["with" [(Lean.binderIdent `ha) (Lean.binderIdent `ha)]])
       "<;>"
       (linarith "linarith" [] (linarithArgsRest [] ["only"] ["[" [`ha] "]"])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (linarith "linarith" [] (linarithArgsRest [] ["only"] ["[" [`ha] "]"]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ha
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 2 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
      (Tactic.cases'
       "cases'"
       [(Tactic.casesTarget [] `ha)]
       []
       ["with" [(Lean.binderIdent `ha) (Lean.binderIdent `ha)]])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ha
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine'
       "refine'"
       (Term.anonymousCtor
        "⟨"
        [`a.fst "," (Term.anonymousCtor "⟨" [`a.snd "," (Term.hole "_")] "⟩")]
        "⟩"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [`a.fst "," (Term.anonymousCtor "⟨" [`a.snd "," (Term.hole "_")] "⟩")]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [`a.snd "," (Term.hole "_")] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a.snd
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a.fst
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
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
        [(Tactic.simpLemma [] [] `true_and_iff)
         ","
         (Tactic.simpLemma [] [] `Multiset.mem_cons)
         ","
         (Tactic.simpLemma [] [] `range_val)
         ","
         (Tactic.simpLemma [] [] `product_val)
         ","
         (Tactic.simpLemma [] [] `Multiset.mem_range)
         ","
         (Tactic.simpLemma [] [] `Multiset.mem_product)
         ","
         (Tactic.simpLemma [] [] `Multiset.range_succ)
         ","
         (Tactic.simpLemma [] [] `mem_univ_val)]
        "]"]
       [(Tactic.location "at" (Tactic.locationHyp [`ha] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ha
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mem_univ_val
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Multiset.range_succ
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Multiset.mem_product
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Multiset.mem_range
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `product_val
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `range_val
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Multiset.mem_cons
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `true_and_iff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.apply
       "apply"
       (Term.app `Function.uncurry [(Matrix.Data.Fin.VecNotation.«term![_,» "![" [`x "," `y] "]")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Function.uncurry [(Matrix.Data.Fin.VecNotation.«term![_,» "![" [`x "," `y] "]")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Matrix.Data.Fin.VecNotation.«term![_,»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Matrix.Data.Fin.VecNotation.«term![_,»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Matrix.Data.Fin.VecNotation.«term![_,» "![" [`x "," `y] "]")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Function.uncurry
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.rintro
       "rintro"
       [(Std.Tactic.RCases.rintroPat.one
         (Std.Tactic.RCases.rcasesPat.tuple
          "⟨"
          [(Std.Tactic.RCases.rcasesPatLo
            (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `a)])
            [])
           ","
           (Std.Tactic.RCases.rcasesPatLo
            (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `ha)])
            [])]
          "⟩"))]
       [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.apply "apply" `f₀)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f₀
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.intro "intro" [`x `y])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.arrow
       (Term.app `TruncatedWittVector [`p («term_+_» `n "+" (num "1")) `k])
       "→"
       (Term.arrow (Term.app `TruncatedWittVector [`p («term_+_» `n "+" (num "1")) `k]) "→" `k))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.arrow (Term.app `TruncatedWittVector [`p («term_+_» `n "+" (num "1")) `k]) "→" `k)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k
[PrettyPrinter.parenthesize] ...precedences are 25 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
      (Term.app `TruncatedWittVector [`p («term_+_» `n "+" (num "1")) `k])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `TruncatedWittVector
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 25, term)
[PrettyPrinter.parenthesize] ...precedences are 25 >? 25, (some 25, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
      (Term.app `TruncatedWittVector [`p («term_+_» `n "+" (num "1")) `k])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `TruncatedWittVector
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 25, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 25, (some 25, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.obtain
       "obtain"
       [(Std.Tactic.RCases.rcasesPatMed
         [(Std.Tactic.RCases.rcasesPat.tuple
           "⟨"
           [(Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `f₀)])
             [])
            ","
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hf₀)])
             [])]
           "⟩")])]
       []
       [":=" [(Term.app `exists_restrict_to_vars [`k (Term.app `poly_of_interest_vars [`p `n])])]])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `exists_restrict_to_vars [`k (Term.app `poly_of_interest_vars [`p `n])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `poly_of_interest_vars [`p `n])
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
      `poly_of_interest_vars
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `poly_of_interest_vars [`p `n])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `k
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `exists_restrict_to_vars
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
       ["[" [(Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `peval_poly_of_interest')] "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `peval_poly_of_interest'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term∃_,_»
       "∃"
       (Lean.explicitBinders
        (Lean.unbracketedExplicitBinders
         [(Lean.binderIdent `f)]
         [":"
          (Term.arrow
           (Term.app `TruncatedWittVector [`p («term_+_» `n "+" (num "1")) `k])
           "→"
           (Term.arrow
            (Term.app `TruncatedWittVector [`p («term_+_» `n "+" (num "1")) `k])
            "→"
            `k))]))
       ","
       (Term.forall
        "∀"
        [`x `y]
        [(Term.typeSpec ":" (Term.app (WittVector.RingTheory.WittVector.MulCoeff.term𝕎 "𝕎") [`k]))]
        ","
        («term_=_»
         (Term.app
          `f
          [(Term.app `truncateFun [(«term_+_» `n "+" (num "1")) `x])
           (Term.app `truncateFun [(«term_+_» `n "+" (num "1")) `y])])
         "="
         («term_-_»
          («term_-_»
           (Term.app (Term.proj («term_*_» `x "*" `y) "." `coeff) [(«term_+_» `n "+" (num "1"))])
           "-"
           («term_*_»
            (Term.app (Term.proj `y "." `coeff) [(«term_+_» `n "+" (num "1"))])
            "*"
            («term_^_»
             (Term.app (Term.proj `x "." `coeff) [(num "0")])
             "^"
             («term_^_» `p "^" («term_+_» `n "+" (num "1"))))))
          "-"
          («term_*_»
           (Term.app (Term.proj `x "." `coeff) [(«term_+_» `n "+" (num "1"))])
           "*"
           («term_^_»
            (Term.app (Term.proj `y "." `coeff) [(num "0")])
            "^"
            («term_^_» `p "^" («term_+_» `n "+" (num "1")))))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.forall
       "∀"
       [`x `y]
       [(Term.typeSpec ":" (Term.app (WittVector.RingTheory.WittVector.MulCoeff.term𝕎 "𝕎") [`k]))]
       ","
       («term_=_»
        (Term.app
         `f
         [(Term.app `truncateFun [(«term_+_» `n "+" (num "1")) `x])
          (Term.app `truncateFun [(«term_+_» `n "+" (num "1")) `y])])
        "="
        («term_-_»
         («term_-_»
          (Term.app (Term.proj («term_*_» `x "*" `y) "." `coeff) [(«term_+_» `n "+" (num "1"))])
          "-"
          («term_*_»
           (Term.app (Term.proj `y "." `coeff) [(«term_+_» `n "+" (num "1"))])
           "*"
           («term_^_»
            (Term.app (Term.proj `x "." `coeff) [(num "0")])
            "^"
            («term_^_» `p "^" («term_+_» `n "+" (num "1"))))))
         "-"
         («term_*_»
          (Term.app (Term.proj `x "." `coeff) [(«term_+_» `n "+" (num "1"))])
          "*"
          («term_^_»
           (Term.app (Term.proj `y "." `coeff) [(num "0")])
           "^"
           («term_^_» `p "^" («term_+_» `n "+" (num "1"))))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Term.app
        `f
        [(Term.app `truncateFun [(«term_+_» `n "+" (num "1")) `x])
         (Term.app `truncateFun [(«term_+_» `n "+" (num "1")) `y])])
       "="
       («term_-_»
        («term_-_»
         (Term.app (Term.proj («term_*_» `x "*" `y) "." `coeff) [(«term_+_» `n "+" (num "1"))])
         "-"
         («term_*_»
          (Term.app (Term.proj `y "." `coeff) [(«term_+_» `n "+" (num "1"))])
          "*"
          («term_^_»
           (Term.app (Term.proj `x "." `coeff) [(num "0")])
           "^"
           («term_^_» `p "^" («term_+_» `n "+" (num "1"))))))
        "-"
        («term_*_»
         (Term.app (Term.proj `x "." `coeff) [(«term_+_» `n "+" (num "1"))])
         "*"
         («term_^_»
          (Term.app (Term.proj `y "." `coeff) [(num "0")])
          "^"
          («term_^_» `p "^" («term_+_» `n "+" (num "1")))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_-_»
       («term_-_»
        (Term.app (Term.proj («term_*_» `x "*" `y) "." `coeff) [(«term_+_» `n "+" (num "1"))])
        "-"
        («term_*_»
         (Term.app (Term.proj `y "." `coeff) [(«term_+_» `n "+" (num "1"))])
         "*"
         («term_^_»
          (Term.app (Term.proj `x "." `coeff) [(num "0")])
          "^"
          («term_^_» `p "^" («term_+_» `n "+" (num "1"))))))
       "-"
       («term_*_»
        (Term.app (Term.proj `x "." `coeff) [(«term_+_» `n "+" (num "1"))])
        "*"
        («term_^_»
         (Term.app (Term.proj `y "." `coeff) [(num "0")])
         "^"
         («term_^_» `p "^" («term_+_» `n "+" (num "1"))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_»
       (Term.app (Term.proj `x "." `coeff) [(«term_+_» `n "+" (num "1"))])
       "*"
       («term_^_»
        (Term.app (Term.proj `y "." `coeff) [(num "0")])
        "^"
        («term_^_» `p "^" («term_+_» `n "+" (num "1")))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_»
       (Term.app (Term.proj `y "." `coeff) [(num "0")])
       "^"
       («term_^_» `p "^" («term_+_» `n "+" (num "1"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_» `p "^" («term_+_» `n "+" (num "1")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_» `n "+" (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `n
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_+_» `n "+" (num "1")) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Term.app (Term.proj `y "." `coeff) [(num "0")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `y "." `coeff)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `y
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1022, (some 1023, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (Term.app (Term.proj `x "." `coeff) [(«term_+_» `n "+" (num "1"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_+_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_+_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_» `n "+" (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `n
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_+_» `n "+" (num "1")) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `x "." `coeff)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1022, (some 1023, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      («term_-_»
       (Term.app (Term.proj («term_*_» `x "*" `y) "." `coeff) [(«term_+_» `n "+" (num "1"))])
       "-"
       («term_*_»
        (Term.app (Term.proj `y "." `coeff) [(«term_+_» `n "+" (num "1"))])
        "*"
        («term_^_»
         (Term.app (Term.proj `x "." `coeff) [(num "0")])
         "^"
         («term_^_» `p "^" («term_+_» `n "+" (num "1"))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_»
       (Term.app (Term.proj `y "." `coeff) [(«term_+_» `n "+" (num "1"))])
       "*"
       («term_^_»
        (Term.app (Term.proj `x "." `coeff) [(num "0")])
        "^"
        («term_^_» `p "^" («term_+_» `n "+" (num "1")))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_»
       (Term.app (Term.proj `x "." `coeff) [(num "0")])
       "^"
       («term_^_» `p "^" («term_+_» `n "+" (num "1"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_» `p "^" («term_+_» `n "+" (num "1")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_» `n "+" (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `n
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_+_» `n "+" (num "1")) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Term.app (Term.proj `x "." `coeff) [(num "0")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
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
[PrettyPrinter.parenthesize] ...precedences are 71 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (Term.app (Term.proj `y "." `coeff) [(«term_+_» `n "+" (num "1"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_+_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_+_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_» `n "+" (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `n
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_+_» `n "+" (num "1")) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `y "." `coeff)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `y
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1022, (some 1023, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      (Term.app (Term.proj («term_*_» `x "*" `y) "." `coeff) [(«term_+_» `n "+" (num "1"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_+_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_+_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_» `n "+" (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `n
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_+_» `n "+" (num "1")) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj («term_*_» `x "*" `y) "." `coeff)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      («term_*_» `x "*" `y)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 70, (some 71, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_*_» `x "*" `y) ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1022, (some 1023, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 65 >? 65, (some 66, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app
       `f
       [(Term.app `truncateFun [(«term_+_» `n "+" (num "1")) `x])
        (Term.app `truncateFun [(«term_+_» `n "+" (num "1")) `y])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `truncateFun [(«term_+_» `n "+" (num "1")) `y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
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
      `truncateFun
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `truncateFun [(Term.paren "(" («term_+_» `n "+" (num "1")) ")") `y])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `truncateFun [(«term_+_» `n "+" (num "1")) `x])
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
      `truncateFun
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `truncateFun [(Term.paren "(" («term_+_» `n "+" (num "1")) ")") `x])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (WittVector.RingTheory.WittVector.MulCoeff.term𝕎 "𝕎") [`k])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (WittVector.RingTheory.WittVector.MulCoeff.term𝕎 "𝕎")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'WittVector.RingTheory.WittVector.MulCoeff.term𝕎', expected 'WittVector.RingTheory.WittVector.MulCoeff.term𝕎._@.RingTheory.WittVector.MulCoeff._hyg.6'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  nth_mul_coeff'
  ( n : ℕ )
    :
      ∃
        f : TruncatedWittVector p n + 1 k → TruncatedWittVector p n + 1 k → k
        ,
        ∀
          x y
          : 𝕎 k
          ,
          f truncateFun n + 1 x truncateFun n + 1 y
            =
            x * y . coeff n + 1 - y . coeff n + 1 * x . coeff 0 ^ p ^ n + 1
              -
              x . coeff n + 1 * y . coeff 0 ^ p ^ n + 1
  :=
    by
      simp only [ ← peval_poly_of_interest' ]
        obtain ⟨ f₀ , hf₀ ⟩ := exists_restrict_to_vars k poly_of_interest_vars p n
        let
          f
            : TruncatedWittVector p n + 1 k → TruncatedWittVector p n + 1 k → k
            :=
            by
              intro x y
                apply f₀
                rintro ⟨ a , ha ⟩
                apply Function.uncurry ![ x , y ]
                simp
                  only
                  [
                    true_and_iff
                      ,
                      Multiset.mem_cons
                      ,
                      range_val
                      ,
                      product_val
                      ,
                      Multiset.mem_range
                      ,
                      Multiset.mem_product
                      ,
                      Multiset.range_succ
                      ,
                      mem_univ_val
                    ]
                  at ha
                refine' ⟨ a.fst , ⟨ a.snd , _ ⟩ ⟩
                cases' ha with ha ha <;> linarith only [ ha ]
        use f
        intro x y
        dsimp [ peval ]
        rw [ ← hf₀ ]
        simp only [ f , Function.uncurry_apply_pair ]
        congr
        ext a
        cases' a with a ha
        cases' a with i m
        simp
          only
          [
            true_and_iff
              ,
              Multiset.mem_cons
              ,
              range_val
              ,
              product_val
              ,
              Multiset.mem_range
              ,
              Multiset.mem_product
              ,
              Multiset.range_succ
              ,
              mem_univ_val
            ]
          at ha
        have ha' : m < n + 1 := by cases' ha with ha ha <;> linarith only [ ha ]
        fin_cases i <;> · simpa only using x.coeff_truncate_fun ⟨ m , ha' ⟩
#align witt_vector.nth_mul_coeff' WittVector.nth_mul_coeff'

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `nth_mul_coeff [])
      (Command.declSig
       [(Term.explicitBinder "(" [`n] [":" (termℕ "ℕ")] [] ")")]
       (Term.typeSpec
        ":"
        («term∃_,_»
         "∃"
         (Lean.explicitBinders
          (Lean.unbracketedExplicitBinders
           [(Lean.binderIdent `f)]
           [":"
            (Term.arrow
             (Term.app `TruncatedWittVector [`p («term_+_» `n "+" (num "1")) `k])
             "→"
             (Term.arrow
              (Term.app `TruncatedWittVector [`p («term_+_» `n "+" (num "1")) `k])
              "→"
              `k))]))
         ","
         (Term.forall
          "∀"
          [`x `y]
          [(Term.typeSpec
            ":"
            (Term.app (WittVector.RingTheory.WittVector.MulCoeff.term𝕎 "𝕎") [`k]))]
          ","
          («term_=_»
           (Term.app (Term.proj («term_*_» `x "*" `y) "." `coeff) [(«term_+_» `n "+" (num "1"))])
           "="
           («term_+_»
            («term_+_»
             («term_*_»
              (Term.app (Term.proj `x "." `coeff) [(«term_+_» `n "+" (num "1"))])
              "*"
              («term_^_»
               (Term.app (Term.proj `y "." `coeff) [(num "0")])
               "^"
               («term_^_» `p "^" («term_+_» `n "+" (num "1")))))
             "+"
             («term_*_»
              (Term.app (Term.proj `y "." `coeff) [(«term_+_» `n "+" (num "1"))])
              "*"
              («term_^_»
               (Term.app (Term.proj `x "." `coeff) [(num "0")])
               "^"
               («term_^_» `p "^" («term_+_» `n "+" (num "1"))))))
            "+"
            (Term.app
             `f
             [(Term.app `truncateFun [(«term_+_» `n "+" (num "1")) `x])
              (Term.app `truncateFun [(«term_+_» `n "+" (num "1")) `y])])))))))
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
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `f)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hf)])
                  [])]
                "⟩")])]
            []
            [":=" [(Term.app `nth_mul_coeff' [`p `k `n])]])
           []
           (Mathlib.Tactic.«tacticUse_,,» "use" [`f])
           []
           (Tactic.intro "intro" [`x `y])
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `hf [`x `y]))] "]")
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
         [(Std.Tactic.obtain
           "obtain"
           [(Std.Tactic.RCases.rcasesPatMed
             [(Std.Tactic.RCases.rcasesPat.tuple
               "⟨"
               [(Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `f)])
                 [])
                ","
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hf)])
                 [])]
               "⟩")])]
           []
           [":=" [(Term.app `nth_mul_coeff' [`p `k `n])]])
          []
          (Mathlib.Tactic.«tacticUse_,,» "use" [`f])
          []
          (Tactic.intro "intro" [`x `y])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `hf [`x `y]))] "]")
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
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `hf [`x `y]))] "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `hf [`x `y])
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
      `hf
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.intro "intro" [`x `y])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.«tacticUse_,,» "use" [`f])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
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
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `f)])
             [])
            ","
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hf)])
             [])]
           "⟩")])]
       []
       [":=" [(Term.app `nth_mul_coeff' [`p `k `n])]])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `nth_mul_coeff' [`p `k `n])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `k
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `nth_mul_coeff'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term∃_,_»
       "∃"
       (Lean.explicitBinders
        (Lean.unbracketedExplicitBinders
         [(Lean.binderIdent `f)]
         [":"
          (Term.arrow
           (Term.app `TruncatedWittVector [`p («term_+_» `n "+" (num "1")) `k])
           "→"
           (Term.arrow
            (Term.app `TruncatedWittVector [`p («term_+_» `n "+" (num "1")) `k])
            "→"
            `k))]))
       ","
       (Term.forall
        "∀"
        [`x `y]
        [(Term.typeSpec ":" (Term.app (WittVector.RingTheory.WittVector.MulCoeff.term𝕎 "𝕎") [`k]))]
        ","
        («term_=_»
         (Term.app (Term.proj («term_*_» `x "*" `y) "." `coeff) [(«term_+_» `n "+" (num "1"))])
         "="
         («term_+_»
          («term_+_»
           («term_*_»
            (Term.app (Term.proj `x "." `coeff) [(«term_+_» `n "+" (num "1"))])
            "*"
            («term_^_»
             (Term.app (Term.proj `y "." `coeff) [(num "0")])
             "^"
             («term_^_» `p "^" («term_+_» `n "+" (num "1")))))
           "+"
           («term_*_»
            (Term.app (Term.proj `y "." `coeff) [(«term_+_» `n "+" (num "1"))])
            "*"
            («term_^_»
             (Term.app (Term.proj `x "." `coeff) [(num "0")])
             "^"
             («term_^_» `p "^" («term_+_» `n "+" (num "1"))))))
          "+"
          (Term.app
           `f
           [(Term.app `truncateFun [(«term_+_» `n "+" (num "1")) `x])
            (Term.app `truncateFun [(«term_+_» `n "+" (num "1")) `y])])))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.forall
       "∀"
       [`x `y]
       [(Term.typeSpec ":" (Term.app (WittVector.RingTheory.WittVector.MulCoeff.term𝕎 "𝕎") [`k]))]
       ","
       («term_=_»
        (Term.app (Term.proj («term_*_» `x "*" `y) "." `coeff) [(«term_+_» `n "+" (num "1"))])
        "="
        («term_+_»
         («term_+_»
          («term_*_»
           (Term.app (Term.proj `x "." `coeff) [(«term_+_» `n "+" (num "1"))])
           "*"
           («term_^_»
            (Term.app (Term.proj `y "." `coeff) [(num "0")])
            "^"
            («term_^_» `p "^" («term_+_» `n "+" (num "1")))))
          "+"
          («term_*_»
           (Term.app (Term.proj `y "." `coeff) [(«term_+_» `n "+" (num "1"))])
           "*"
           («term_^_»
            (Term.app (Term.proj `x "." `coeff) [(num "0")])
            "^"
            («term_^_» `p "^" («term_+_» `n "+" (num "1"))))))
         "+"
         (Term.app
          `f
          [(Term.app `truncateFun [(«term_+_» `n "+" (num "1")) `x])
           (Term.app `truncateFun [(«term_+_» `n "+" (num "1")) `y])]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Term.app (Term.proj («term_*_» `x "*" `y) "." `coeff) [(«term_+_» `n "+" (num "1"))])
       "="
       («term_+_»
        («term_+_»
         («term_*_»
          (Term.app (Term.proj `x "." `coeff) [(«term_+_» `n "+" (num "1"))])
          "*"
          («term_^_»
           (Term.app (Term.proj `y "." `coeff) [(num "0")])
           "^"
           («term_^_» `p "^" («term_+_» `n "+" (num "1")))))
         "+"
         («term_*_»
          (Term.app (Term.proj `y "." `coeff) [(«term_+_» `n "+" (num "1"))])
          "*"
          («term_^_»
           (Term.app (Term.proj `x "." `coeff) [(num "0")])
           "^"
           («term_^_» `p "^" («term_+_» `n "+" (num "1"))))))
        "+"
        (Term.app
         `f
         [(Term.app `truncateFun [(«term_+_» `n "+" (num "1")) `x])
          (Term.app `truncateFun [(«term_+_» `n "+" (num "1")) `y])])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_»
       («term_+_»
        («term_*_»
         (Term.app (Term.proj `x "." `coeff) [(«term_+_» `n "+" (num "1"))])
         "*"
         («term_^_»
          (Term.app (Term.proj `y "." `coeff) [(num "0")])
          "^"
          («term_^_» `p "^" («term_+_» `n "+" (num "1")))))
        "+"
        («term_*_»
         (Term.app (Term.proj `y "." `coeff) [(«term_+_» `n "+" (num "1"))])
         "*"
         («term_^_»
          (Term.app (Term.proj `x "." `coeff) [(num "0")])
          "^"
          («term_^_» `p "^" («term_+_» `n "+" (num "1"))))))
       "+"
       (Term.app
        `f
        [(Term.app `truncateFun [(«term_+_» `n "+" (num "1")) `x])
         (Term.app `truncateFun [(«term_+_» `n "+" (num "1")) `y])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `f
       [(Term.app `truncateFun [(«term_+_» `n "+" (num "1")) `x])
        (Term.app `truncateFun [(«term_+_» `n "+" (num "1")) `y])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `truncateFun [(«term_+_» `n "+" (num "1")) `y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
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
      `truncateFun
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `truncateFun [(Term.paren "(" («term_+_» `n "+" (num "1")) ")") `y])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `truncateFun [(«term_+_» `n "+" (num "1")) `x])
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
      `truncateFun
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `truncateFun [(Term.paren "(" («term_+_» `n "+" (num "1")) ")") `x])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      («term_+_»
       («term_*_»
        (Term.app (Term.proj `x "." `coeff) [(«term_+_» `n "+" (num "1"))])
        "*"
        («term_^_»
         (Term.app (Term.proj `y "." `coeff) [(num "0")])
         "^"
         («term_^_» `p "^" («term_+_» `n "+" (num "1")))))
       "+"
       («term_*_»
        (Term.app (Term.proj `y "." `coeff) [(«term_+_» `n "+" (num "1"))])
        "*"
        («term_^_»
         (Term.app (Term.proj `x "." `coeff) [(num "0")])
         "^"
         («term_^_» `p "^" («term_+_» `n "+" (num "1"))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_»
       (Term.app (Term.proj `y "." `coeff) [(«term_+_» `n "+" (num "1"))])
       "*"
       («term_^_»
        (Term.app (Term.proj `x "." `coeff) [(num "0")])
        "^"
        («term_^_» `p "^" («term_+_» `n "+" (num "1")))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_»
       (Term.app (Term.proj `x "." `coeff) [(num "0")])
       "^"
       («term_^_» `p "^" («term_+_» `n "+" (num "1"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_» `p "^" («term_+_» `n "+" (num "1")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_» `n "+" (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `n
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_+_» `n "+" (num "1")) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Term.app (Term.proj `x "." `coeff) [(num "0")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
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
[PrettyPrinter.parenthesize] ...precedences are 71 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (Term.app (Term.proj `y "." `coeff) [(«term_+_» `n "+" (num "1"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_+_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_+_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_» `n "+" (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `n
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_+_» `n "+" (num "1")) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `y "." `coeff)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `y
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1022, (some 1023, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      («term_*_»
       (Term.app (Term.proj `x "." `coeff) [(«term_+_» `n "+" (num "1"))])
       "*"
       («term_^_»
        (Term.app (Term.proj `y "." `coeff) [(num "0")])
        "^"
        («term_^_» `p "^" («term_+_» `n "+" (num "1")))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_»
       (Term.app (Term.proj `y "." `coeff) [(num "0")])
       "^"
       («term_^_» `p "^" («term_+_» `n "+" (num "1"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_» `p "^" («term_+_» `n "+" (num "1")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_» `n "+" (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `n
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_+_» `n "+" (num "1")) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Term.app (Term.proj `y "." `coeff) [(num "0")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `y "." `coeff)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `y
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1022, (some 1023, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (Term.app (Term.proj `x "." `coeff) [(«term_+_» `n "+" (num "1"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_+_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_+_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_» `n "+" (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `n
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_+_» `n "+" (num "1")) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `x "." `coeff)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1022, (some 1023, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 65 >? 70, (some 71, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 65 >? 65, (some 66, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app (Term.proj («term_*_» `x "*" `y) "." `coeff) [(«term_+_» `n "+" (num "1"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_+_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_+_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_» `n "+" (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `n
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_+_» `n "+" (num "1")) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj («term_*_» `x "*" `y) "." `coeff)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      («term_*_» `x "*" `y)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 70, (some 71, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_*_» `x "*" `y) ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (WittVector.RingTheory.WittVector.MulCoeff.term𝕎 "𝕎") [`k])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (WittVector.RingTheory.WittVector.MulCoeff.term𝕎 "𝕎")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'WittVector.RingTheory.WittVector.MulCoeff.term𝕎', expected 'WittVector.RingTheory.WittVector.MulCoeff.term𝕎._@.RingTheory.WittVector.MulCoeff._hyg.6'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  nth_mul_coeff
  ( n : ℕ )
    :
      ∃
        f : TruncatedWittVector p n + 1 k → TruncatedWittVector p n + 1 k → k
        ,
        ∀
          x y
          : 𝕎 k
          ,
          x * y . coeff n + 1
            =
            x . coeff n + 1 * y . coeff 0 ^ p ^ n + 1 + y . coeff n + 1 * x . coeff 0 ^ p ^ n + 1
              +
              f truncateFun n + 1 x truncateFun n + 1 y
  := by obtain ⟨ f , hf ⟩ := nth_mul_coeff' p k n use f intro x y rw [ hf x y ] ring
#align witt_vector.nth_mul_coeff WittVector.nth_mul_coeff

variable {k}

/--
Produces the "remainder function" of the `n+1`st coefficient, which does not depend on the `n+1`st
coefficients of the inputs. -/
def nthRemainder (n : ℕ) : (Fin (n + 1) → k) → (Fin (n + 1) → k) → k :=
  Classical.choose (nth_mul_coeff p k n)
#align witt_vector.nth_remainder WittVector.nthRemainder

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `nth_remainder_spec [])
      (Command.declSig
       [(Term.explicitBinder "(" [`n] [":" (termℕ "ℕ")] [] ")")
        (Term.explicitBinder
         "("
         [`x `y]
         [":" (Term.app (WittVector.RingTheory.WittVector.MulCoeff.term𝕎 "𝕎") [`k])]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app (Term.proj («term_*_» `x "*" `y) "." `coeff) [(«term_+_» `n "+" (num "1"))])
         "="
         («term_+_»
          («term_+_»
           («term_*_»
            (Term.app (Term.proj `x "." `coeff) [(«term_+_» `n "+" (num "1"))])
            "*"
            («term_^_»
             (Term.app (Term.proj `y "." `coeff) [(num "0")])
             "^"
             («term_^_» `p "^" («term_+_» `n "+" (num "1")))))
           "+"
           («term_*_»
            (Term.app (Term.proj `y "." `coeff) [(«term_+_» `n "+" (num "1"))])
            "*"
            («term_^_»
             (Term.app (Term.proj `x "." `coeff) [(num "0")])
             "^"
             («term_^_» `p "^" («term_+_» `n "+" (num "1"))))))
          "+"
          (Term.app
           `nthRemainder
           [`p
            `n
            (Term.app `truncateFun [(«term_+_» `n "+" (num "1")) `x])
            (Term.app `truncateFun [(«term_+_» `n "+" (num "1")) `y])])))))
      (Command.declValSimple
       ":="
       (Term.app
        `Classical.choose_spec
        [(Term.app `nth_mul_coeff [`p `k `n]) (Term.hole "_") (Term.hole "_")])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Classical.choose_spec
       [(Term.app `nth_mul_coeff [`p `k `n]) (Term.hole "_") (Term.hole "_")])
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.app `nth_mul_coeff [`p `k `n])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `k
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `nth_mul_coeff
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `nth_mul_coeff [`p `k `n])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Classical.choose_spec
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app (Term.proj («term_*_» `x "*" `y) "." `coeff) [(«term_+_» `n "+" (num "1"))])
       "="
       («term_+_»
        («term_+_»
         («term_*_»
          (Term.app (Term.proj `x "." `coeff) [(«term_+_» `n "+" (num "1"))])
          "*"
          («term_^_»
           (Term.app (Term.proj `y "." `coeff) [(num "0")])
           "^"
           («term_^_» `p "^" («term_+_» `n "+" (num "1")))))
         "+"
         («term_*_»
          (Term.app (Term.proj `y "." `coeff) [(«term_+_» `n "+" (num "1"))])
          "*"
          («term_^_»
           (Term.app (Term.proj `x "." `coeff) [(num "0")])
           "^"
           («term_^_» `p "^" («term_+_» `n "+" (num "1"))))))
        "+"
        (Term.app
         `nthRemainder
         [`p
          `n
          (Term.app `truncateFun [(«term_+_» `n "+" (num "1")) `x])
          (Term.app `truncateFun [(«term_+_» `n "+" (num "1")) `y])])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_»
       («term_+_»
        («term_*_»
         (Term.app (Term.proj `x "." `coeff) [(«term_+_» `n "+" (num "1"))])
         "*"
         («term_^_»
          (Term.app (Term.proj `y "." `coeff) [(num "0")])
          "^"
          («term_^_» `p "^" («term_+_» `n "+" (num "1")))))
        "+"
        («term_*_»
         (Term.app (Term.proj `y "." `coeff) [(«term_+_» `n "+" (num "1"))])
         "*"
         («term_^_»
          (Term.app (Term.proj `x "." `coeff) [(num "0")])
          "^"
          («term_^_» `p "^" («term_+_» `n "+" (num "1"))))))
       "+"
       (Term.app
        `nthRemainder
        [`p
         `n
         (Term.app `truncateFun [(«term_+_» `n "+" (num "1")) `x])
         (Term.app `truncateFun [(«term_+_» `n "+" (num "1")) `y])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `nthRemainder
       [`p
        `n
        (Term.app `truncateFun [(«term_+_» `n "+" (num "1")) `x])
        (Term.app `truncateFun [(«term_+_» `n "+" (num "1")) `y])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `truncateFun [(«term_+_» `n "+" (num "1")) `y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
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
      `truncateFun
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `truncateFun [(Term.paren "(" («term_+_» `n "+" (num "1")) ")") `y])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `truncateFun [(«term_+_» `n "+" (num "1")) `x])
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
      `truncateFun
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `truncateFun [(Term.paren "(" («term_+_» `n "+" (num "1")) ")") `x])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `nthRemainder
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      («term_+_»
       («term_*_»
        (Term.app (Term.proj `x "." `coeff) [(«term_+_» `n "+" (num "1"))])
        "*"
        («term_^_»
         (Term.app (Term.proj `y "." `coeff) [(num "0")])
         "^"
         («term_^_» `p "^" («term_+_» `n "+" (num "1")))))
       "+"
       («term_*_»
        (Term.app (Term.proj `y "." `coeff) [(«term_+_» `n "+" (num "1"))])
        "*"
        («term_^_»
         (Term.app (Term.proj `x "." `coeff) [(num "0")])
         "^"
         («term_^_» `p "^" («term_+_» `n "+" (num "1"))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_»
       (Term.app (Term.proj `y "." `coeff) [(«term_+_» `n "+" (num "1"))])
       "*"
       («term_^_»
        (Term.app (Term.proj `x "." `coeff) [(num "0")])
        "^"
        («term_^_» `p "^" («term_+_» `n "+" (num "1")))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_»
       (Term.app (Term.proj `x "." `coeff) [(num "0")])
       "^"
       («term_^_» `p "^" («term_+_» `n "+" (num "1"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_» `p "^" («term_+_» `n "+" (num "1")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_» `n "+" (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `n
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_+_» `n "+" (num "1")) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Term.app (Term.proj `x "." `coeff) [(num "0")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
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
[PrettyPrinter.parenthesize] ...precedences are 71 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (Term.app (Term.proj `y "." `coeff) [(«term_+_» `n "+" (num "1"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_+_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_+_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_» `n "+" (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `n
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_+_» `n "+" (num "1")) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `y "." `coeff)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `y
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1022, (some 1023, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      («term_*_»
       (Term.app (Term.proj `x "." `coeff) [(«term_+_» `n "+" (num "1"))])
       "*"
       («term_^_»
        (Term.app (Term.proj `y "." `coeff) [(num "0")])
        "^"
        («term_^_» `p "^" («term_+_» `n "+" (num "1")))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_»
       (Term.app (Term.proj `y "." `coeff) [(num "0")])
       "^"
       («term_^_» `p "^" («term_+_» `n "+" (num "1"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_» `p "^" («term_+_» `n "+" (num "1")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_» `n "+" (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `n
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_+_» `n "+" (num "1")) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Term.app (Term.proj `y "." `coeff) [(num "0")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `y "." `coeff)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `y
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1022, (some 1023, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (Term.app (Term.proj `x "." `coeff) [(«term_+_» `n "+" (num "1"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_+_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_+_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_» `n "+" (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `n
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_+_» `n "+" (num "1")) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `x "." `coeff)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1022, (some 1023, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 65 >? 70, (some 71, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 65 >? 65, (some 66, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app (Term.proj («term_*_» `x "*" `y) "." `coeff) [(«term_+_» `n "+" (num "1"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_+_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_+_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_» `n "+" (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `n
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_+_» `n "+" (num "1")) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj («term_*_» `x "*" `y) "." `coeff)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      («term_*_» `x "*" `y)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 70, (some 71, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_*_» `x "*" `y) ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (WittVector.RingTheory.WittVector.MulCoeff.term𝕎 "𝕎") [`k])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (WittVector.RingTheory.WittVector.MulCoeff.term𝕎 "𝕎")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'WittVector.RingTheory.WittVector.MulCoeff.term𝕎', expected 'WittVector.RingTheory.WittVector.MulCoeff.term𝕎._@.RingTheory.WittVector.MulCoeff._hyg.6'
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
  nth_remainder_spec
  ( n : ℕ ) ( x y : 𝕎 k )
    :
      x * y . coeff n + 1
        =
        x . coeff n + 1 * y . coeff 0 ^ p ^ n + 1 + y . coeff n + 1 * x . coeff 0 ^ p ^ n + 1
          +
          nthRemainder p n truncateFun n + 1 x truncateFun n + 1 y
  := Classical.choose_spec nth_mul_coeff p k n _ _
#align witt_vector.nth_remainder_spec WittVector.nth_remainder_spec

end WittVector

