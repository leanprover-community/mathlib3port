import Mathbin.Algebra.GroupPower.Identities
import Mathbin.Data.Zmod.Basic
import Mathbin.FieldTheory.Finite.Basic
import Mathbin.Data.Int.Parity
import Mathbin.Data.Fintype.Card

/-!
# Lagrange's four square theorem

The main result in this file is `sum_four_squares`,
a proof that every natural number is the sum of four square numbers.

## Implementation Notes

The proof used is close to Lagrange's original proof.
-/


open Finset Polynomial FiniteField Equivₓ

open_locale BigOperators

namespace Int

theorem sq_add_sq_of_two_mul_sq_add_sq {m x y : ℤ} (h : (2*m) = (x^2)+y^2) : m = ((x - y) / 2^2)+(x+y) / 2^2 :=
  have : Even ((x^2)+y^2) := by
    simp [h.symm, even_mul]
  have hxaddy : Even (x+y) := by
    simpa [sq] with parity_simps
  have hxsuby : Even (x - y) := by
    simpa [sq] with parity_simps
  (mul_right_inj'
        (show (2*2 : ℤ) ≠ 0 from by
          decide)).1 $
    calc ((2*2)*m) = (x - y^2)+(x+y)^2 := by
      rw [mul_assocₓ, h] <;> ring
      _ = ((2*(x - y) / 2)^2)+(2*(x+y) / 2)^2 := by
      rw [Int.mul_div_cancel' hxsuby, Int.mul_div_cancel' hxaddy]
      _ = (2*2)*((x - y) / 2^2)+(x+y) / 2^2 := by
      simp [mul_addₓ, pow_succₓ, mul_commₓ, mul_assocₓ, mul_left_commₓ]
      

theorem exists_sq_add_sq_add_one_eq_k (p : ℕ) [hp : Fact p.prime] :
    ∃ (a b : ℤ)(k : ℕ), ((((a^2)+b^2)+1) = k*p) ∧ k < p :=
  (hp.1.eq_two_or_odd.elim fun hp2 =>
      hp2.symm ▸
        ⟨1, 0, 1, rfl, by
          decide⟩) $
    fun hp1 =>
    let ⟨a, b, hab⟩ := Zmod.sq_add_sq p (-1)
    have hab' : (p : ℤ) ∣ ((a.val_min_abs^2)+b.val_min_abs^2)+1 :=
      (CharP.int_cast_eq_zero_iff (Zmod p) p _).1 $ by
        simpa [eq_neg_iff_add_eq_zero] using hab
    let ⟨k, hk⟩ := hab'
    have hk0 : 0 ≤ k :=
      nonneg_of_mul_nonneg_left
        (by
          rw [← hk] <;> exact add_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) zero_le_one)
        (Int.coe_nat_pos.2 hp.1.Pos)
    ⟨a.val_min_abs, b.val_min_abs, k.nat_abs, by
      rw [hk, Int.nat_abs_of_nonneg hk0, mul_commₓ],
      lt_of_mul_lt_mul_left
        (calc (p*k.nat_abs) = ((a.val_min_abs.nat_abs^2)+b.val_min_abs.nat_abs^2)+1 := by
          rw [← Int.coe_nat_inj', Int.coe_nat_add, Int.coe_nat_add, Int.coe_nat_pow, Int.coe_nat_pow, Int.nat_abs_sq,
            Int.nat_abs_sq, Int.coe_nat_one, hk, Int.coe_nat_mul, Int.nat_abs_of_nonneg hk0]
          _ ≤ ((p / 2^2)+p / 2^2)+1 :=
          add_le_add
            (add_le_add (Nat.pow_le_pow_of_le_leftₓ (Zmod.nat_abs_val_min_abs_le _) _)
              (Nat.pow_le_pow_of_le_leftₓ (Zmod.nat_abs_val_min_abs_le _) _))
            (le_reflₓ _)
          _ < (((p / 2^2)+p / 2^2)+p % 2^2)+(2*p / 2^2)+(4*p / 2)*p % 2 := by
          rw [hp1, one_pow, mul_oneₓ] <;>
            exact
              (lt_add_iff_pos_right _).2
                (add_pos_of_nonneg_of_pos (Nat.zero_leₓ _)
                  (mul_pos
                    (by
                      decide)
                    (Nat.div_pos hp.1.two_le
                      (by
                        decide))))
          _ = p*p := by
          conv_rhs => rw [← Nat.mod_add_divₓ p 2]
          ring
          )
        (show 0 ≤ p from Nat.zero_leₓ _)⟩

end Int

namespace Nat

open Int

open_locale Classical

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [] [] [(Command.private "private")] [] [] [])
 (Command.theorem
  "theorem"
  (Command.declId `sum_four_squares_of_two_mul_sum_four_squares [])
  (Command.declSig
   [(Term.implicitBinder "{" [`m `a `b `c `d] [":" (termℤ "ℤ")] "}")
    (Term.explicitBinder
     "("
     [`h]
     [":"
      («term_=_»
       (Init.Logic.«term_+_»
        (Init.Logic.«term_+_»
         (Init.Logic.«term_+_»
          (Cardinal.SetTheory.Cofinality.«term_^_» `a "^" (numLit "2"))
          "+"
          (Cardinal.SetTheory.Cofinality.«term_^_» `b "^" (numLit "2")))
         "+"
         (Cardinal.SetTheory.Cofinality.«term_^_» `c "^" (numLit "2")))
        "+"
        (Cardinal.SetTheory.Cofinality.«term_^_» `d "^" (numLit "2")))
       "="
       (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `m))]
     []
     ")")]
   (Term.typeSpec
    ":"
    («term∃_,_»
     "∃"
     (Lean.explicitBinders
      (Lean.unbracketedExplicitBinders
       [(Lean.binderIdent `w) (Lean.binderIdent `x) (Lean.binderIdent `y) (Lean.binderIdent `z)]
       [":" (termℤ "ℤ")]))
     ","
     («term_=_»
      (Init.Logic.«term_+_»
       (Init.Logic.«term_+_»
        (Init.Logic.«term_+_»
         (Cardinal.SetTheory.Cofinality.«term_^_» `w "^" (numLit "2"))
         "+"
         (Cardinal.SetTheory.Cofinality.«term_^_» `x "^" (numLit "2")))
        "+"
        (Cardinal.SetTheory.Cofinality.«term_^_» `y "^" (numLit "2")))
       "+"
       (Cardinal.SetTheory.Cofinality.«term_^_» `z "^" (numLit "2")))
      "="
      `m))))
  (Command.declValSimple
   ":="
   (Term.have
    "have"
    (Term.haveDecl
     (Term.haveIdDecl
      []
      [(Term.typeSpec
        ":"
        (Term.forall
         "∀"
         [(Term.simpleBinder
           [`f]
           [(Term.typeSpec ":" (Term.arrow (Term.app `Finₓ [(numLit "4")]) "→" (Term.app `Zmod [(numLit "2")])))])]
         ","
         (Term.arrow
          («term_=_»
           (Init.Logic.«term_+_»
            (Init.Logic.«term_+_»
             (Init.Logic.«term_+_»
              (Cardinal.SetTheory.Cofinality.«term_^_» (Term.app `f [(numLit "0")]) "^" (numLit "2"))
              "+"
              (Cardinal.SetTheory.Cofinality.«term_^_» (Term.app `f [(numLit "1")]) "^" (numLit "2")))
             "+"
             (Cardinal.SetTheory.Cofinality.«term_^_» (Term.app `f [(numLit "2")]) "^" (numLit "2")))
            "+"
            (Cardinal.SetTheory.Cofinality.«term_^_» (Term.app `f [(numLit "3")]) "^" (numLit "2")))
           "="
           (numLit "0"))
          "→"
          («term∃_,_»
           "∃"
           (Lean.explicitBinders
            (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] [":" (Term.app `Finₓ [(numLit "4")])]))
           ","
           («term_∧_»
            («term_=_»
             (Init.Logic.«term_+_»
              (Cardinal.SetTheory.Cofinality.«term_^_» (Term.app `f [`i]) "^" (numLit "2"))
              "+"
              (Cardinal.SetTheory.Cofinality.«term_^_»
               (Term.app `f [(Term.app `swap [`i (numLit "0") (numLit "1")])])
               "^"
               (numLit "2")))
             "="
             (numLit "0"))
            "∧"
            («term_=_»
             (Init.Logic.«term_+_»
              (Cardinal.SetTheory.Cofinality.«term_^_»
               (Term.app `f [(Term.app `swap [`i (numLit "0") (numLit "2")])])
               "^"
               (numLit "2"))
              "+"
              (Cardinal.SetTheory.Cofinality.«term_^_»
               (Term.app `f [(Term.app `swap [`i (numLit "0") (numLit "3")])])
               "^"
               (numLit "2")))
             "="
             (numLit "0")))))))]
      ":="
      (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.decide "decide") [])])))))
    []
    (Term.let
     "let"
     (Term.letDecl
      (Term.letIdDecl
       `f
       []
       [(Term.typeSpec ":" (Term.arrow (Term.app `Finₓ [(numLit "4")]) "→" (termℤ "ℤ")))]
       ":="
       (Term.app
        `Vector.nth
        [(Vector.Data.Vector.Basic.«term_::ᵥ_»
          `a
          "::ᵥ"
          (Vector.Data.Vector.Basic.«term_::ᵥ_»
           `b
           "::ᵥ"
           (Vector.Data.Vector.Basic.«term_::ᵥ_»
            `c
            "::ᵥ"
            (Vector.Data.Vector.Basic.«term_::ᵥ_» `d "::ᵥ" `Vector.nil))))])))
     []
     (Term.let
      "let"
      (Term.letDecl
       (Term.letPatDecl
        (Term.anonymousCtor "⟨" [`i "," `hσ] "⟩")
        []
        []
        ":="
        (Term.app
         `this
         [(«term_∘_» `coeₓ "∘" `f)
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group
               (Tactic.«tactic_<;>_»
                (Tactic.rwSeq
                 "rw"
                 []
                 (Tactic.rwRuleSeq
                  "["
                  [(Tactic.rwRule
                    ["←"]
                    (Term.app (Term.explicit "@" `zero_mul) [(Term.app `Zmod [(numLit "2")]) (Term.hole "_") `m]))
                   ","
                   (Tactic.rwRule
                    ["←"]
                    (Term.show
                     "show"
                     («term_=_»
                      (Term.paren
                       "("
                       [(Term.paren "(" [(numLit "2") [(Term.typeAscription ":" (termℤ "ℤ"))]] ")")
                        [(Term.typeAscription ":" (Term.app `Zmod [(numLit "2")]))]]
                       ")")
                      "="
                      (numLit "0"))
                     (Term.fromTerm "from" `rfl)))
                   ","
                   (Tactic.rwRule ["←"] `Int.cast_mul)
                   ","
                   (Tactic.rwRule ["←"] `h)]
                  "]")
                 [])
                "<;>"
                (Tactic.«tactic_<;>_»
                 (Tactic.simp
                  "simp"
                  []
                  ["only"]
                  ["[" [(Tactic.simpLemma [] [] `Int.cast_add) "," (Tactic.simpLemma [] [] `Int.cast_pow)] "]"]
                  [])
                 "<;>"
                 (Tactic.tacticRfl "rfl")))
               [])])))])))
      []
      (Term.let
       "let"
       (Term.letDecl (Term.letIdDecl `σ [] [] ":=" (Term.app `swap [`i (numLit "0")])))
       []
       (Term.have
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`h01 []]
          [(Term.typeSpec
            ":"
            (Init.Core.«term_∣_»
             (numLit "2")
             " ∣ "
             (Init.Logic.«term_+_»
              (Cardinal.SetTheory.Cofinality.«term_^_» (Term.app `f [(Term.app `σ [(numLit "0")])]) "^" (numLit "2"))
              "+"
              (Cardinal.SetTheory.Cofinality.«term_^_»
               (Term.app `f [(Term.app `σ [(numLit "1")])])
               "^"
               (numLit "2")))))]
          ":="
          («term_$__»
           (Term.proj
            (Term.app `CharP.int_cast_eq_zero_iff [(Term.app `Zmod [(numLit "2")]) (numLit "2") (Term.hole "_")])
            "."
            (fieldIdx "1"))
           "$"
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(group
                (Tactic.simpa
                 "simpa"
                 []
                 []
                 ["[" [(Tactic.simpLemma [] [] `σ)] "]"]
                 []
                 ["using" (Term.proj `hσ "." (fieldIdx "1"))])
                [])]))))))
        []
        (Term.have
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`h23 []]
           [(Term.typeSpec
             ":"
             (Init.Core.«term_∣_»
              (numLit "2")
              " ∣ "
              (Init.Logic.«term_+_»
               (Cardinal.SetTheory.Cofinality.«term_^_» (Term.app `f [(Term.app `σ [(numLit "2")])]) "^" (numLit "2"))
               "+"
               (Cardinal.SetTheory.Cofinality.«term_^_»
                (Term.app `f [(Term.app `σ [(numLit "3")])])
                "^"
                (numLit "2")))))]
           ":="
           («term_$__»
            (Term.proj
             (Term.app `CharP.int_cast_eq_zero_iff [(Term.app `Zmod [(numLit "2")]) (numLit "2") (Term.hole "_")])
             "."
             (fieldIdx "1"))
            "$"
            (Term.byTactic
             "by"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(group (Tactic.simpa "simpa" [] [] [] [] ["using" (Term.proj `hσ "." (fieldIdx "2"))]) [])]))))))
         []
         (Term.let
          "let"
          (Term.letDecl (Term.letPatDecl (Term.anonymousCtor "⟨" [`x "," `hx] "⟩") [] [] ":=" `h01))
          []
          (Term.let
           "let"
           (Term.letDecl (Term.letPatDecl (Term.anonymousCtor "⟨" [`y "," `hy] "⟩") [] [] ":=" `h23))
           []
           (Term.anonymousCtor
            "⟨"
            [(«term_/_»
              («term_-_» (Term.app `f [(Term.app `σ [(numLit "0")])]) "-" (Term.app `f [(Term.app `σ [(numLit "1")])]))
              "/"
              (numLit "2"))
             ","
             («term_/_»
              (Init.Logic.«term_+_»
               (Term.app `f [(Term.app `σ [(numLit "0")])])
               "+"
               (Term.app `f [(Term.app `σ [(numLit "1")])]))
              "/"
              (numLit "2"))
             ","
             («term_/_»
              («term_-_» (Term.app `f [(Term.app `σ [(numLit "2")])]) "-" (Term.app `f [(Term.app `σ [(numLit "3")])]))
              "/"
              (numLit "2"))
             ","
             («term_/_»
              (Init.Logic.«term_+_»
               (Term.app `f [(Term.app `σ [(numLit "2")])])
               "+"
               (Term.app `f [(Term.app `σ [(numLit "3")])]))
              "/"
              (numLit "2"))
             ","
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
                    [(Tactic.rwRule ["←"] (Term.app `Int.sq_add_sq_of_two_mul_sq_add_sq [`hx.symm]))
                     ","
                     (Tactic.rwRule [] `add_assocₓ)
                     ","
                     (Tactic.rwRule ["←"] (Term.app `Int.sq_add_sq_of_two_mul_sq_add_sq [`hy.symm]))
                     ","
                     (Tactic.rwRule
                      ["←"]
                      (Term.app
                       `mul_right_inj'
                       [(Term.show
                         "show"
                         («term_≠_»
                          (Term.paren "(" [(numLit "2") [(Term.typeAscription ":" (termℤ "ℤ"))]] ")")
                          "≠"
                          (numLit "0"))
                         (Term.fromTerm
                          "from"
                          (Term.byTactic
                           "by"
                           (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.decide "decide") [])])))))]))
                     ","
                     (Tactic.rwRule ["←"] `h)
                     ","
                     (Tactic.rwRule [] `mul_addₓ)
                     ","
                     (Tactic.rwRule ["←"] `hx)
                     ","
                     (Tactic.rwRule ["←"] `hy)]
                    "]")
                   [])
                  [])
                 (group
                  (Tactic.tacticHave_
                   "have"
                   (Term.haveDecl
                    (Term.haveIdDecl
                     []
                     [(Term.typeSpec
                       ":"
                       («term_=_»
                        (Algebra.BigOperators.Basic.«term∑_,_»
                         "∑"
                         (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
                         ", "
                         (Cardinal.SetTheory.Cofinality.«term_^_» (Term.app `f [(Term.app `σ [`x])]) "^" (numLit "2")))
                        "="
                        (Algebra.BigOperators.Basic.«term∑_,_»
                         "∑"
                         (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
                         ", "
                         (Cardinal.SetTheory.Cofinality.«term_^_» (Term.app `f [`x]) "^" (numLit "2")))))]
                     ":="
                     (Term.byTactic
                      "by"
                      (Tactic.tacticSeq
                       (Tactic.tacticSeq1Indented
                        [(group
                          (Mathlib.Tactic.Conv.convRHS
                           "conv_rhs"
                           []
                           []
                           "=>"
                           (Tactic.Conv.convSeq
                            (Tactic.Conv.convSeq1Indented
                             [(group
                               (Tactic.Conv.convRw__
                                "rw"
                                []
                                (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `σ.sum_comp)] "]"))
                               [])])))
                          [])]))))))
                  [])
                 (group
                  (Tactic.have''
                   "have"
                   [`fin4univ []]
                   [(Term.typeSpec
                     ":"
                     («term_=_»
                      (Term.proj
                       (Term.paren
                        "("
                        [`univ [(Term.typeAscription ":" (Term.app `Finset [(Term.app `Finₓ [(numLit "4")])]))]]
                        ")")
                       "."
                       (fieldIdx "1"))
                      "="
                      (Multiset.Data.Multiset.Basic.«term_::ₘ_»
                       (numLit "0")
                       " ::ₘ "
                       (Multiset.Data.Multiset.Basic.«term_::ₘ_»
                        (numLit "1")
                        " ::ₘ "
                        (Multiset.Data.Multiset.Basic.«term_::ₘ_»
                         (numLit "2")
                         " ::ₘ "
                         (Multiset.Data.Multiset.Basic.«term_::ₘ_» (numLit "3") " ::ₘ " (numLit "0")))))))])
                  [])
                 (group
                  (Tactic.exact
                   "exact"
                   (Term.byTactic
                    "by"
                    (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.decide "decide") [])]))))
                  [])
                 (group
                  (Tactic.simpa
                   "simpa"
                   []
                   []
                   ["["
                    [(Tactic.simpLemma [] [] `Finset.sum_eq_multiset_sum)
                     ","
                     (Tactic.simpLemma [] [] `fin4univ)
                     ","
                     (Tactic.simpLemma [] [] `Multiset.sum_cons)
                     ","
                     (Tactic.simpLemma [] [] `f)
                     ","
                     (Tactic.simpLemma [] [] `add_assocₓ)]
                    "]"]
                   []
                   [])
                  [])])))]
            "⟩")))))))))
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
  (Term.have
   "have"
   (Term.haveDecl
    (Term.haveIdDecl
     []
     [(Term.typeSpec
       ":"
       (Term.forall
        "∀"
        [(Term.simpleBinder
          [`f]
          [(Term.typeSpec ":" (Term.arrow (Term.app `Finₓ [(numLit "4")]) "→" (Term.app `Zmod [(numLit "2")])))])]
        ","
        (Term.arrow
         («term_=_»
          (Init.Logic.«term_+_»
           (Init.Logic.«term_+_»
            (Init.Logic.«term_+_»
             (Cardinal.SetTheory.Cofinality.«term_^_» (Term.app `f [(numLit "0")]) "^" (numLit "2"))
             "+"
             (Cardinal.SetTheory.Cofinality.«term_^_» (Term.app `f [(numLit "1")]) "^" (numLit "2")))
            "+"
            (Cardinal.SetTheory.Cofinality.«term_^_» (Term.app `f [(numLit "2")]) "^" (numLit "2")))
           "+"
           (Cardinal.SetTheory.Cofinality.«term_^_» (Term.app `f [(numLit "3")]) "^" (numLit "2")))
          "="
          (numLit "0"))
         "→"
         («term∃_,_»
          "∃"
          (Lean.explicitBinders
           (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] [":" (Term.app `Finₓ [(numLit "4")])]))
          ","
          («term_∧_»
           («term_=_»
            (Init.Logic.«term_+_»
             (Cardinal.SetTheory.Cofinality.«term_^_» (Term.app `f [`i]) "^" (numLit "2"))
             "+"
             (Cardinal.SetTheory.Cofinality.«term_^_»
              (Term.app `f [(Term.app `swap [`i (numLit "0") (numLit "1")])])
              "^"
              (numLit "2")))
            "="
            (numLit "0"))
           "∧"
           («term_=_»
            (Init.Logic.«term_+_»
             (Cardinal.SetTheory.Cofinality.«term_^_»
              (Term.app `f [(Term.app `swap [`i (numLit "0") (numLit "2")])])
              "^"
              (numLit "2"))
             "+"
             (Cardinal.SetTheory.Cofinality.«term_^_»
              (Term.app `f [(Term.app `swap [`i (numLit "0") (numLit "3")])])
              "^"
              (numLit "2")))
            "="
            (numLit "0")))))))]
     ":="
     (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.decide "decide") [])])))))
   []
   (Term.let
    "let"
    (Term.letDecl
     (Term.letIdDecl
      `f
      []
      [(Term.typeSpec ":" (Term.arrow (Term.app `Finₓ [(numLit "4")]) "→" (termℤ "ℤ")))]
      ":="
      (Term.app
       `Vector.nth
       [(Vector.Data.Vector.Basic.«term_::ᵥ_»
         `a
         "::ᵥ"
         (Vector.Data.Vector.Basic.«term_::ᵥ_»
          `b
          "::ᵥ"
          (Vector.Data.Vector.Basic.«term_::ᵥ_»
           `c
           "::ᵥ"
           (Vector.Data.Vector.Basic.«term_::ᵥ_» `d "::ᵥ" `Vector.nil))))])))
    []
    (Term.let
     "let"
     (Term.letDecl
      (Term.letPatDecl
       (Term.anonymousCtor "⟨" [`i "," `hσ] "⟩")
       []
       []
       ":="
       (Term.app
        `this
        [(«term_∘_» `coeₓ "∘" `f)
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(group
              (Tactic.«tactic_<;>_»
               (Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule
                   ["←"]
                   (Term.app (Term.explicit "@" `zero_mul) [(Term.app `Zmod [(numLit "2")]) (Term.hole "_") `m]))
                  ","
                  (Tactic.rwRule
                   ["←"]
                   (Term.show
                    "show"
                    («term_=_»
                     (Term.paren
                      "("
                      [(Term.paren "(" [(numLit "2") [(Term.typeAscription ":" (termℤ "ℤ"))]] ")")
                       [(Term.typeAscription ":" (Term.app `Zmod [(numLit "2")]))]]
                      ")")
                     "="
                     (numLit "0"))
                    (Term.fromTerm "from" `rfl)))
                  ","
                  (Tactic.rwRule ["←"] `Int.cast_mul)
                  ","
                  (Tactic.rwRule ["←"] `h)]
                 "]")
                [])
               "<;>"
               (Tactic.«tactic_<;>_»
                (Tactic.simp
                 "simp"
                 []
                 ["only"]
                 ["[" [(Tactic.simpLemma [] [] `Int.cast_add) "," (Tactic.simpLemma [] [] `Int.cast_pow)] "]"]
                 [])
                "<;>"
                (Tactic.tacticRfl "rfl")))
              [])])))])))
     []
     (Term.let
      "let"
      (Term.letDecl (Term.letIdDecl `σ [] [] ":=" (Term.app `swap [`i (numLit "0")])))
      []
      (Term.have
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`h01 []]
         [(Term.typeSpec
           ":"
           (Init.Core.«term_∣_»
            (numLit "2")
            " ∣ "
            (Init.Logic.«term_+_»
             (Cardinal.SetTheory.Cofinality.«term_^_» (Term.app `f [(Term.app `σ [(numLit "0")])]) "^" (numLit "2"))
             "+"
             (Cardinal.SetTheory.Cofinality.«term_^_» (Term.app `f [(Term.app `σ [(numLit "1")])]) "^" (numLit "2")))))]
         ":="
         («term_$__»
          (Term.proj
           (Term.app `CharP.int_cast_eq_zero_iff [(Term.app `Zmod [(numLit "2")]) (numLit "2") (Term.hole "_")])
           "."
           (fieldIdx "1"))
          "$"
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group
               (Tactic.simpa
                "simpa"
                []
                []
                ["[" [(Tactic.simpLemma [] [] `σ)] "]"]
                []
                ["using" (Term.proj `hσ "." (fieldIdx "1"))])
               [])]))))))
       []
       (Term.have
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`h23 []]
          [(Term.typeSpec
            ":"
            (Init.Core.«term_∣_»
             (numLit "2")
             " ∣ "
             (Init.Logic.«term_+_»
              (Cardinal.SetTheory.Cofinality.«term_^_» (Term.app `f [(Term.app `σ [(numLit "2")])]) "^" (numLit "2"))
              "+"
              (Cardinal.SetTheory.Cofinality.«term_^_»
               (Term.app `f [(Term.app `σ [(numLit "3")])])
               "^"
               (numLit "2")))))]
          ":="
          («term_$__»
           (Term.proj
            (Term.app `CharP.int_cast_eq_zero_iff [(Term.app `Zmod [(numLit "2")]) (numLit "2") (Term.hole "_")])
            "."
            (fieldIdx "1"))
           "$"
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(group (Tactic.simpa "simpa" [] [] [] [] ["using" (Term.proj `hσ "." (fieldIdx "2"))]) [])]))))))
        []
        (Term.let
         "let"
         (Term.letDecl (Term.letPatDecl (Term.anonymousCtor "⟨" [`x "," `hx] "⟩") [] [] ":=" `h01))
         []
         (Term.let
          "let"
          (Term.letDecl (Term.letPatDecl (Term.anonymousCtor "⟨" [`y "," `hy] "⟩") [] [] ":=" `h23))
          []
          (Term.anonymousCtor
           "⟨"
           [(«term_/_»
             («term_-_» (Term.app `f [(Term.app `σ [(numLit "0")])]) "-" (Term.app `f [(Term.app `σ [(numLit "1")])]))
             "/"
             (numLit "2"))
            ","
            («term_/_»
             (Init.Logic.«term_+_»
              (Term.app `f [(Term.app `σ [(numLit "0")])])
              "+"
              (Term.app `f [(Term.app `σ [(numLit "1")])]))
             "/"
             (numLit "2"))
            ","
            («term_/_»
             («term_-_» (Term.app `f [(Term.app `σ [(numLit "2")])]) "-" (Term.app `f [(Term.app `σ [(numLit "3")])]))
             "/"
             (numLit "2"))
            ","
            («term_/_»
             (Init.Logic.«term_+_»
              (Term.app `f [(Term.app `σ [(numLit "2")])])
              "+"
              (Term.app `f [(Term.app `σ [(numLit "3")])]))
             "/"
             (numLit "2"))
            ","
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
                   [(Tactic.rwRule ["←"] (Term.app `Int.sq_add_sq_of_two_mul_sq_add_sq [`hx.symm]))
                    ","
                    (Tactic.rwRule [] `add_assocₓ)
                    ","
                    (Tactic.rwRule ["←"] (Term.app `Int.sq_add_sq_of_two_mul_sq_add_sq [`hy.symm]))
                    ","
                    (Tactic.rwRule
                     ["←"]
                     (Term.app
                      `mul_right_inj'
                      [(Term.show
                        "show"
                        («term_≠_»
                         (Term.paren "(" [(numLit "2") [(Term.typeAscription ":" (termℤ "ℤ"))]] ")")
                         "≠"
                         (numLit "0"))
                        (Term.fromTerm
                         "from"
                         (Term.byTactic
                          "by"
                          (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.decide "decide") [])])))))]))
                    ","
                    (Tactic.rwRule ["←"] `h)
                    ","
                    (Tactic.rwRule [] `mul_addₓ)
                    ","
                    (Tactic.rwRule ["←"] `hx)
                    ","
                    (Tactic.rwRule ["←"] `hy)]
                   "]")
                  [])
                 [])
                (group
                 (Tactic.tacticHave_
                  "have"
                  (Term.haveDecl
                   (Term.haveIdDecl
                    []
                    [(Term.typeSpec
                      ":"
                      («term_=_»
                       (Algebra.BigOperators.Basic.«term∑_,_»
                        "∑"
                        (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
                        ", "
                        (Cardinal.SetTheory.Cofinality.«term_^_» (Term.app `f [(Term.app `σ [`x])]) "^" (numLit "2")))
                       "="
                       (Algebra.BigOperators.Basic.«term∑_,_»
                        "∑"
                        (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
                        ", "
                        (Cardinal.SetTheory.Cofinality.«term_^_» (Term.app `f [`x]) "^" (numLit "2")))))]
                    ":="
                    (Term.byTactic
                     "by"
                     (Tactic.tacticSeq
                      (Tactic.tacticSeq1Indented
                       [(group
                         (Mathlib.Tactic.Conv.convRHS
                          "conv_rhs"
                          []
                          []
                          "=>"
                          (Tactic.Conv.convSeq
                           (Tactic.Conv.convSeq1Indented
                            [(group
                              (Tactic.Conv.convRw__
                               "rw"
                               []
                               (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `σ.sum_comp)] "]"))
                              [])])))
                         [])]))))))
                 [])
                (group
                 (Tactic.have''
                  "have"
                  [`fin4univ []]
                  [(Term.typeSpec
                    ":"
                    («term_=_»
                     (Term.proj
                      (Term.paren
                       "("
                       [`univ [(Term.typeAscription ":" (Term.app `Finset [(Term.app `Finₓ [(numLit "4")])]))]]
                       ")")
                      "."
                      (fieldIdx "1"))
                     "="
                     (Multiset.Data.Multiset.Basic.«term_::ₘ_»
                      (numLit "0")
                      " ::ₘ "
                      (Multiset.Data.Multiset.Basic.«term_::ₘ_»
                       (numLit "1")
                       " ::ₘ "
                       (Multiset.Data.Multiset.Basic.«term_::ₘ_»
                        (numLit "2")
                        " ::ₘ "
                        (Multiset.Data.Multiset.Basic.«term_::ₘ_» (numLit "3") " ::ₘ " (numLit "0")))))))])
                 [])
                (group
                 (Tactic.exact
                  "exact"
                  (Term.byTactic
                   "by"
                   (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.decide "decide") [])]))))
                 [])
                (group
                 (Tactic.simpa
                  "simpa"
                  []
                  []
                  ["["
                   [(Tactic.simpLemma [] [] `Finset.sum_eq_multiset_sum)
                    ","
                    (Tactic.simpLemma [] [] `fin4univ)
                    ","
                    (Tactic.simpLemma [] [] `Multiset.sum_cons)
                    ","
                    (Tactic.simpLemma [] [] `f)
                    ","
                    (Tactic.simpLemma [] [] `add_assocₓ)]
                   "]"]
                  []
                  [])
                 [])])))]
           "⟩")))))))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.have', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.have', expected 'Lean.Parser.Term.have.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.let
   "let"
   (Term.letDecl
    (Term.letIdDecl
     `f
     []
     [(Term.typeSpec ":" (Term.arrow (Term.app `Finₓ [(numLit "4")]) "→" (termℤ "ℤ")))]
     ":="
     (Term.app
      `Vector.nth
      [(Vector.Data.Vector.Basic.«term_::ᵥ_»
        `a
        "::ᵥ"
        (Vector.Data.Vector.Basic.«term_::ᵥ_»
         `b
         "::ᵥ"
         (Vector.Data.Vector.Basic.«term_::ᵥ_»
          `c
          "::ᵥ"
          (Vector.Data.Vector.Basic.«term_::ᵥ_» `d "::ᵥ" `Vector.nil))))])))
   []
   (Term.let
    "let"
    (Term.letDecl
     (Term.letPatDecl
      (Term.anonymousCtor "⟨" [`i "," `hσ] "⟩")
      []
      []
      ":="
      (Term.app
       `this
       [(«term_∘_» `coeₓ "∘" `f)
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group
             (Tactic.«tactic_<;>_»
              (Tactic.rwSeq
               "rw"
               []
               (Tactic.rwRuleSeq
                "["
                [(Tactic.rwRule
                  ["←"]
                  (Term.app (Term.explicit "@" `zero_mul) [(Term.app `Zmod [(numLit "2")]) (Term.hole "_") `m]))
                 ","
                 (Tactic.rwRule
                  ["←"]
                  (Term.show
                   "show"
                   («term_=_»
                    (Term.paren
                     "("
                     [(Term.paren "(" [(numLit "2") [(Term.typeAscription ":" (termℤ "ℤ"))]] ")")
                      [(Term.typeAscription ":" (Term.app `Zmod [(numLit "2")]))]]
                     ")")
                    "="
                    (numLit "0"))
                   (Term.fromTerm "from" `rfl)))
                 ","
                 (Tactic.rwRule ["←"] `Int.cast_mul)
                 ","
                 (Tactic.rwRule ["←"] `h)]
                "]")
               [])
              "<;>"
              (Tactic.«tactic_<;>_»
               (Tactic.simp
                "simp"
                []
                ["only"]
                ["[" [(Tactic.simpLemma [] [] `Int.cast_add) "," (Tactic.simpLemma [] [] `Int.cast_pow)] "]"]
                [])
               "<;>"
               (Tactic.tacticRfl "rfl")))
             [])])))])))
    []
    (Term.let
     "let"
     (Term.letDecl (Term.letIdDecl `σ [] [] ":=" (Term.app `swap [`i (numLit "0")])))
     []
     (Term.have
      "have"
      (Term.haveDecl
       (Term.haveIdDecl
        [`h01 []]
        [(Term.typeSpec
          ":"
          (Init.Core.«term_∣_»
           (numLit "2")
           " ∣ "
           (Init.Logic.«term_+_»
            (Cardinal.SetTheory.Cofinality.«term_^_» (Term.app `f [(Term.app `σ [(numLit "0")])]) "^" (numLit "2"))
            "+"
            (Cardinal.SetTheory.Cofinality.«term_^_» (Term.app `f [(Term.app `σ [(numLit "1")])]) "^" (numLit "2")))))]
        ":="
        («term_$__»
         (Term.proj
          (Term.app `CharP.int_cast_eq_zero_iff [(Term.app `Zmod [(numLit "2")]) (numLit "2") (Term.hole "_")])
          "."
          (fieldIdx "1"))
         "$"
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(group
              (Tactic.simpa
               "simpa"
               []
               []
               ["[" [(Tactic.simpLemma [] [] `σ)] "]"]
               []
               ["using" (Term.proj `hσ "." (fieldIdx "1"))])
              [])]))))))
      []
      (Term.have
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`h23 []]
         [(Term.typeSpec
           ":"
           (Init.Core.«term_∣_»
            (numLit "2")
            " ∣ "
            (Init.Logic.«term_+_»
             (Cardinal.SetTheory.Cofinality.«term_^_» (Term.app `f [(Term.app `σ [(numLit "2")])]) "^" (numLit "2"))
             "+"
             (Cardinal.SetTheory.Cofinality.«term_^_» (Term.app `f [(Term.app `σ [(numLit "3")])]) "^" (numLit "2")))))]
         ":="
         («term_$__»
          (Term.proj
           (Term.app `CharP.int_cast_eq_zero_iff [(Term.app `Zmod [(numLit "2")]) (numLit "2") (Term.hole "_")])
           "."
           (fieldIdx "1"))
          "$"
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group (Tactic.simpa "simpa" [] [] [] [] ["using" (Term.proj `hσ "." (fieldIdx "2"))]) [])]))))))
       []
       (Term.let
        "let"
        (Term.letDecl (Term.letPatDecl (Term.anonymousCtor "⟨" [`x "," `hx] "⟩") [] [] ":=" `h01))
        []
        (Term.let
         "let"
         (Term.letDecl (Term.letPatDecl (Term.anonymousCtor "⟨" [`y "," `hy] "⟩") [] [] ":=" `h23))
         []
         (Term.anonymousCtor
          "⟨"
          [(«term_/_»
            («term_-_» (Term.app `f [(Term.app `σ [(numLit "0")])]) "-" (Term.app `f [(Term.app `σ [(numLit "1")])]))
            "/"
            (numLit "2"))
           ","
           («term_/_»
            (Init.Logic.«term_+_»
             (Term.app `f [(Term.app `σ [(numLit "0")])])
             "+"
             (Term.app `f [(Term.app `σ [(numLit "1")])]))
            "/"
            (numLit "2"))
           ","
           («term_/_»
            («term_-_» (Term.app `f [(Term.app `σ [(numLit "2")])]) "-" (Term.app `f [(Term.app `σ [(numLit "3")])]))
            "/"
            (numLit "2"))
           ","
           («term_/_»
            (Init.Logic.«term_+_»
             (Term.app `f [(Term.app `σ [(numLit "2")])])
             "+"
             (Term.app `f [(Term.app `σ [(numLit "3")])]))
            "/"
            (numLit "2"))
           ","
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
                  [(Tactic.rwRule ["←"] (Term.app `Int.sq_add_sq_of_two_mul_sq_add_sq [`hx.symm]))
                   ","
                   (Tactic.rwRule [] `add_assocₓ)
                   ","
                   (Tactic.rwRule ["←"] (Term.app `Int.sq_add_sq_of_two_mul_sq_add_sq [`hy.symm]))
                   ","
                   (Tactic.rwRule
                    ["←"]
                    (Term.app
                     `mul_right_inj'
                     [(Term.show
                       "show"
                       («term_≠_»
                        (Term.paren "(" [(numLit "2") [(Term.typeAscription ":" (termℤ "ℤ"))]] ")")
                        "≠"
                        (numLit "0"))
                       (Term.fromTerm
                        "from"
                        (Term.byTactic
                         "by"
                         (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.decide "decide") [])])))))]))
                   ","
                   (Tactic.rwRule ["←"] `h)
                   ","
                   (Tactic.rwRule [] `mul_addₓ)
                   ","
                   (Tactic.rwRule ["←"] `hx)
                   ","
                   (Tactic.rwRule ["←"] `hy)]
                  "]")
                 [])
                [])
               (group
                (Tactic.tacticHave_
                 "have"
                 (Term.haveDecl
                  (Term.haveIdDecl
                   []
                   [(Term.typeSpec
                     ":"
                     («term_=_»
                      (Algebra.BigOperators.Basic.«term∑_,_»
                       "∑"
                       (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
                       ", "
                       (Cardinal.SetTheory.Cofinality.«term_^_» (Term.app `f [(Term.app `σ [`x])]) "^" (numLit "2")))
                      "="
                      (Algebra.BigOperators.Basic.«term∑_,_»
                       "∑"
                       (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
                       ", "
                       (Cardinal.SetTheory.Cofinality.«term_^_» (Term.app `f [`x]) "^" (numLit "2")))))]
                   ":="
                   (Term.byTactic
                    "by"
                    (Tactic.tacticSeq
                     (Tactic.tacticSeq1Indented
                      [(group
                        (Mathlib.Tactic.Conv.convRHS
                         "conv_rhs"
                         []
                         []
                         "=>"
                         (Tactic.Conv.convSeq
                          (Tactic.Conv.convSeq1Indented
                           [(group
                             (Tactic.Conv.convRw__
                              "rw"
                              []
                              (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `σ.sum_comp)] "]"))
                             [])])))
                        [])]))))))
                [])
               (group
                (Tactic.have''
                 "have"
                 [`fin4univ []]
                 [(Term.typeSpec
                   ":"
                   («term_=_»
                    (Term.proj
                     (Term.paren
                      "("
                      [`univ [(Term.typeAscription ":" (Term.app `Finset [(Term.app `Finₓ [(numLit "4")])]))]]
                      ")")
                     "."
                     (fieldIdx "1"))
                    "="
                    (Multiset.Data.Multiset.Basic.«term_::ₘ_»
                     (numLit "0")
                     " ::ₘ "
                     (Multiset.Data.Multiset.Basic.«term_::ₘ_»
                      (numLit "1")
                      " ::ₘ "
                      (Multiset.Data.Multiset.Basic.«term_::ₘ_»
                       (numLit "2")
                       " ::ₘ "
                       (Multiset.Data.Multiset.Basic.«term_::ₘ_» (numLit "3") " ::ₘ " (numLit "0")))))))])
                [])
               (group
                (Tactic.exact
                 "exact"
                 (Term.byTactic
                  "by"
                  (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.decide "decide") [])]))))
                [])
               (group
                (Tactic.simpa
                 "simpa"
                 []
                 []
                 ["["
                  [(Tactic.simpLemma [] [] `Finset.sum_eq_multiset_sum)
                   ","
                   (Tactic.simpLemma [] [] `fin4univ)
                   ","
                   (Tactic.simpLemma [] [] `Multiset.sum_cons)
                   ","
                   (Tactic.simpLemma [] [] `f)
                   ","
                   (Tactic.simpLemma [] [] `add_assocₓ)]
                  "]"]
                 []
                 [])
                [])])))]
          "⟩"))))))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.let', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.let', expected 'Lean.Parser.Term.let.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.let
   "let"
   (Term.letDecl
    (Term.letPatDecl
     (Term.anonymousCtor "⟨" [`i "," `hσ] "⟩")
     []
     []
     ":="
     (Term.app
      `this
      [(«term_∘_» `coeₓ "∘" `f)
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group
            (Tactic.«tactic_<;>_»
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule
                 ["←"]
                 (Term.app (Term.explicit "@" `zero_mul) [(Term.app `Zmod [(numLit "2")]) (Term.hole "_") `m]))
                ","
                (Tactic.rwRule
                 ["←"]
                 (Term.show
                  "show"
                  («term_=_»
                   (Term.paren
                    "("
                    [(Term.paren "(" [(numLit "2") [(Term.typeAscription ":" (termℤ "ℤ"))]] ")")
                     [(Term.typeAscription ":" (Term.app `Zmod [(numLit "2")]))]]
                    ")")
                   "="
                   (numLit "0"))
                  (Term.fromTerm "from" `rfl)))
                ","
                (Tactic.rwRule ["←"] `Int.cast_mul)
                ","
                (Tactic.rwRule ["←"] `h)]
               "]")
              [])
             "<;>"
             (Tactic.«tactic_<;>_»
              (Tactic.simp
               "simp"
               []
               ["only"]
               ["[" [(Tactic.simpLemma [] [] `Int.cast_add) "," (Tactic.simpLemma [] [] `Int.cast_pow)] "]"]
               [])
              "<;>"
              (Tactic.tacticRfl "rfl")))
            [])])))])))
   []
   (Term.let
    "let"
    (Term.letDecl (Term.letIdDecl `σ [] [] ":=" (Term.app `swap [`i (numLit "0")])))
    []
    (Term.have
     "have"
     (Term.haveDecl
      (Term.haveIdDecl
       [`h01 []]
       [(Term.typeSpec
         ":"
         (Init.Core.«term_∣_»
          (numLit "2")
          " ∣ "
          (Init.Logic.«term_+_»
           (Cardinal.SetTheory.Cofinality.«term_^_» (Term.app `f [(Term.app `σ [(numLit "0")])]) "^" (numLit "2"))
           "+"
           (Cardinal.SetTheory.Cofinality.«term_^_» (Term.app `f [(Term.app `σ [(numLit "1")])]) "^" (numLit "2")))))]
       ":="
       («term_$__»
        (Term.proj
         (Term.app `CharP.int_cast_eq_zero_iff [(Term.app `Zmod [(numLit "2")]) (numLit "2") (Term.hole "_")])
         "."
         (fieldIdx "1"))
        "$"
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group
             (Tactic.simpa
              "simpa"
              []
              []
              ["[" [(Tactic.simpLemma [] [] `σ)] "]"]
              []
              ["using" (Term.proj `hσ "." (fieldIdx "1"))])
             [])]))))))
     []
     (Term.have
      "have"
      (Term.haveDecl
       (Term.haveIdDecl
        [`h23 []]
        [(Term.typeSpec
          ":"
          (Init.Core.«term_∣_»
           (numLit "2")
           " ∣ "
           (Init.Logic.«term_+_»
            (Cardinal.SetTheory.Cofinality.«term_^_» (Term.app `f [(Term.app `σ [(numLit "2")])]) "^" (numLit "2"))
            "+"
            (Cardinal.SetTheory.Cofinality.«term_^_» (Term.app `f [(Term.app `σ [(numLit "3")])]) "^" (numLit "2")))))]
        ":="
        («term_$__»
         (Term.proj
          (Term.app `CharP.int_cast_eq_zero_iff [(Term.app `Zmod [(numLit "2")]) (numLit "2") (Term.hole "_")])
          "."
          (fieldIdx "1"))
         "$"
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(group (Tactic.simpa "simpa" [] [] [] [] ["using" (Term.proj `hσ "." (fieldIdx "2"))]) [])]))))))
      []
      (Term.let
       "let"
       (Term.letDecl (Term.letPatDecl (Term.anonymousCtor "⟨" [`x "," `hx] "⟩") [] [] ":=" `h01))
       []
       (Term.let
        "let"
        (Term.letDecl (Term.letPatDecl (Term.anonymousCtor "⟨" [`y "," `hy] "⟩") [] [] ":=" `h23))
        []
        (Term.anonymousCtor
         "⟨"
         [(«term_/_»
           («term_-_» (Term.app `f [(Term.app `σ [(numLit "0")])]) "-" (Term.app `f [(Term.app `σ [(numLit "1")])]))
           "/"
           (numLit "2"))
          ","
          («term_/_»
           (Init.Logic.«term_+_»
            (Term.app `f [(Term.app `σ [(numLit "0")])])
            "+"
            (Term.app `f [(Term.app `σ [(numLit "1")])]))
           "/"
           (numLit "2"))
          ","
          («term_/_»
           («term_-_» (Term.app `f [(Term.app `σ [(numLit "2")])]) "-" (Term.app `f [(Term.app `σ [(numLit "3")])]))
           "/"
           (numLit "2"))
          ","
          («term_/_»
           (Init.Logic.«term_+_»
            (Term.app `f [(Term.app `σ [(numLit "2")])])
            "+"
            (Term.app `f [(Term.app `σ [(numLit "3")])]))
           "/"
           (numLit "2"))
          ","
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
                 [(Tactic.rwRule ["←"] (Term.app `Int.sq_add_sq_of_two_mul_sq_add_sq [`hx.symm]))
                  ","
                  (Tactic.rwRule [] `add_assocₓ)
                  ","
                  (Tactic.rwRule ["←"] (Term.app `Int.sq_add_sq_of_two_mul_sq_add_sq [`hy.symm]))
                  ","
                  (Tactic.rwRule
                   ["←"]
                   (Term.app
                    `mul_right_inj'
                    [(Term.show
                      "show"
                      («term_≠_»
                       (Term.paren "(" [(numLit "2") [(Term.typeAscription ":" (termℤ "ℤ"))]] ")")
                       "≠"
                       (numLit "0"))
                      (Term.fromTerm
                       "from"
                       (Term.byTactic
                        "by"
                        (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.decide "decide") [])])))))]))
                  ","
                  (Tactic.rwRule ["←"] `h)
                  ","
                  (Tactic.rwRule [] `mul_addₓ)
                  ","
                  (Tactic.rwRule ["←"] `hx)
                  ","
                  (Tactic.rwRule ["←"] `hy)]
                 "]")
                [])
               [])
              (group
               (Tactic.tacticHave_
                "have"
                (Term.haveDecl
                 (Term.haveIdDecl
                  []
                  [(Term.typeSpec
                    ":"
                    («term_=_»
                     (Algebra.BigOperators.Basic.«term∑_,_»
                      "∑"
                      (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
                      ", "
                      (Cardinal.SetTheory.Cofinality.«term_^_» (Term.app `f [(Term.app `σ [`x])]) "^" (numLit "2")))
                     "="
                     (Algebra.BigOperators.Basic.«term∑_,_»
                      "∑"
                      (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
                      ", "
                      (Cardinal.SetTheory.Cofinality.«term_^_» (Term.app `f [`x]) "^" (numLit "2")))))]
                  ":="
                  (Term.byTactic
                   "by"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented
                     [(group
                       (Mathlib.Tactic.Conv.convRHS
                        "conv_rhs"
                        []
                        []
                        "=>"
                        (Tactic.Conv.convSeq
                         (Tactic.Conv.convSeq1Indented
                          [(group
                            (Tactic.Conv.convRw__
                             "rw"
                             []
                             (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `σ.sum_comp)] "]"))
                            [])])))
                       [])]))))))
               [])
              (group
               (Tactic.have''
                "have"
                [`fin4univ []]
                [(Term.typeSpec
                  ":"
                  («term_=_»
                   (Term.proj
                    (Term.paren
                     "("
                     [`univ [(Term.typeAscription ":" (Term.app `Finset [(Term.app `Finₓ [(numLit "4")])]))]]
                     ")")
                    "."
                    (fieldIdx "1"))
                   "="
                   (Multiset.Data.Multiset.Basic.«term_::ₘ_»
                    (numLit "0")
                    " ::ₘ "
                    (Multiset.Data.Multiset.Basic.«term_::ₘ_»
                     (numLit "1")
                     " ::ₘ "
                     (Multiset.Data.Multiset.Basic.«term_::ₘ_»
                      (numLit "2")
                      " ::ₘ "
                      (Multiset.Data.Multiset.Basic.«term_::ₘ_» (numLit "3") " ::ₘ " (numLit "0")))))))])
               [])
              (group
               (Tactic.exact
                "exact"
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.decide "decide") [])]))))
               [])
              (group
               (Tactic.simpa
                "simpa"
                []
                []
                ["["
                 [(Tactic.simpLemma [] [] `Finset.sum_eq_multiset_sum)
                  ","
                  (Tactic.simpLemma [] [] `fin4univ)
                  ","
                  (Tactic.simpLemma [] [] `Multiset.sum_cons)
                  ","
                  (Tactic.simpLemma [] [] `f)
                  ","
                  (Tactic.simpLemma [] [] `add_assocₓ)]
                 "]"]
                []
                [])
               [])])))]
         "⟩")))))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.let', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.let', expected 'Lean.Parser.Term.let.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.let
   "let"
   (Term.letDecl (Term.letIdDecl `σ [] [] ":=" (Term.app `swap [`i (numLit "0")])))
   []
   (Term.have
    "have"
    (Term.haveDecl
     (Term.haveIdDecl
      [`h01 []]
      [(Term.typeSpec
        ":"
        (Init.Core.«term_∣_»
         (numLit "2")
         " ∣ "
         (Init.Logic.«term_+_»
          (Cardinal.SetTheory.Cofinality.«term_^_» (Term.app `f [(Term.app `σ [(numLit "0")])]) "^" (numLit "2"))
          "+"
          (Cardinal.SetTheory.Cofinality.«term_^_» (Term.app `f [(Term.app `σ [(numLit "1")])]) "^" (numLit "2")))))]
      ":="
      («term_$__»
       (Term.proj
        (Term.app `CharP.int_cast_eq_zero_iff [(Term.app `Zmod [(numLit "2")]) (numLit "2") (Term.hole "_")])
        "."
        (fieldIdx "1"))
       "$"
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group
            (Tactic.simpa
             "simpa"
             []
             []
             ["[" [(Tactic.simpLemma [] [] `σ)] "]"]
             []
             ["using" (Term.proj `hσ "." (fieldIdx "1"))])
            [])]))))))
    []
    (Term.have
     "have"
     (Term.haveDecl
      (Term.haveIdDecl
       [`h23 []]
       [(Term.typeSpec
         ":"
         (Init.Core.«term_∣_»
          (numLit "2")
          " ∣ "
          (Init.Logic.«term_+_»
           (Cardinal.SetTheory.Cofinality.«term_^_» (Term.app `f [(Term.app `σ [(numLit "2")])]) "^" (numLit "2"))
           "+"
           (Cardinal.SetTheory.Cofinality.«term_^_» (Term.app `f [(Term.app `σ [(numLit "3")])]) "^" (numLit "2")))))]
       ":="
       («term_$__»
        (Term.proj
         (Term.app `CharP.int_cast_eq_zero_iff [(Term.app `Zmod [(numLit "2")]) (numLit "2") (Term.hole "_")])
         "."
         (fieldIdx "1"))
        "$"
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group (Tactic.simpa "simpa" [] [] [] [] ["using" (Term.proj `hσ "." (fieldIdx "2"))]) [])]))))))
     []
     (Term.let
      "let"
      (Term.letDecl (Term.letPatDecl (Term.anonymousCtor "⟨" [`x "," `hx] "⟩") [] [] ":=" `h01))
      []
      (Term.let
       "let"
       (Term.letDecl (Term.letPatDecl (Term.anonymousCtor "⟨" [`y "," `hy] "⟩") [] [] ":=" `h23))
       []
       (Term.anonymousCtor
        "⟨"
        [(«term_/_»
          («term_-_» (Term.app `f [(Term.app `σ [(numLit "0")])]) "-" (Term.app `f [(Term.app `σ [(numLit "1")])]))
          "/"
          (numLit "2"))
         ","
         («term_/_»
          (Init.Logic.«term_+_»
           (Term.app `f [(Term.app `σ [(numLit "0")])])
           "+"
           (Term.app `f [(Term.app `σ [(numLit "1")])]))
          "/"
          (numLit "2"))
         ","
         («term_/_»
          («term_-_» (Term.app `f [(Term.app `σ [(numLit "2")])]) "-" (Term.app `f [(Term.app `σ [(numLit "3")])]))
          "/"
          (numLit "2"))
         ","
         («term_/_»
          (Init.Logic.«term_+_»
           (Term.app `f [(Term.app `σ [(numLit "2")])])
           "+"
           (Term.app `f [(Term.app `σ [(numLit "3")])]))
          "/"
          (numLit "2"))
         ","
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
                [(Tactic.rwRule ["←"] (Term.app `Int.sq_add_sq_of_two_mul_sq_add_sq [`hx.symm]))
                 ","
                 (Tactic.rwRule [] `add_assocₓ)
                 ","
                 (Tactic.rwRule ["←"] (Term.app `Int.sq_add_sq_of_two_mul_sq_add_sq [`hy.symm]))
                 ","
                 (Tactic.rwRule
                  ["←"]
                  (Term.app
                   `mul_right_inj'
                   [(Term.show
                     "show"
                     («term_≠_»
                      (Term.paren "(" [(numLit "2") [(Term.typeAscription ":" (termℤ "ℤ"))]] ")")
                      "≠"
                      (numLit "0"))
                     (Term.fromTerm
                      "from"
                      (Term.byTactic
                       "by"
                       (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.decide "decide") [])])))))]))
                 ","
                 (Tactic.rwRule ["←"] `h)
                 ","
                 (Tactic.rwRule [] `mul_addₓ)
                 ","
                 (Tactic.rwRule ["←"] `hx)
                 ","
                 (Tactic.rwRule ["←"] `hy)]
                "]")
               [])
              [])
             (group
              (Tactic.tacticHave_
               "have"
               (Term.haveDecl
                (Term.haveIdDecl
                 []
                 [(Term.typeSpec
                   ":"
                   («term_=_»
                    (Algebra.BigOperators.Basic.«term∑_,_»
                     "∑"
                     (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
                     ", "
                     (Cardinal.SetTheory.Cofinality.«term_^_» (Term.app `f [(Term.app `σ [`x])]) "^" (numLit "2")))
                    "="
                    (Algebra.BigOperators.Basic.«term∑_,_»
                     "∑"
                     (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
                     ", "
                     (Cardinal.SetTheory.Cofinality.«term_^_» (Term.app `f [`x]) "^" (numLit "2")))))]
                 ":="
                 (Term.byTactic
                  "by"
                  (Tactic.tacticSeq
                   (Tactic.tacticSeq1Indented
                    [(group
                      (Mathlib.Tactic.Conv.convRHS
                       "conv_rhs"
                       []
                       []
                       "=>"
                       (Tactic.Conv.convSeq
                        (Tactic.Conv.convSeq1Indented
                         [(group
                           (Tactic.Conv.convRw__ "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `σ.sum_comp)] "]"))
                           [])])))
                      [])]))))))
              [])
             (group
              (Tactic.have''
               "have"
               [`fin4univ []]
               [(Term.typeSpec
                 ":"
                 («term_=_»
                  (Term.proj
                   (Term.paren
                    "("
                    [`univ [(Term.typeAscription ":" (Term.app `Finset [(Term.app `Finₓ [(numLit "4")])]))]]
                    ")")
                   "."
                   (fieldIdx "1"))
                  "="
                  (Multiset.Data.Multiset.Basic.«term_::ₘ_»
                   (numLit "0")
                   " ::ₘ "
                   (Multiset.Data.Multiset.Basic.«term_::ₘ_»
                    (numLit "1")
                    " ::ₘ "
                    (Multiset.Data.Multiset.Basic.«term_::ₘ_»
                     (numLit "2")
                     " ::ₘ "
                     (Multiset.Data.Multiset.Basic.«term_::ₘ_» (numLit "3") " ::ₘ " (numLit "0")))))))])
              [])
             (group
              (Tactic.exact
               "exact"
               (Term.byTactic
                "by"
                (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.decide "decide") [])]))))
              [])
             (group
              (Tactic.simpa
               "simpa"
               []
               []
               ["["
                [(Tactic.simpLemma [] [] `Finset.sum_eq_multiset_sum)
                 ","
                 (Tactic.simpLemma [] [] `fin4univ)
                 ","
                 (Tactic.simpLemma [] [] `Multiset.sum_cons)
                 ","
                 (Tactic.simpLemma [] [] `f)
                 ","
                 (Tactic.simpLemma [] [] `add_assocₓ)]
                "]"]
               []
               [])
              [])])))]
        "⟩"))))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.let', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.let', expected 'Lean.Parser.Term.let.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.have
   "have"
   (Term.haveDecl
    (Term.haveIdDecl
     [`h01 []]
     [(Term.typeSpec
       ":"
       (Init.Core.«term_∣_»
        (numLit "2")
        " ∣ "
        (Init.Logic.«term_+_»
         (Cardinal.SetTheory.Cofinality.«term_^_» (Term.app `f [(Term.app `σ [(numLit "0")])]) "^" (numLit "2"))
         "+"
         (Cardinal.SetTheory.Cofinality.«term_^_» (Term.app `f [(Term.app `σ [(numLit "1")])]) "^" (numLit "2")))))]
     ":="
     («term_$__»
      (Term.proj
       (Term.app `CharP.int_cast_eq_zero_iff [(Term.app `Zmod [(numLit "2")]) (numLit "2") (Term.hole "_")])
       "."
       (fieldIdx "1"))
      "$"
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(group
           (Tactic.simpa
            "simpa"
            []
            []
            ["[" [(Tactic.simpLemma [] [] `σ)] "]"]
            []
            ["using" (Term.proj `hσ "." (fieldIdx "1"))])
           [])]))))))
   []
   (Term.have
    "have"
    (Term.haveDecl
     (Term.haveIdDecl
      [`h23 []]
      [(Term.typeSpec
        ":"
        (Init.Core.«term_∣_»
         (numLit "2")
         " ∣ "
         (Init.Logic.«term_+_»
          (Cardinal.SetTheory.Cofinality.«term_^_» (Term.app `f [(Term.app `σ [(numLit "2")])]) "^" (numLit "2"))
          "+"
          (Cardinal.SetTheory.Cofinality.«term_^_» (Term.app `f [(Term.app `σ [(numLit "3")])]) "^" (numLit "2")))))]
      ":="
      («term_$__»
       (Term.proj
        (Term.app `CharP.int_cast_eq_zero_iff [(Term.app `Zmod [(numLit "2")]) (numLit "2") (Term.hole "_")])
        "."
        (fieldIdx "1"))
       "$"
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group (Tactic.simpa "simpa" [] [] [] [] ["using" (Term.proj `hσ "." (fieldIdx "2"))]) [])]))))))
    []
    (Term.let
     "let"
     (Term.letDecl (Term.letPatDecl (Term.anonymousCtor "⟨" [`x "," `hx] "⟩") [] [] ":=" `h01))
     []
     (Term.let
      "let"
      (Term.letDecl (Term.letPatDecl (Term.anonymousCtor "⟨" [`y "," `hy] "⟩") [] [] ":=" `h23))
      []
      (Term.anonymousCtor
       "⟨"
       [(«term_/_»
         («term_-_» (Term.app `f [(Term.app `σ [(numLit "0")])]) "-" (Term.app `f [(Term.app `σ [(numLit "1")])]))
         "/"
         (numLit "2"))
        ","
        («term_/_»
         (Init.Logic.«term_+_»
          (Term.app `f [(Term.app `σ [(numLit "0")])])
          "+"
          (Term.app `f [(Term.app `σ [(numLit "1")])]))
         "/"
         (numLit "2"))
        ","
        («term_/_»
         («term_-_» (Term.app `f [(Term.app `σ [(numLit "2")])]) "-" (Term.app `f [(Term.app `σ [(numLit "3")])]))
         "/"
         (numLit "2"))
        ","
        («term_/_»
         (Init.Logic.«term_+_»
          (Term.app `f [(Term.app `σ [(numLit "2")])])
          "+"
          (Term.app `f [(Term.app `σ [(numLit "3")])]))
         "/"
         (numLit "2"))
        ","
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
               [(Tactic.rwRule ["←"] (Term.app `Int.sq_add_sq_of_two_mul_sq_add_sq [`hx.symm]))
                ","
                (Tactic.rwRule [] `add_assocₓ)
                ","
                (Tactic.rwRule ["←"] (Term.app `Int.sq_add_sq_of_two_mul_sq_add_sq [`hy.symm]))
                ","
                (Tactic.rwRule
                 ["←"]
                 (Term.app
                  `mul_right_inj'
                  [(Term.show
                    "show"
                    («term_≠_»
                     (Term.paren "(" [(numLit "2") [(Term.typeAscription ":" (termℤ "ℤ"))]] ")")
                     "≠"
                     (numLit "0"))
                    (Term.fromTerm
                     "from"
                     (Term.byTactic
                      "by"
                      (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.decide "decide") [])])))))]))
                ","
                (Tactic.rwRule ["←"] `h)
                ","
                (Tactic.rwRule [] `mul_addₓ)
                ","
                (Tactic.rwRule ["←"] `hx)
                ","
                (Tactic.rwRule ["←"] `hy)]
               "]")
              [])
             [])
            (group
             (Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                []
                [(Term.typeSpec
                  ":"
                  («term_=_»
                   (Algebra.BigOperators.Basic.«term∑_,_»
                    "∑"
                    (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
                    ", "
                    (Cardinal.SetTheory.Cofinality.«term_^_» (Term.app `f [(Term.app `σ [`x])]) "^" (numLit "2")))
                   "="
                   (Algebra.BigOperators.Basic.«term∑_,_»
                    "∑"
                    (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
                    ", "
                    (Cardinal.SetTheory.Cofinality.«term_^_» (Term.app `f [`x]) "^" (numLit "2")))))]
                ":="
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(group
                     (Mathlib.Tactic.Conv.convRHS
                      "conv_rhs"
                      []
                      []
                      "=>"
                      (Tactic.Conv.convSeq
                       (Tactic.Conv.convSeq1Indented
                        [(group
                          (Tactic.Conv.convRw__ "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `σ.sum_comp)] "]"))
                          [])])))
                     [])]))))))
             [])
            (group
             (Tactic.have''
              "have"
              [`fin4univ []]
              [(Term.typeSpec
                ":"
                («term_=_»
                 (Term.proj
                  (Term.paren
                   "("
                   [`univ [(Term.typeAscription ":" (Term.app `Finset [(Term.app `Finₓ [(numLit "4")])]))]]
                   ")")
                  "."
                  (fieldIdx "1"))
                 "="
                 (Multiset.Data.Multiset.Basic.«term_::ₘ_»
                  (numLit "0")
                  " ::ₘ "
                  (Multiset.Data.Multiset.Basic.«term_::ₘ_»
                   (numLit "1")
                   " ::ₘ "
                   (Multiset.Data.Multiset.Basic.«term_::ₘ_»
                    (numLit "2")
                    " ::ₘ "
                    (Multiset.Data.Multiset.Basic.«term_::ₘ_» (numLit "3") " ::ₘ " (numLit "0")))))))])
             [])
            (group
             (Tactic.exact
              "exact"
              (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.decide "decide") [])]))))
             [])
            (group
             (Tactic.simpa
              "simpa"
              []
              []
              ["["
               [(Tactic.simpLemma [] [] `Finset.sum_eq_multiset_sum)
                ","
                (Tactic.simpLemma [] [] `fin4univ)
                ","
                (Tactic.simpLemma [] [] `Multiset.sum_cons)
                ","
                (Tactic.simpLemma [] [] `f)
                ","
                (Tactic.simpLemma [] [] `add_assocₓ)]
               "]"]
              []
              [])
             [])])))]
       "⟩")))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.have', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.have', expected 'Lean.Parser.Term.have.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.have
   "have"
   (Term.haveDecl
    (Term.haveIdDecl
     [`h23 []]
     [(Term.typeSpec
       ":"
       (Init.Core.«term_∣_»
        (numLit "2")
        " ∣ "
        (Init.Logic.«term_+_»
         (Cardinal.SetTheory.Cofinality.«term_^_» (Term.app `f [(Term.app `σ [(numLit "2")])]) "^" (numLit "2"))
         "+"
         (Cardinal.SetTheory.Cofinality.«term_^_» (Term.app `f [(Term.app `σ [(numLit "3")])]) "^" (numLit "2")))))]
     ":="
     («term_$__»
      (Term.proj
       (Term.app `CharP.int_cast_eq_zero_iff [(Term.app `Zmod [(numLit "2")]) (numLit "2") (Term.hole "_")])
       "."
       (fieldIdx "1"))
      "$"
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(group (Tactic.simpa "simpa" [] [] [] [] ["using" (Term.proj `hσ "." (fieldIdx "2"))]) [])]))))))
   []
   (Term.let
    "let"
    (Term.letDecl (Term.letPatDecl (Term.anonymousCtor "⟨" [`x "," `hx] "⟩") [] [] ":=" `h01))
    []
    (Term.let
     "let"
     (Term.letDecl (Term.letPatDecl (Term.anonymousCtor "⟨" [`y "," `hy] "⟩") [] [] ":=" `h23))
     []
     (Term.anonymousCtor
      "⟨"
      [(«term_/_»
        («term_-_» (Term.app `f [(Term.app `σ [(numLit "0")])]) "-" (Term.app `f [(Term.app `σ [(numLit "1")])]))
        "/"
        (numLit "2"))
       ","
       («term_/_»
        (Init.Logic.«term_+_»
         (Term.app `f [(Term.app `σ [(numLit "0")])])
         "+"
         (Term.app `f [(Term.app `σ [(numLit "1")])]))
        "/"
        (numLit "2"))
       ","
       («term_/_»
        («term_-_» (Term.app `f [(Term.app `σ [(numLit "2")])]) "-" (Term.app `f [(Term.app `σ [(numLit "3")])]))
        "/"
        (numLit "2"))
       ","
       («term_/_»
        (Init.Logic.«term_+_»
         (Term.app `f [(Term.app `σ [(numLit "2")])])
         "+"
         (Term.app `f [(Term.app `σ [(numLit "3")])]))
        "/"
        (numLit "2"))
       ","
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
              [(Tactic.rwRule ["←"] (Term.app `Int.sq_add_sq_of_two_mul_sq_add_sq [`hx.symm]))
               ","
               (Tactic.rwRule [] `add_assocₓ)
               ","
               (Tactic.rwRule ["←"] (Term.app `Int.sq_add_sq_of_two_mul_sq_add_sq [`hy.symm]))
               ","
               (Tactic.rwRule
                ["←"]
                (Term.app
                 `mul_right_inj'
                 [(Term.show
                   "show"
                   («term_≠_»
                    (Term.paren "(" [(numLit "2") [(Term.typeAscription ":" (termℤ "ℤ"))]] ")")
                    "≠"
                    (numLit "0"))
                   (Term.fromTerm
                    "from"
                    (Term.byTactic
                     "by"
                     (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.decide "decide") [])])))))]))
               ","
               (Tactic.rwRule ["←"] `h)
               ","
               (Tactic.rwRule [] `mul_addₓ)
               ","
               (Tactic.rwRule ["←"] `hx)
               ","
               (Tactic.rwRule ["←"] `hy)]
              "]")
             [])
            [])
           (group
            (Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               []
               [(Term.typeSpec
                 ":"
                 («term_=_»
                  (Algebra.BigOperators.Basic.«term∑_,_»
                   "∑"
                   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
                   ", "
                   (Cardinal.SetTheory.Cofinality.«term_^_» (Term.app `f [(Term.app `σ [`x])]) "^" (numLit "2")))
                  "="
                  (Algebra.BigOperators.Basic.«term∑_,_»
                   "∑"
                   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
                   ", "
                   (Cardinal.SetTheory.Cofinality.«term_^_» (Term.app `f [`x]) "^" (numLit "2")))))]
               ":="
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(group
                    (Mathlib.Tactic.Conv.convRHS
                     "conv_rhs"
                     []
                     []
                     "=>"
                     (Tactic.Conv.convSeq
                      (Tactic.Conv.convSeq1Indented
                       [(group
                         (Tactic.Conv.convRw__ "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `σ.sum_comp)] "]"))
                         [])])))
                    [])]))))))
            [])
           (group
            (Tactic.have''
             "have"
             [`fin4univ []]
             [(Term.typeSpec
               ":"
               («term_=_»
                (Term.proj
                 (Term.paren
                  "("
                  [`univ [(Term.typeAscription ":" (Term.app `Finset [(Term.app `Finₓ [(numLit "4")])]))]]
                  ")")
                 "."
                 (fieldIdx "1"))
                "="
                (Multiset.Data.Multiset.Basic.«term_::ₘ_»
                 (numLit "0")
                 " ::ₘ "
                 (Multiset.Data.Multiset.Basic.«term_::ₘ_»
                  (numLit "1")
                  " ::ₘ "
                  (Multiset.Data.Multiset.Basic.«term_::ₘ_»
                   (numLit "2")
                   " ::ₘ "
                   (Multiset.Data.Multiset.Basic.«term_::ₘ_» (numLit "3") " ::ₘ " (numLit "0")))))))])
            [])
           (group
            (Tactic.exact
             "exact"
             (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.decide "decide") [])]))))
            [])
           (group
            (Tactic.simpa
             "simpa"
             []
             []
             ["["
              [(Tactic.simpLemma [] [] `Finset.sum_eq_multiset_sum)
               ","
               (Tactic.simpLemma [] [] `fin4univ)
               ","
               (Tactic.simpLemma [] [] `Multiset.sum_cons)
               ","
               (Tactic.simpLemma [] [] `f)
               ","
               (Tactic.simpLemma [] [] `add_assocₓ)]
              "]"]
             []
             [])
            [])])))]
      "⟩"))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.have', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.have', expected 'Lean.Parser.Term.have.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.let
   "let"
   (Term.letDecl (Term.letPatDecl (Term.anonymousCtor "⟨" [`x "," `hx] "⟩") [] [] ":=" `h01))
   []
   (Term.let
    "let"
    (Term.letDecl (Term.letPatDecl (Term.anonymousCtor "⟨" [`y "," `hy] "⟩") [] [] ":=" `h23))
    []
    (Term.anonymousCtor
     "⟨"
     [(«term_/_»
       («term_-_» (Term.app `f [(Term.app `σ [(numLit "0")])]) "-" (Term.app `f [(Term.app `σ [(numLit "1")])]))
       "/"
       (numLit "2"))
      ","
      («term_/_»
       (Init.Logic.«term_+_»
        (Term.app `f [(Term.app `σ [(numLit "0")])])
        "+"
        (Term.app `f [(Term.app `σ [(numLit "1")])]))
       "/"
       (numLit "2"))
      ","
      («term_/_»
       («term_-_» (Term.app `f [(Term.app `σ [(numLit "2")])]) "-" (Term.app `f [(Term.app `σ [(numLit "3")])]))
       "/"
       (numLit "2"))
      ","
      («term_/_»
       (Init.Logic.«term_+_»
        (Term.app `f [(Term.app `σ [(numLit "2")])])
        "+"
        (Term.app `f [(Term.app `σ [(numLit "3")])]))
       "/"
       (numLit "2"))
      ","
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
             [(Tactic.rwRule ["←"] (Term.app `Int.sq_add_sq_of_two_mul_sq_add_sq [`hx.symm]))
              ","
              (Tactic.rwRule [] `add_assocₓ)
              ","
              (Tactic.rwRule ["←"] (Term.app `Int.sq_add_sq_of_two_mul_sq_add_sq [`hy.symm]))
              ","
              (Tactic.rwRule
               ["←"]
               (Term.app
                `mul_right_inj'
                [(Term.show
                  "show"
                  («term_≠_»
                   (Term.paren "(" [(numLit "2") [(Term.typeAscription ":" (termℤ "ℤ"))]] ")")
                   "≠"
                   (numLit "0"))
                  (Term.fromTerm
                   "from"
                   (Term.byTactic
                    "by"
                    (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.decide "decide") [])])))))]))
              ","
              (Tactic.rwRule ["←"] `h)
              ","
              (Tactic.rwRule [] `mul_addₓ)
              ","
              (Tactic.rwRule ["←"] `hx)
              ","
              (Tactic.rwRule ["←"] `hy)]
             "]")
            [])
           [])
          (group
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              []
              [(Term.typeSpec
                ":"
                («term_=_»
                 (Algebra.BigOperators.Basic.«term∑_,_»
                  "∑"
                  (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
                  ", "
                  (Cardinal.SetTheory.Cofinality.«term_^_» (Term.app `f [(Term.app `σ [`x])]) "^" (numLit "2")))
                 "="
                 (Algebra.BigOperators.Basic.«term∑_,_»
                  "∑"
                  (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
                  ", "
                  (Cardinal.SetTheory.Cofinality.«term_^_» (Term.app `f [`x]) "^" (numLit "2")))))]
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(group
                   (Mathlib.Tactic.Conv.convRHS
                    "conv_rhs"
                    []
                    []
                    "=>"
                    (Tactic.Conv.convSeq
                     (Tactic.Conv.convSeq1Indented
                      [(group
                        (Tactic.Conv.convRw__ "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `σ.sum_comp)] "]"))
                        [])])))
                   [])]))))))
           [])
          (group
           (Tactic.have''
            "have"
            [`fin4univ []]
            [(Term.typeSpec
              ":"
              («term_=_»
               (Term.proj
                (Term.paren
                 "("
                 [`univ [(Term.typeAscription ":" (Term.app `Finset [(Term.app `Finₓ [(numLit "4")])]))]]
                 ")")
                "."
                (fieldIdx "1"))
               "="
               (Multiset.Data.Multiset.Basic.«term_::ₘ_»
                (numLit "0")
                " ::ₘ "
                (Multiset.Data.Multiset.Basic.«term_::ₘ_»
                 (numLit "1")
                 " ::ₘ "
                 (Multiset.Data.Multiset.Basic.«term_::ₘ_»
                  (numLit "2")
                  " ::ₘ "
                  (Multiset.Data.Multiset.Basic.«term_::ₘ_» (numLit "3") " ::ₘ " (numLit "0")))))))])
           [])
          (group
           (Tactic.exact
            "exact"
            (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.decide "decide") [])]))))
           [])
          (group
           (Tactic.simpa
            "simpa"
            []
            []
            ["["
             [(Tactic.simpLemma [] [] `Finset.sum_eq_multiset_sum)
              ","
              (Tactic.simpLemma [] [] `fin4univ)
              ","
              (Tactic.simpLemma [] [] `Multiset.sum_cons)
              ","
              (Tactic.simpLemma [] [] `f)
              ","
              (Tactic.simpLemma [] [] `add_assocₓ)]
             "]"]
            []
            [])
           [])])))]
     "⟩")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.let', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.let', expected 'Lean.Parser.Term.let.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.let
   "let"
   (Term.letDecl (Term.letPatDecl (Term.anonymousCtor "⟨" [`y "," `hy] "⟩") [] [] ":=" `h23))
   []
   (Term.anonymousCtor
    "⟨"
    [(«term_/_»
      («term_-_» (Term.app `f [(Term.app `σ [(numLit "0")])]) "-" (Term.app `f [(Term.app `σ [(numLit "1")])]))
      "/"
      (numLit "2"))
     ","
     («term_/_»
      (Init.Logic.«term_+_»
       (Term.app `f [(Term.app `σ [(numLit "0")])])
       "+"
       (Term.app `f [(Term.app `σ [(numLit "1")])]))
      "/"
      (numLit "2"))
     ","
     («term_/_»
      («term_-_» (Term.app `f [(Term.app `σ [(numLit "2")])]) "-" (Term.app `f [(Term.app `σ [(numLit "3")])]))
      "/"
      (numLit "2"))
     ","
     («term_/_»
      (Init.Logic.«term_+_»
       (Term.app `f [(Term.app `σ [(numLit "2")])])
       "+"
       (Term.app `f [(Term.app `σ [(numLit "3")])]))
      "/"
      (numLit "2"))
     ","
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
            [(Tactic.rwRule ["←"] (Term.app `Int.sq_add_sq_of_two_mul_sq_add_sq [`hx.symm]))
             ","
             (Tactic.rwRule [] `add_assocₓ)
             ","
             (Tactic.rwRule ["←"] (Term.app `Int.sq_add_sq_of_two_mul_sq_add_sq [`hy.symm]))
             ","
             (Tactic.rwRule
              ["←"]
              (Term.app
               `mul_right_inj'
               [(Term.show
                 "show"
                 («term_≠_»
                  (Term.paren "(" [(numLit "2") [(Term.typeAscription ":" (termℤ "ℤ"))]] ")")
                  "≠"
                  (numLit "0"))
                 (Term.fromTerm
                  "from"
                  (Term.byTactic
                   "by"
                   (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.decide "decide") [])])))))]))
             ","
             (Tactic.rwRule ["←"] `h)
             ","
             (Tactic.rwRule [] `mul_addₓ)
             ","
             (Tactic.rwRule ["←"] `hx)
             ","
             (Tactic.rwRule ["←"] `hy)]
            "]")
           [])
          [])
         (group
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             []
             [(Term.typeSpec
               ":"
               («term_=_»
                (Algebra.BigOperators.Basic.«term∑_,_»
                 "∑"
                 (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
                 ", "
                 (Cardinal.SetTheory.Cofinality.«term_^_» (Term.app `f [(Term.app `σ [`x])]) "^" (numLit "2")))
                "="
                (Algebra.BigOperators.Basic.«term∑_,_»
                 "∑"
                 (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
                 ", "
                 (Cardinal.SetTheory.Cofinality.«term_^_» (Term.app `f [`x]) "^" (numLit "2")))))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(group
                  (Mathlib.Tactic.Conv.convRHS
                   "conv_rhs"
                   []
                   []
                   "=>"
                   (Tactic.Conv.convSeq
                    (Tactic.Conv.convSeq1Indented
                     [(group
                       (Tactic.Conv.convRw__ "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `σ.sum_comp)] "]"))
                       [])])))
                  [])]))))))
          [])
         (group
          (Tactic.have''
           "have"
           [`fin4univ []]
           [(Term.typeSpec
             ":"
             («term_=_»
              (Term.proj
               (Term.paren
                "("
                [`univ [(Term.typeAscription ":" (Term.app `Finset [(Term.app `Finₓ [(numLit "4")])]))]]
                ")")
               "."
               (fieldIdx "1"))
              "="
              (Multiset.Data.Multiset.Basic.«term_::ₘ_»
               (numLit "0")
               " ::ₘ "
               (Multiset.Data.Multiset.Basic.«term_::ₘ_»
                (numLit "1")
                " ::ₘ "
                (Multiset.Data.Multiset.Basic.«term_::ₘ_»
                 (numLit "2")
                 " ::ₘ "
                 (Multiset.Data.Multiset.Basic.«term_::ₘ_» (numLit "3") " ::ₘ " (numLit "0")))))))])
          [])
         (group
          (Tactic.exact
           "exact"
           (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.decide "decide") [])]))))
          [])
         (group
          (Tactic.simpa
           "simpa"
           []
           []
           ["["
            [(Tactic.simpLemma [] [] `Finset.sum_eq_multiset_sum)
             ","
             (Tactic.simpLemma [] [] `fin4univ)
             ","
             (Tactic.simpLemma [] [] `Multiset.sum_cons)
             ","
             (Tactic.simpLemma [] [] `f)
             ","
             (Tactic.simpLemma [] [] `add_assocₓ)]
            "]"]
           []
           [])
          [])])))]
    "⟩"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.let', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.let', expected 'Lean.Parser.Term.let.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor
   "⟨"
   [(«term_/_»
     («term_-_» (Term.app `f [(Term.app `σ [(numLit "0")])]) "-" (Term.app `f [(Term.app `σ [(numLit "1")])]))
     "/"
     (numLit "2"))
    ","
    («term_/_»
     (Init.Logic.«term_+_»
      (Term.app `f [(Term.app `σ [(numLit "0")])])
      "+"
      (Term.app `f [(Term.app `σ [(numLit "1")])]))
     "/"
     (numLit "2"))
    ","
    («term_/_»
     («term_-_» (Term.app `f [(Term.app `σ [(numLit "2")])]) "-" (Term.app `f [(Term.app `σ [(numLit "3")])]))
     "/"
     (numLit "2"))
    ","
    («term_/_»
     (Init.Logic.«term_+_»
      (Term.app `f [(Term.app `σ [(numLit "2")])])
      "+"
      (Term.app `f [(Term.app `σ [(numLit "3")])]))
     "/"
     (numLit "2"))
    ","
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
           [(Tactic.rwRule ["←"] (Term.app `Int.sq_add_sq_of_two_mul_sq_add_sq [`hx.symm]))
            ","
            (Tactic.rwRule [] `add_assocₓ)
            ","
            (Tactic.rwRule ["←"] (Term.app `Int.sq_add_sq_of_two_mul_sq_add_sq [`hy.symm]))
            ","
            (Tactic.rwRule
             ["←"]
             (Term.app
              `mul_right_inj'
              [(Term.show
                "show"
                («term_≠_» (Term.paren "(" [(numLit "2") [(Term.typeAscription ":" (termℤ "ℤ"))]] ")") "≠" (numLit "0"))
                (Term.fromTerm
                 "from"
                 (Term.byTactic
                  "by"
                  (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.decide "decide") [])])))))]))
            ","
            (Tactic.rwRule ["←"] `h)
            ","
            (Tactic.rwRule [] `mul_addₓ)
            ","
            (Tactic.rwRule ["←"] `hx)
            ","
            (Tactic.rwRule ["←"] `hy)]
           "]")
          [])
         [])
        (group
         (Tactic.tacticHave_
          "have"
          (Term.haveDecl
           (Term.haveIdDecl
            []
            [(Term.typeSpec
              ":"
              («term_=_»
               (Algebra.BigOperators.Basic.«term∑_,_»
                "∑"
                (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
                ", "
                (Cardinal.SetTheory.Cofinality.«term_^_» (Term.app `f [(Term.app `σ [`x])]) "^" (numLit "2")))
               "="
               (Algebra.BigOperators.Basic.«term∑_,_»
                "∑"
                (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
                ", "
                (Cardinal.SetTheory.Cofinality.«term_^_» (Term.app `f [`x]) "^" (numLit "2")))))]
            ":="
            (Term.byTactic
             "by"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(group
                 (Mathlib.Tactic.Conv.convRHS
                  "conv_rhs"
                  []
                  []
                  "=>"
                  (Tactic.Conv.convSeq
                   (Tactic.Conv.convSeq1Indented
                    [(group
                      (Tactic.Conv.convRw__ "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `σ.sum_comp)] "]"))
                      [])])))
                 [])]))))))
         [])
        (group
         (Tactic.have''
          "have"
          [`fin4univ []]
          [(Term.typeSpec
            ":"
            («term_=_»
             (Term.proj
              (Term.paren
               "("
               [`univ [(Term.typeAscription ":" (Term.app `Finset [(Term.app `Finₓ [(numLit "4")])]))]]
               ")")
              "."
              (fieldIdx "1"))
             "="
             (Multiset.Data.Multiset.Basic.«term_::ₘ_»
              (numLit "0")
              " ::ₘ "
              (Multiset.Data.Multiset.Basic.«term_::ₘ_»
               (numLit "1")
               " ::ₘ "
               (Multiset.Data.Multiset.Basic.«term_::ₘ_»
                (numLit "2")
                " ::ₘ "
                (Multiset.Data.Multiset.Basic.«term_::ₘ_» (numLit "3") " ::ₘ " (numLit "0")))))))])
         [])
        (group
         (Tactic.exact
          "exact"
          (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.decide "decide") [])]))))
         [])
        (group
         (Tactic.simpa
          "simpa"
          []
          []
          ["["
           [(Tactic.simpLemma [] [] `Finset.sum_eq_multiset_sum)
            ","
            (Tactic.simpLemma [] [] `fin4univ)
            ","
            (Tactic.simpLemma [] [] `Multiset.sum_cons)
            ","
            (Tactic.simpLemma [] [] `f)
            ","
            (Tactic.simpLemma [] [] `add_assocₓ)]
           "]"]
          []
          [])
         [])])))]
   "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'sepBy.antiquot_scope'
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
         [(Tactic.rwRule ["←"] (Term.app `Int.sq_add_sq_of_two_mul_sq_add_sq [`hx.symm]))
          ","
          (Tactic.rwRule [] `add_assocₓ)
          ","
          (Tactic.rwRule ["←"] (Term.app `Int.sq_add_sq_of_two_mul_sq_add_sq [`hy.symm]))
          ","
          (Tactic.rwRule
           ["←"]
           (Term.app
            `mul_right_inj'
            [(Term.show
              "show"
              («term_≠_» (Term.paren "(" [(numLit "2") [(Term.typeAscription ":" (termℤ "ℤ"))]] ")") "≠" (numLit "0"))
              (Term.fromTerm
               "from"
               (Term.byTactic
                "by"
                (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.decide "decide") [])])))))]))
          ","
          (Tactic.rwRule ["←"] `h)
          ","
          (Tactic.rwRule [] `mul_addₓ)
          ","
          (Tactic.rwRule ["←"] `hx)
          ","
          (Tactic.rwRule ["←"] `hy)]
         "]")
        [])
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          []
          [(Term.typeSpec
            ":"
            («term_=_»
             (Algebra.BigOperators.Basic.«term∑_,_»
              "∑"
              (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
              ", "
              (Cardinal.SetTheory.Cofinality.«term_^_» (Term.app `f [(Term.app `σ [`x])]) "^" (numLit "2")))
             "="
             (Algebra.BigOperators.Basic.«term∑_,_»
              "∑"
              (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
              ", "
              (Cardinal.SetTheory.Cofinality.«term_^_» (Term.app `f [`x]) "^" (numLit "2")))))]
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group
               (Mathlib.Tactic.Conv.convRHS
                "conv_rhs"
                []
                []
                "=>"
                (Tactic.Conv.convSeq
                 (Tactic.Conv.convSeq1Indented
                  [(group
                    (Tactic.Conv.convRw__ "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `σ.sum_comp)] "]"))
                    [])])))
               [])]))))))
       [])
      (group
       (Tactic.have''
        "have"
        [`fin4univ []]
        [(Term.typeSpec
          ":"
          («term_=_»
           (Term.proj
            (Term.paren
             "("
             [`univ [(Term.typeAscription ":" (Term.app `Finset [(Term.app `Finₓ [(numLit "4")])]))]]
             ")")
            "."
            (fieldIdx "1"))
           "="
           (Multiset.Data.Multiset.Basic.«term_::ₘ_»
            (numLit "0")
            " ::ₘ "
            (Multiset.Data.Multiset.Basic.«term_::ₘ_»
             (numLit "1")
             " ::ₘ "
             (Multiset.Data.Multiset.Basic.«term_::ₘ_»
              (numLit "2")
              " ::ₘ "
              (Multiset.Data.Multiset.Basic.«term_::ₘ_» (numLit "3") " ::ₘ " (numLit "0")))))))])
       [])
      (group
       (Tactic.exact
        "exact"
        (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.decide "decide") [])]))))
       [])
      (group
       (Tactic.simpa
        "simpa"
        []
        []
        ["["
         [(Tactic.simpLemma [] [] `Finset.sum_eq_multiset_sum)
          ","
          (Tactic.simpLemma [] [] `fin4univ)
          ","
          (Tactic.simpLemma [] [] `Multiset.sum_cons)
          ","
          (Tactic.simpLemma [] [] `f)
          ","
          (Tactic.simpLemma [] [] `add_assocₓ)]
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
    [(Tactic.simpLemma [] [] `Finset.sum_eq_multiset_sum)
     ","
     (Tactic.simpLemma [] [] `fin4univ)
     ","
     (Tactic.simpLemma [] [] `Multiset.sum_cons)
     ","
     (Tactic.simpLemma [] [] `f)
     ","
     (Tactic.simpLemma [] [] `add_assocₓ)]
    "]"]
   []
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpa', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `add_assocₓ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `f
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Multiset.sum_cons
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `fin4univ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Finset.sum_eq_multiset_sum
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.exact
   "exact"
   (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.decide "decide") [])]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.exact', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.decide "decide") [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.decide "decide")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.decide', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.decide', expected 'Lean.Parser.Tactic.decide.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.have''
   "have"
   [`fin4univ []]
   [(Term.typeSpec
     ":"
     («term_=_»
      (Term.proj
       (Term.paren "(" [`univ [(Term.typeAscription ":" (Term.app `Finset [(Term.app `Finₓ [(numLit "4")])]))]] ")")
       "."
       (fieldIdx "1"))
      "="
      (Multiset.Data.Multiset.Basic.«term_::ₘ_»
       (numLit "0")
       " ::ₘ "
       (Multiset.Data.Multiset.Basic.«term_::ₘ_»
        (numLit "1")
        " ::ₘ "
        (Multiset.Data.Multiset.Basic.«term_::ₘ_»
         (numLit "2")
         " ::ₘ "
         (Multiset.Data.Multiset.Basic.«term_::ₘ_» (numLit "3") " ::ₘ " (numLit "0")))))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.have''', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_=_»
   (Term.proj
    (Term.paren "(" [`univ [(Term.typeAscription ":" (Term.app `Finset [(Term.app `Finₓ [(numLit "4")])]))]] ")")
    "."
    (fieldIdx "1"))
   "="
   (Multiset.Data.Multiset.Basic.«term_::ₘ_»
    (numLit "0")
    " ::ₘ "
    (Multiset.Data.Multiset.Basic.«term_::ₘ_»
     (numLit "1")
     " ::ₘ "
     (Multiset.Data.Multiset.Basic.«term_::ₘ_»
      (numLit "2")
      " ::ₘ "
      (Multiset.Data.Multiset.Basic.«term_::ₘ_» (numLit "3") " ::ₘ " (numLit "0"))))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Multiset.Data.Multiset.Basic.«term_::ₘ_»
   (numLit "0")
   " ::ₘ "
   (Multiset.Data.Multiset.Basic.«term_::ₘ_»
    (numLit "1")
    " ::ₘ "
    (Multiset.Data.Multiset.Basic.«term_::ₘ_»
     (numLit "2")
     " ::ₘ "
     (Multiset.Data.Multiset.Basic.«term_::ₘ_» (numLit "3") " ::ₘ " (numLit "0")))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Multiset.Data.Multiset.Basic.«term_::ₘ_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Multiset.Data.Multiset.Basic.«term_::ₘ_»
   (numLit "1")
   " ::ₘ "
   (Multiset.Data.Multiset.Basic.«term_::ₘ_»
    (numLit "2")
    " ::ₘ "
    (Multiset.Data.Multiset.Basic.«term_::ₘ_» (numLit "3") " ::ₘ " (numLit "0"))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Multiset.Data.Multiset.Basic.«term_::ₘ_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Multiset.Data.Multiset.Basic.«term_::ₘ_»
   (numLit "2")
   " ::ₘ "
   (Multiset.Data.Multiset.Basic.«term_::ₘ_» (numLit "3") " ::ₘ " (numLit "0")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Multiset.Data.Multiset.Basic.«term_::ₘ_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Multiset.Data.Multiset.Basic.«term_::ₘ_» (numLit "3") " ::ₘ " (numLit "0"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Multiset.Data.Multiset.Basic.«term_::ₘ_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "0")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 67 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 67, term))
  (numLit "3")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 68 >? 1024, (none, [anonymous]) <=? (some 67, term)
[PrettyPrinter.parenthesize] ...precedences are 67 >? 67, (some 67, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 67, term))
  (numLit "2")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 68 >? 1024, (none, [anonymous]) <=? (some 67, term)
[PrettyPrinter.parenthesize] ...precedences are 67 >? 67, (some 67, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 67, term))
  (numLit "1")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 68 >? 1024, (none, [anonymous]) <=? (some 67, term)
[PrettyPrinter.parenthesize] ...precedences are 67 >? 67, (some 67, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 67, term))
  (numLit "0")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 68 >? 1024, (none, [anonymous]) <=? (some 67, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 67, (some 67, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Term.proj
   (Term.paren "(" [`univ [(Term.typeAscription ":" (Term.app `Finset [(Term.app `Finₓ [(numLit "4")])]))]] ")")
   "."
   (fieldIdx "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.paren "(" [`univ [(Term.typeAscription ":" (Term.app `Finset [(Term.app `Finₓ [(numLit "4")])]))]] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.paren.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.typeAscription.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Finset [(Term.app `Finₓ [(numLit "4")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Finₓ [(numLit "4")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "4")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Finₓ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `Finₓ [(numLit "4")]) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Finset
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  `univ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.tacticHave_
   "have"
   (Term.haveDecl
    (Term.haveIdDecl
     []
     [(Term.typeSpec
       ":"
       («term_=_»
        (Algebra.BigOperators.Basic.«term∑_,_»
         "∑"
         (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
         ", "
         (Cardinal.SetTheory.Cofinality.«term_^_» (Term.app `f [(Term.app `σ [`x])]) "^" (numLit "2")))
        "="
        (Algebra.BigOperators.Basic.«term∑_,_»
         "∑"
         (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
         ", "
         (Cardinal.SetTheory.Cofinality.«term_^_» (Term.app `f [`x]) "^" (numLit "2")))))]
     ":="
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(group
          (Mathlib.Tactic.Conv.convRHS
           "conv_rhs"
           []
           []
           "=>"
           (Tactic.Conv.convSeq
            (Tactic.Conv.convSeq1Indented
             [(group
               (Tactic.Conv.convRw__ "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `σ.sum_comp)] "]"))
               [])])))
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
       (Mathlib.Tactic.Conv.convRHS
        "conv_rhs"
        []
        []
        "=>"
        (Tactic.Conv.convSeq
         (Tactic.Conv.convSeq1Indented
          [(group (Tactic.Conv.convRw__ "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `σ.sum_comp)] "]")) [])])))
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Mathlib.Tactic.Conv.convRHS
   "conv_rhs"
   []
   []
   "=>"
   (Tactic.Conv.convSeq
    (Tactic.Conv.convSeq1Indented
     [(group (Tactic.Conv.convRw__ "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `σ.sum_comp)] "]")) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Mathlib.Tactic.Conv.convRHS', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.Conv.convRw__', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `σ.sum_comp
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«←»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_=_»
   (Algebra.BigOperators.Basic.«term∑_,_»
    "∑"
    (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
    ", "
    (Cardinal.SetTheory.Cofinality.«term_^_» (Term.app `f [(Term.app `σ [`x])]) "^" (numLit "2")))
   "="
   (Algebra.BigOperators.Basic.«term∑_,_»
    "∑"
    (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
    ", "
    (Cardinal.SetTheory.Cofinality.«term_^_» (Term.app `f [`x]) "^" (numLit "2"))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Algebra.BigOperators.Basic.«term∑_,_»
   "∑"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
   ", "
   (Cardinal.SetTheory.Cofinality.«term_^_» (Term.app `f [`x]) "^" (numLit "2")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.BigOperators.Basic.«term∑_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Cardinal.SetTheory.Cofinality.«term_^_» (Term.app `f [`x]) "^" (numLit "2"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Cardinal.SetTheory.Cofinality.«term_^_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "2")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 0, term))
  (Term.app `f [`x])
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
  `f
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1 >? 1022, (some 1023, term) <=? (some 0, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 0, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.explicitBinders', expected 'Mathlib.ExtendedBinder.extBinders'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.letPatDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.letPatDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveEqnsDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveEqnsDecl'
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
private
  theorem
    sum_four_squares_of_two_mul_sum_four_squares
    { m a b c d : ℤ } ( h : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = 2 * m ) : ∃ w x y z : ℤ , w ^ 2 + x ^ 2 + y ^ 2 + z ^ 2 = m
    :=
      have
        :
            ∀
              f : Finₓ 4 → Zmod 2
              ,
              f 0 ^ 2 + f 1 ^ 2 + f 2 ^ 2 + f 3 ^ 2 = 0
                →
                ∃ i : Finₓ 4 , f i ^ 2 + f swap i 0 1 ^ 2 = 0 ∧ f swap i 0 2 ^ 2 + f swap i 0 3 ^ 2 = 0
          :=
          by decide
        let
          f : Finₓ 4 → ℤ := Vector.nth a ::ᵥ b ::ᵥ c ::ᵥ d ::ᵥ Vector.nil
          let
            ⟨ i , hσ ⟩
              :=
              this
                coeₓ ∘ f
                  by
                    rw [ ← @ zero_mul Zmod 2 _ m , ← show ( ( 2 : ℤ ) : Zmod 2 ) = 0 from rfl , ← Int.cast_mul , ← h ]
                      <;>
                      simp only [ Int.cast_add , Int.cast_pow ] <;> rfl
            let
              σ := swap i 0
              have
                h01
                  : 2 ∣ f σ 0 ^ 2 + f σ 1 ^ 2
                  :=
                  CharP.int_cast_eq_zero_iff Zmod 2 2 _ . 1 $ by simpa [ σ ] using hσ . 1
                have
                  h23 : 2 ∣ f σ 2 ^ 2 + f σ 3 ^ 2 := CharP.int_cast_eq_zero_iff Zmod 2 2 _ . 1 $ by simpa using hσ . 2
                  let
                    ⟨ x , hx ⟩ := h01
                    let
                      ⟨ y , hy ⟩ := h23
                      ⟨
                        f σ 0 - f σ 1 / 2
                          ,
                          f σ 0 + f σ 1 / 2
                          ,
                          f σ 2 - f σ 3 / 2
                          ,
                          f σ 2 + f σ 3 / 2
                          ,
                          by
                            rw
                                [
                                  ← Int.sq_add_sq_of_two_mul_sq_add_sq hx.symm
                                    ,
                                    add_assocₓ
                                    ,
                                    ← Int.sq_add_sq_of_two_mul_sq_add_sq hy.symm
                                    ,
                                    ← mul_right_inj' show ( 2 : ℤ ) ≠ 0 from by decide
                                    ,
                                    ← h
                                    ,
                                    mul_addₓ
                                    ,
                                    ← hx
                                    ,
                                    ← hy
                                  ]
                              have : ∑ x , f σ x ^ 2 = ∑ x , f x ^ 2 := by conv_rhs => rw [ ← σ.sum_comp ]
                              have fin4univ : ( univ : Finset Finₓ 4 ) . 1 = 0 ::ₘ 1 ::ₘ 2 ::ₘ 3 ::ₘ 0
                              exact by decide
                              simpa [ Finset.sum_eq_multiset_sum , fin4univ , Multiset.sum_cons , f , add_assocₓ ]
                        ⟩

private theorem prime_sum_four_squares (p : ℕ) [hp : _root_.fact p.prime] :
    ∃ a b c d : ℤ, ((((a^2)+b^2)+c^2)+d^2) = p :=
  have hm : ∃ m < p, 0 < m ∧ ∃ a b c d : ℤ, ((((a^2)+b^2)+c^2)+d^2) = m*p :=
    let ⟨a, b, k, hk⟩ := exists_sq_add_sq_add_one_eq_k p
    ⟨k, hk.2,
      Nat.pos_of_ne_zeroₓ $ fun hk0 => by
        rw [hk0, Int.coe_nat_zero, zero_mul] at hk
        exact
          ne_of_gtₓ
            (show (((a^2)+b^2)+1) > 0 from
              add_pos_of_nonneg_of_pos (add_nonneg (sq_nonneg _) (sq_nonneg _)) zero_lt_one)
            hk.1,
      a, b, 1, 0, by
      simpa [sq] using hk.1⟩
  let m := Nat.findₓ hm
  let ⟨a, b, c, d, (habcd : ((((a^2)+b^2)+c^2)+d^2) = m*p)⟩ := (Nat.find_specₓ hm).snd.2
  by
  have hm0 : _root_.fact (0 < m) := ⟨(Nat.find_specₓ hm).snd.1⟩ <;>
    exact
      have hmp : m < p := (Nat.find_specₓ hm).fst
      m.mod_two_eq_zero_or_one.elim
        (fun hm2 : m % 2 = 0 =>
          let ⟨k, hk⟩ := (Nat.dvd_iff_mod_eq_zeroₓ _ _).2 hm2
          have hk0 : 0 < k :=
            Nat.pos_of_ne_zeroₓ $ fun _ => by
              simp_all [lt_irreflₓ]
          have hkm : k < m := by
            rw [hk, two_mul]
            exact (lt_add_iff_pos_left _).2 hk0
          False.elim $
            Nat.find_minₓ hm hkm
              ⟨lt_transₓ hkm hmp, hk0,
                sum_four_squares_of_two_mul_sum_four_squares
                  (show ((((a^2)+b^2)+c^2)+d^2) = 2*k*p by
                    rw [habcd, hk, Int.coe_nat_mul, mul_assocₓ]
                    simp )⟩)
        fun hm2 : m % 2 = 1 =>
        if hm1 : m = 1 then
          ⟨a, b, c, d, by
            simp only [hm1, habcd, Int.coe_nat_one, one_mulₓ]⟩
        else
          let w := (a : Zmod m).valMinAbs
          let x := (b : Zmod m).valMinAbs
          let y := (c : Zmod m).valMinAbs
          let z := (d : Zmod m).valMinAbs
          have hnat_abs : ((((w^2)+x^2)+y^2)+z^2) = ((((w.nat_abs^2)+x.nat_abs^2)+y.nat_abs^2)+z.nat_abs^2 : ℕ) := by
            simp [sq]
          have hwxyzlt : ((((w^2)+x^2)+y^2)+z^2) < (m^2) :=
            calc ((((w^2)+x^2)+y^2)+z^2) = ((((w.nat_abs^2)+x.nat_abs^2)+y.nat_abs^2)+z.nat_abs^2 : ℕ) := hnat_abs
              _ ≤ ((((m / 2^2)+m / 2^2)+m / 2^2)+m / 2^2 : ℕ) :=
              Int.coe_nat_le.2 $
                add_le_add
                  (add_le_add
                    (add_le_add (Nat.pow_le_pow_of_le_leftₓ (Zmod.nat_abs_val_min_abs_le _) _)
                      (Nat.pow_le_pow_of_le_leftₓ (Zmod.nat_abs_val_min_abs_le _) _))
                    (Nat.pow_le_pow_of_le_leftₓ (Zmod.nat_abs_val_min_abs_le _) _))
                  (Nat.pow_le_pow_of_le_leftₓ (Zmod.nat_abs_val_min_abs_le _) _)
              _ = 4*(m / 2 : ℕ)^2 := by
              simp [sq, bit0, bit1, mul_addₓ, add_mulₓ, add_assocₓ]
              _ < (4*(m / 2 : ℕ)^2)+((4*m / 2 : ℕ)*(m % 2 : ℕ))+(m % 2 : ℕ)^2 :=
              (lt_add_iff_pos_right _).2
                (by
                  rw [hm2, Int.coe_nat_one, one_pow, mul_oneₓ]
                  exact add_pos_of_nonneg_of_pos (Int.coe_nat_nonneg _) zero_lt_one)
              _ = (m^2) := by
              conv_rhs => rw [← Nat.mod_add_divₓ m 2]
              simp [-Nat.mod_add_divₓ, mul_addₓ, add_mulₓ, bit0, bit1, mul_commₓ, mul_assocₓ, mul_left_commₓ, pow_addₓ,
                add_commₓ, add_left_commₓ]
              
          have hwxyzabcd : (((((w^2)+x^2)+y^2)+z^2 : ℤ) : Zmod m) = (((((a^2)+b^2)+c^2)+d^2 : ℤ) : Zmod m) := by
            simp [w, x, y, z, sq]
          have hwxyz0 : (((((w^2)+x^2)+y^2)+z^2 : ℤ) : Zmod m) = 0 := by
            rw [hwxyzabcd, habcd, Int.cast_mul, cast_coe_nat, Zmod.nat_cast_self, zero_mul]
          let ⟨n, hn⟩ := (CharP.int_cast_eq_zero_iff _ m _).1 hwxyz0
          have hn0 : 0 < n.nat_abs :=
            Int.nat_abs_pos_of_ne_zero fun hn0 =>
              have hwxyz0 : ((((w.nat_abs^2)+x.nat_abs^2)+y.nat_abs^2)+z.nat_abs^2 : ℕ) = 0 := by
                rw [← Int.coe_nat_eq_zero, ← hnat_abs]
                rwa [hn0, mul_zero] at hn
              have habcd0 : (m : ℤ) ∣ a ∧ (m : ℤ) ∣ b ∧ (m : ℤ) ∣ c ∧ (m : ℤ) ∣ d := by
                simpa [add_eq_zero_iff' (sq_nonneg (_ : ℤ)) (sq_nonneg _), pow_two, w, x, y, z,
                  CharP.int_cast_eq_zero_iff _ m _, And.assoc] using hwxyz0
              let ⟨ma, hma⟩ := habcd0.1
              let ⟨mb, hmb⟩ := habcd0.2.1
              let ⟨mc, hmc⟩ := habcd0.2.2.1
              let ⟨md, hmd⟩ := habcd0.2.2.2
              have hmdvdp : m ∣ p :=
                Int.coe_nat_dvd.1
                  ⟨(((ma^2)+mb^2)+mc^2)+md^2,
                    (mul_right_inj' (show (m : ℤ) ≠ 0 from Int.coe_nat_ne_zero_iff_pos.2 hm0.1)).1 $ by
                      rw [← habcd, hma, hmb, hmc, hmd]
                      ring⟩
              (hp.1.2 _ hmdvdp).elim hm1 fun hmeqp => by
                simpa [lt_irreflₓ, hmeqp] using hmp
          have hawbxcydz : ((m : ℕ) : ℤ) ∣ (((a*w)+b*x)+c*y)+d*z :=
            (CharP.int_cast_eq_zero_iff (Zmod m) m _).1 $ by
              rw [← hwxyz0]
              simp
              ring
          have haxbwczdy : ((m : ℕ) : ℤ) ∣ (((a*x) - b*w) - c*z)+d*y :=
            (CharP.int_cast_eq_zero_iff (Zmod m) m _).1 $ by
              simp [sub_eq_add_neg]
              ring
          have haybzcwdx : ((m : ℕ) : ℤ) ∣ (((a*y)+b*z) - c*w) - d*x :=
            (CharP.int_cast_eq_zero_iff (Zmod m) m _).1 $ by
              simp [sub_eq_add_neg]
              ring
          have hazbycxdw : ((m : ℕ) : ℤ) ∣ (((a*z) - b*y)+c*x) - d*w :=
            (CharP.int_cast_eq_zero_iff (Zmod m) m _).1 $ by
              simp [sub_eq_add_neg]
              ring
          let ⟨s, hs⟩ := hawbxcydz
          let ⟨t, ht⟩ := haxbwczdy
          let ⟨u, hu⟩ := haybzcwdx
          let ⟨v, hv⟩ := hazbycxdw
          have hn_nonneg : 0 ≤ n :=
            nonneg_of_mul_nonneg_left
              (by
                erw [← hn]
                repeat'
                  try
                    refine' add_nonneg _ _
                  try
                    exact sq_nonneg _)
              (Int.coe_nat_pos.2 hm0.1)
          have hnm : n.nat_abs < m :=
            Int.coe_nat_lt.1
              (lt_of_mul_lt_mul_left
                (by
                  rw [Int.nat_abs_of_nonneg hn_nonneg, ← hn, ← sq]
                  exact hwxyzlt)
                (Int.coe_nat_nonneg m))
          have hstuv : ((((s^2)+t^2)+u^2)+v^2) = n.nat_abs*p :=
            (mul_right_inj' (show (m^2 : ℤ) ≠ 0 from pow_ne_zero 2 (Int.coe_nat_ne_zero_iff_pos.2 hm0.1))).1 $
              calc
                (((m : ℤ)^2)*(((s^2)+t^2)+u^2)+v^2) = (((((m : ℕ)*s)^2)+((m : ℕ)*t)^2)+((m : ℕ)*u)^2)+((m : ℕ)*v)^2 :=
                by
                simp [mul_powₓ]
                ring
                _ = ((((w^2)+x^2)+y^2)+z^2)*(((a^2)+b^2)+c^2)+d^2 := by
                simp only [hs.symm, ht.symm, hu.symm, hv.symm]
                ring
                _ = _ := by
                rw [hn, habcd, Int.nat_abs_of_nonneg hn_nonneg]
                dsimp [m]
                ring
                
          False.elim $ Nat.find_minₓ hm hnm ⟨lt_transₓ hnm hmp, hn0, s, t, u, v, hstuv⟩

/--  **Four squares theorem** -/
theorem sum_four_squares : ∀ n : ℕ, ∃ a b c d : ℕ, ((((a^2)+b^2)+c^2)+d^2) = n
  | 0 => ⟨0, 0, 0, 0, rfl⟩
  | 1 => ⟨1, 0, 0, 0, rfl⟩
  | n@(k+2) =>
    have hm : _root_.fact (min_fac (k+2)).Prime :=
      ⟨min_fac_prime
          (by
            decide)⟩
    have : n / min_fac n < n := factors_lemma
    let ⟨a, b, c, d, h₁⟩ :=
      show ∃ a b c d : ℤ, ((((a^2)+b^2)+c^2)+d^2) = min_fac n by
        exact prime_sum_four_squares (min_fac (k+2))
    let ⟨w, x, y, z, h₂⟩ := sum_four_squares (n / min_fac n)
    ⟨((((a*w) - b*x) - c*y) - d*z).natAbs, ((((a*x)+b*w)+c*z) - d*y).natAbs, ((((a*y) - b*z)+c*w)+d*x).natAbs,
      ((((a*z)+b*y) - c*x)+d*w).natAbs, by
      rw [← Int.coe_nat_inj', ← Nat.mul_div_cancel'ₓ (min_fac_dvd (k+2)), Int.coe_nat_mul, ← h₁, ← h₂]
      simp [sum_four_sq_mul_sum_four_sq]⟩

end Nat

