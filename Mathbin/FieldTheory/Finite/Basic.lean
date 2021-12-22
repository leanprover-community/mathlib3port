import Mathbin.Tactic.ApplyFun
import Mathbin.Data.Equiv.Ring
import Mathbin.Data.Zmod.Algebra
import Mathbin.LinearAlgebra.FiniteDimensional
import Mathbin.RingTheory.IntegralDomain
import Mathbin.FieldTheory.Separable
import Mathbin.FieldTheory.SplittingField

/-!
# Finite fields

This file contains basic results about finite fields.
Throughout most of this file, `K` denotes a finite field
and `q` is notation for the cardinality of `K`.

See `ring_theory.integral_domain` for the fact that the unit group of a finite field is a
cyclic group, as well as the fact that every finite integral domain is a field
(`field_of_is_domain`).

## Main results

1. `fintype.card_units`: The unit group of a finite field is has cardinality `q - 1`.
2. `sum_pow_units`: The sum of `x^i`, where `x` ranges over the units of `K`, is
   - `q-1` if `q-1 ∣ i`
   - `0`   otherwise
3. `finite_field.card`: The cardinality `q` is a power of the characteristic of `K`.
   See `card'` for a variant.

## Notation

Throughout most of this file, `K` denotes a finite field
and `q` is notation for the cardinality of `K`.

## Implementation notes

While `fintype (units K)` can be inferred from `fintype K` in the presence of `decidable_eq K`,
in this file we take the `fintype (units K)` argument directly to reduce the chance of typeclass
diamonds, as `fintype` carries data.

-/


variable {K : Type _} {R : Type _}

local notation "q" => Fintype.card K

open_locale BigOperators

namespace FiniteField

open Finset Function

section Polynomial

variable [CommRingₓ R] [IsDomain R]

open Polynomial

/--  The cardinality of a field is at most `n` times the cardinality of the image of a degree `n`
  polynomial -/
theorem card_image_polynomial_eval [DecidableEq R] [Fintype R] {p : Polynomial R} (hp : 0 < p.degree) :
    Fintype.card R ≤ nat_degree p*(univ.Image fun x => eval x p).card :=
  Finset.card_le_mul_card_image _ _ fun a _ =>
    calc _ = (p - C a).roots.toFinset.card :=
      congr_argₓ card
        (by
          simp [Finset.ext_iff, mem_roots_sub_C hp])
      _ ≤ (p - C a).roots.card := Multiset.to_finset_card_le _
      _ ≤ _ := card_roots_sub_C' hp
      

/--  If `f` and `g` are quadratic polynomials, then the `f.eval a + g.eval b = 0` has a solution. -/
theorem exists_root_sum_quadratic [Fintype R] {f g : Polynomial R} (hf2 : degree f = 2) (hg2 : degree g = 2)
    (hR : Fintype.card R % 2 = 1) : ∃ a b, (f.eval a+g.eval b) = 0 := by
  let this' := Classical.decEq R <;>
    exact
      suffices ¬Disjoint (univ.image fun x : R => eval x f) (univ.image fun x : R => eval x (-g))by
        simp only [disjoint_left, mem_image] at this
        push_neg  at this
        rcases this with ⟨x, ⟨a, _, ha⟩, ⟨b, _, hb⟩⟩
        exact
          ⟨a, b, by
            rw [ha, ← hb, eval_neg, neg_add_selfₓ]⟩
      fun hd : Disjoint _ _ =>
      lt_irreflₓ (2*((univ.image fun x : R => eval x f) ∪ univ.image fun x : R => eval x (-g)).card) $
        calc (2*((univ.image fun x : R => eval x f) ∪ univ.image fun x : R => eval x (-g)).card) ≤ 2*Fintype.card R :=
          Nat.mul_le_mul_leftₓ _ (Finset.card_le_univ _)
          _ = Fintype.card R+Fintype.card R := two_mul _
          _ <
            (nat_degree
                  f*(univ.image fun x : R =>
                    eval x f).card)+nat_degree (-g)*(univ.image fun x : R => eval x (-g)).card :=
          add_lt_add_of_lt_of_le
            (lt_of_le_of_neₓ
              (card_image_polynomial_eval
                (by
                  rw [hf2] <;>
                    exact by
                      decide))
              (mt (congr_argₓ (· % 2))
                (by
                  simp [nat_degree_eq_of_degree_eq_some hf2, hR])))
            (card_image_polynomial_eval
              (by
                rw [degree_neg, hg2] <;>
                  exact by
                    decide))
          _ = 2*((univ.image fun x : R => eval x f) ∪ univ.image fun x : R => eval x (-g)).card := by
          rw [card_disjoint_union hd] <;>
            simp [nat_degree_eq_of_degree_eq_some hf2, nat_degree_eq_of_degree_eq_some hg2, bit0, mul_addₓ]
          

end Polynomial

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [] [] [] [] [] [])
 (Command.theorem
  "theorem"
  (Command.declId `prod_univ_units_id_eq_neg_one [])
  (Command.declSig
   [(Term.instBinder "[" [] (Term.app `CommRingₓ [`K]) "]")
    (Term.instBinder "[" [] (Term.app `IsDomain [`K]) "]")
    (Term.instBinder "[" [] (Term.app `Fintype [(Term.app `Units [`K])]) "]")]
   (Term.typeSpec
    ":"
    («term_=_»
     (Algebra.BigOperators.Basic.«term∏_,_»
      "∏"
      (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] [":" (Term.app `Units [`K])]))
      ", "
      `x)
     "="
     (Term.paren "(" [(«term-_» "-" (numLit "1")) [(Term.typeAscription ":" (Term.app `Units [`K]))]] ")"))))
  (Command.declValSimple
   ":="
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group (Tactic.classical "classical") [])
       (group
        (Tactic.have''
         "have"
         []
         [(Term.typeSpec
           ":"
           («term_=_»
            (Algebra.BigOperators.Basic.«term∏_in_,_»
             "∏"
             (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
             " in "
             (Term.app
              (Term.proj (Term.app (Term.explicit "@" `univ) [(Term.app `Units [`K]) (Term.hole "_")]) "." `erase)
              [(«term-_» "-" (numLit "1"))])
             ", "
             `x)
            "="
            (numLit "1")))])
        [])
       (group
        (Tactic.exact
         "exact"
         (Term.app
          `prod_involution
          [(Term.fun
            "fun"
            (Term.basicFun [(Term.simpleBinder [`x (Term.hole "_")] [])] "=>" (Init.Logic.«term_⁻¹» `x "⁻¹")))
           (Term.byTactic
            "by"
            (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.simp "simp" [] [] [] []) [])])))
           (Term.fun
            "fun"
            (Term.basicFun
             [(Term.simpleBinder [`a] [])]
             "=>"
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(group
                  (Tactic.simp
                   "simp"
                   ["("
                    "config"
                    ":="
                    (Term.structInst
                     "{"
                     []
                     [(group
                       (Term.structInstField (Term.structInstLVal `contextual []) ":=" `Bool.true._@._internal._hyg.0)
                       [])]
                     (Term.optEllipsis [])
                     []
                     "}")
                    ")"]
                   []
                   ["[" [(Tactic.simpLemma [] [] `Units.inv_eq_self_iff)] "]"]
                   [])
                  [])])))))
           (Term.fun
            "fun"
            (Term.basicFun
             [(Term.simpleBinder [`a] [])]
             "=>"
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(group
                  (Tactic.simp
                   "simp"
                   ["("
                    "config"
                    ":="
                    (Term.structInst
                     "{"
                     []
                     [(group
                       (Term.structInstField (Term.structInstLVal `contextual []) ":=" `Bool.true._@._internal._hyg.0)
                       [])]
                     (Term.optEllipsis [])
                     []
                     "}")
                    ")"]
                   []
                   ["["
                    [(Tactic.simpLemma
                      []
                      []
                      (Term.app (Term.explicit "@" `inv_eq_iff_inv_eq) [(Term.hole "_") (Term.hole "_") `a]))
                     ","
                     (Tactic.simpLemma [] [] `eq_comm)]
                    "]"]
                   [])
                  [])])))))
           (Term.byTactic
            "by"
            (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.simp "simp" [] [] [] []) [])])))]))
        [])
       (group
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule
            ["←"]
            (Term.app
             `insert_erase
             [(Term.app
               `mem_univ
               [(Term.paren
                 "("
                 [(«term-_» "-" (numLit "1")) [(Term.typeAscription ":" (Term.app `Units [`K]))]]
                 ")")])]))
           ","
           (Tactic.rwRule [] (Term.app `prod_insert [(Term.app `not_mem_erase [(Term.hole "_") (Term.hole "_")])]))
           ","
           (Tactic.rwRule [] `this)
           ","
           (Tactic.rwRule [] `mul_oneₓ)]
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
     [(group (Tactic.classical "classical") [])
      (group
       (Tactic.have''
        "have"
        []
        [(Term.typeSpec
          ":"
          («term_=_»
           (Algebra.BigOperators.Basic.«term∏_in_,_»
            "∏"
            (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
            " in "
            (Term.app
             (Term.proj (Term.app (Term.explicit "@" `univ) [(Term.app `Units [`K]) (Term.hole "_")]) "." `erase)
             [(«term-_» "-" (numLit "1"))])
            ", "
            `x)
           "="
           (numLit "1")))])
       [])
      (group
       (Tactic.exact
        "exact"
        (Term.app
         `prod_involution
         [(Term.fun
           "fun"
           (Term.basicFun [(Term.simpleBinder [`x (Term.hole "_")] [])] "=>" (Init.Logic.«term_⁻¹» `x "⁻¹")))
          (Term.byTactic
           "by"
           (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.simp "simp" [] [] [] []) [])])))
          (Term.fun
           "fun"
           (Term.basicFun
            [(Term.simpleBinder [`a] [])]
            "=>"
            (Term.byTactic
             "by"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(group
                 (Tactic.simp
                  "simp"
                  ["("
                   "config"
                   ":="
                   (Term.structInst
                    "{"
                    []
                    [(group
                      (Term.structInstField (Term.structInstLVal `contextual []) ":=" `Bool.true._@._internal._hyg.0)
                      [])]
                    (Term.optEllipsis [])
                    []
                    "}")
                   ")"]
                  []
                  ["[" [(Tactic.simpLemma [] [] `Units.inv_eq_self_iff)] "]"]
                  [])
                 [])])))))
          (Term.fun
           "fun"
           (Term.basicFun
            [(Term.simpleBinder [`a] [])]
            "=>"
            (Term.byTactic
             "by"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(group
                 (Tactic.simp
                  "simp"
                  ["("
                   "config"
                   ":="
                   (Term.structInst
                    "{"
                    []
                    [(group
                      (Term.structInstField (Term.structInstLVal `contextual []) ":=" `Bool.true._@._internal._hyg.0)
                      [])]
                    (Term.optEllipsis [])
                    []
                    "}")
                   ")"]
                  []
                  ["["
                   [(Tactic.simpLemma
                     []
                     []
                     (Term.app (Term.explicit "@" `inv_eq_iff_inv_eq) [(Term.hole "_") (Term.hole "_") `a]))
                    ","
                    (Tactic.simpLemma [] [] `eq_comm)]
                   "]"]
                  [])
                 [])])))))
          (Term.byTactic
           "by"
           (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.simp "simp" [] [] [] []) [])])))]))
       [])
      (group
       (Tactic.rwSeq
        "rw"
        []
        (Tactic.rwRuleSeq
         "["
         [(Tactic.rwRule
           ["←"]
           (Term.app
            `insert_erase
            [(Term.app
              `mem_univ
              [(Term.paren
                "("
                [(«term-_» "-" (numLit "1")) [(Term.typeAscription ":" (Term.app `Units [`K]))]]
                ")")])]))
          ","
          (Tactic.rwRule [] (Term.app `prod_insert [(Term.app `not_mem_erase [(Term.hole "_") (Term.hole "_")])]))
          ","
          (Tactic.rwRule [] `this)
          ","
          (Tactic.rwRule [] `mul_oneₓ)]
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
    [(Tactic.rwRule
      ["←"]
      (Term.app
       `insert_erase
       [(Term.app
         `mem_univ
         [(Term.paren "(" [(«term-_» "-" (numLit "1")) [(Term.typeAscription ":" (Term.app `Units [`K]))]] ")")])]))
     ","
     (Tactic.rwRule [] (Term.app `prod_insert [(Term.app `not_mem_erase [(Term.hole "_") (Term.hole "_")])]))
     ","
     (Tactic.rwRule [] `this)
     ","
     (Tactic.rwRule [] `mul_oneₓ)]
    "]")
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwSeq', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `mul_oneₓ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `this
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `prod_insert [(Term.app `not_mem_erase [(Term.hole "_") (Term.hole "_")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `not_mem_erase [(Term.hole "_") (Term.hole "_")])
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `not_mem_erase
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app `not_mem_erase [(Term.hole "_") (Term.hole "_")]) []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `prod_insert
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `insert_erase
   [(Term.app
     `mem_univ
     [(Term.paren "(" [(«term-_» "-" (numLit "1")) [(Term.typeAscription ":" (Term.app `Units [`K]))]] ")")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `mem_univ
   [(Term.paren "(" [(«term-_» "-" (numLit "1")) [(Term.typeAscription ":" (Term.app `Units [`K]))]] ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.paren "(" [(«term-_» "-" (numLit "1")) [(Term.typeAscription ":" (Term.app `Units [`K]))]] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.paren.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.typeAscription.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Units [`K])
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
  `Units
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  («term-_» "-" (numLit "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term-_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "1")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 100 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 100, (some 100, term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `mem_univ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app
   `mem_univ
   [(Term.paren "(" [(«term-_» "-" (numLit "1")) [(Term.typeAscription ":" (Term.app `Units [`K]))]] ")")])
  []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `insert_erase
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«←»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.exact
   "exact"
   (Term.app
    `prod_involution
    [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`x (Term.hole "_")] [])] "=>" (Init.Logic.«term_⁻¹» `x "⁻¹")))
     (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.simp "simp" [] [] [] []) [])])))
     (Term.fun
      "fun"
      (Term.basicFun
       [(Term.simpleBinder [`a] [])]
       "=>"
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group
            (Tactic.simp
             "simp"
             ["("
              "config"
              ":="
              (Term.structInst
               "{"
               []
               [(group
                 (Term.structInstField (Term.structInstLVal `contextual []) ":=" `Bool.true._@._internal._hyg.0)
                 [])]
               (Term.optEllipsis [])
               []
               "}")
              ")"]
             []
             ["[" [(Tactic.simpLemma [] [] `Units.inv_eq_self_iff)] "]"]
             [])
            [])])))))
     (Term.fun
      "fun"
      (Term.basicFun
       [(Term.simpleBinder [`a] [])]
       "=>"
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group
            (Tactic.simp
             "simp"
             ["("
              "config"
              ":="
              (Term.structInst
               "{"
               []
               [(group
                 (Term.structInstField (Term.structInstLVal `contextual []) ":=" `Bool.true._@._internal._hyg.0)
                 [])]
               (Term.optEllipsis [])
               []
               "}")
              ")"]
             []
             ["["
              [(Tactic.simpLemma
                []
                []
                (Term.app (Term.explicit "@" `inv_eq_iff_inv_eq) [(Term.hole "_") (Term.hole "_") `a]))
               ","
               (Tactic.simpLemma [] [] `eq_comm)]
              "]"]
             [])
            [])])))))
     (Term.byTactic
      "by"
      (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.simp "simp" [] [] [] []) [])])))]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.exact', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `prod_involution
   [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`x (Term.hole "_")] [])] "=>" (Init.Logic.«term_⁻¹» `x "⁻¹")))
    (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.simp "simp" [] [] [] []) [])])))
    (Term.fun
     "fun"
     (Term.basicFun
      [(Term.simpleBinder [`a] [])]
      "=>"
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(group
           (Tactic.simp
            "simp"
            ["("
             "config"
             ":="
             (Term.structInst
              "{"
              []
              [(group
                (Term.structInstField (Term.structInstLVal `contextual []) ":=" `Bool.true._@._internal._hyg.0)
                [])]
              (Term.optEllipsis [])
              []
              "}")
             ")"]
            []
            ["[" [(Tactic.simpLemma [] [] `Units.inv_eq_self_iff)] "]"]
            [])
           [])])))))
    (Term.fun
     "fun"
     (Term.basicFun
      [(Term.simpleBinder [`a] [])]
      "=>"
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(group
           (Tactic.simp
            "simp"
            ["("
             "config"
             ":="
             (Term.structInst
              "{"
              []
              [(group
                (Term.structInstField (Term.structInstLVal `contextual []) ":=" `Bool.true._@._internal._hyg.0)
                [])]
              (Term.optEllipsis [])
              []
              "}")
             ")"]
            []
            ["["
             [(Tactic.simpLemma
               []
               []
               (Term.app (Term.explicit "@" `inv_eq_iff_inv_eq) [(Term.hole "_") (Term.hole "_") `a]))
              ","
              (Tactic.simpLemma [] [] `eq_comm)]
             "]"]
            [])
           [])])))))
    (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.simp "simp" [] [] [] []) [])])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.simp "simp" [] [] [] []) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.simp "simp" [] [] [] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.simp "simp" [] [] [] []) [])]))) []]
 ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [`a] [])]
    "=>"
    (Term.byTactic
     "by"
     (Tactic.tacticSeq
      (Tactic.tacticSeq1Indented
       [(group
         (Tactic.simp
          "simp"
          ["("
           "config"
           ":="
           (Term.structInst
            "{"
            []
            [(group (Term.structInstField (Term.structInstLVal `contextual []) ":=" `Bool.true._@._internal._hyg.0) [])]
            (Term.optEllipsis [])
            []
            "}")
           ")"]
          []
          ["["
           [(Tactic.simpLemma
             []
             []
             (Term.app (Term.explicit "@" `inv_eq_iff_inv_eq) [(Term.hole "_") (Term.hole "_") `a]))
            ","
            (Tactic.simpLemma [] [] `eq_comm)]
           "]"]
          [])
         [])])))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.simp
        "simp"
        ["("
         "config"
         ":="
         (Term.structInst
          "{"
          []
          [(group (Term.structInstField (Term.structInstLVal `contextual []) ":=" `Bool.true._@._internal._hyg.0) [])]
          (Term.optEllipsis [])
          []
          "}")
         ")"]
        []
        ["["
         [(Tactic.simpLemma
           []
           []
           (Term.app (Term.explicit "@" `inv_eq_iff_inv_eq) [(Term.hole "_") (Term.hole "_") `a]))
          ","
          (Tactic.simpLemma [] [] `eq_comm)]
         "]"]
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
  (Tactic.simp
   "simp"
   ["("
    "config"
    ":="
    (Term.structInst
     "{"
     []
     [(group (Term.structInstField (Term.structInstLVal `contextual []) ":=" `Bool.true._@._internal._hyg.0) [])]
     (Term.optEllipsis [])
     []
     "}")
    ")"]
   []
   ["["
    [(Tactic.simpLemma [] [] (Term.app (Term.explicit "@" `inv_eq_iff_inv_eq) [(Term.hole "_") (Term.hole "_") `a]))
     ","
     (Tactic.simpLemma [] [] `eq_comm)]
    "]"]
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `eq_comm
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app (Term.explicit "@" `inv_eq_iff_inv_eq) [(Term.hole "_") (Term.hole "_") `a])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `a
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.explicit "@" `inv_eq_iff_inv_eq)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicit', expected 'Lean.Parser.Term.explicit.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `inv_eq_iff_inv_eq
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (some 1024, term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«)»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«)»', expected 'Lean.Parser.Tactic.discharger'
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
  prod_univ_units_id_eq_neg_one
  [ CommRingₓ K ] [ IsDomain K ] [ Fintype Units K ] : ∏ x : Units K , x = ( - 1 : Units K )
  :=
    by
      classical
        have : ∏ x in @ univ Units K _ . erase - 1 , x = 1
        exact
          prod_involution
            fun x _ => x ⁻¹
              by simp
              fun a => by simp ( config := { contextual := Bool.true._@._internal._hyg.0 } ) [ Units.inv_eq_self_iff ]
              fun
                a
                  =>
                  by
                    simp
                      ( config := { contextual := Bool.true._@._internal._hyg.0 } )
                      [ @ inv_eq_iff_inv_eq _ _ a , eq_comm ]
              by simp
        rw [ ← insert_erase mem_univ ( - 1 : Units K ) , prod_insert not_mem_erase _ _ , this , mul_oneₓ ]

section

variable [GroupWithZeroₓ K] [Fintype K]

theorem pow_card_sub_one_eq_one (a : K) (ha : a ≠ 0) : (a^q - 1) = 1 :=
  calc (a^Fintype.card K - 1) = (Units.mk0 a ha^Fintype.card K - 1 : Units K) := by
    rw [Units.coe_pow, Units.coe_mk0]
    _ = 1 := by
    classical
    rw [← Fintype.card_units, pow_card_eq_one]
    rfl
    

theorem pow_card (a : K) : (a^q) = a := by
  have hp : 0 < Fintype.card K := lt_transₓ zero_lt_one Fintype.one_lt_card
  by_cases' h : a = 0
  ·
    rw [h]
    apply zero_pow hp
  rw [← Nat.succ_pred_eq_of_posₓ hp, pow_succₓ, Nat.pred_eq_sub_one, pow_card_sub_one_eq_one a h, mul_oneₓ]

theorem pow_card_pow (n : ℕ) (a : K) : (a^q^n) = a := by
  induction' n with n ih
  ·
    simp
  ·
    simp [pow_succₓ, pow_mulₓ, ih, pow_card]

end

variable (K) [Field K] [Fintype K]

theorem card (p : ℕ) [CharP K p] : ∃ n : ℕ+, Nat.Prime p ∧ q = (p^(n : ℕ)) := by
  have hp : Fact p.prime := ⟨CharP.char_is_prime K p⟩
  let this' : Module (Zmod p) K := { (Zmod.castHom dvd_rfl K).toModule with }
  obtain ⟨n, h⟩ := VectorSpace.card_fintype (Zmod p) K
  rw [Zmod.card] at h
  refine' ⟨⟨n, _⟩, hp.1, h⟩
  apply Or.resolve_left (Nat.eq_zero_or_posₓ n)
  rintro rfl
  rw [pow_zeroₓ] at h
  have : (0 : K) = 1 := by
    apply fintype.card_le_one_iff.mp (le_of_eqₓ h)
  exact absurd this zero_ne_one

theorem card' : ∃ (p : ℕ)(n : ℕ+), Nat.Prime p ∧ Fintype.card K = (p^(n : ℕ)) :=
  let ⟨p, hc⟩ := CharP.exists K
  ⟨p, @FiniteField.card K _ _ p hc⟩

@[simp]
theorem cast_card_eq_zero : (q : K) = 0 := by
  rcases CharP.exists K with ⟨p, _char_p⟩
  skip
  rcases card K p with ⟨n, hp, hn⟩
  simp only [CharP.cast_eq_zero_iff K p, hn]
  conv => congr rw [← pow_oneₓ p]
  exact pow_dvd_pow _ n.2

theorem forall_pow_eq_one_iff (i : ℕ) : (∀ x : Units K, (x^i) = 1) ↔ q - 1 ∣ i := by
  classical
  obtain ⟨x, hx⟩ := IsCyclic.exists_generator (Units K)
  rw [← Fintype.card_units, ← order_of_eq_card_of_forall_mem_zpowers hx, order_of_dvd_iff_pow_eq_one]
  constructor
  ·
    intro h
    apply h
  ·
    intro h y
    simp_rw [← mem_powers_iff_mem_zpowers]  at hx
    rcases hx y with ⟨j, rfl⟩
    rw [← pow_mulₓ, mul_commₓ, pow_mulₓ, h, one_pow]

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  [(Command.docComment
    "/--"
    " The sum of `x ^ i` as `x` ranges over the units of a finite field of cardinality `q`\nis equal to `0` unless `(q - 1) ∣ i`, in which case the sum is `q - 1`. -/")]
  []
  []
  []
  []
  [])
 (Command.theorem
  "theorem"
  (Command.declId `sum_pow_units [])
  (Command.declSig
   [(Term.instBinder "[" [] (Term.app `Fintype [(Term.app `Units [`K])]) "]")
    (Term.explicitBinder "(" [`i] [":" (termℕ "ℕ")] [] ")")]
   (Term.typeSpec
    ":"
    («term_=_»
     (Algebra.BigOperators.Basic.«term∑_,_»
      "∑"
      (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] [":" (Term.app `Units [`K])]))
      ", "
      (Term.paren "(" [(Cardinal.SetTheory.Cofinality.«term_^_» `x "^" `i) [(Term.typeAscription ":" `K)]] ")"))
     "="
     (termIfThenElse
      "if"
      (Init.Core.«term_∣_» («term_-_» (FieldTheory.Finite.Basic.termq "q") "-" (numLit "1")) " ∣ " `i)
      "then"
      («term-_» "-" (numLit "1"))
      "else"
      (numLit "0")))))
  (Command.declValSimple
   ":="
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group
        (Tactic.tacticLet_
         "let"
         (Term.letDecl
          (Term.letIdDecl
           `φ
           [(Term.typeSpec ":" (Algebra.Group.Hom.«term_→*_» (Term.app `Units [`K]) " →* " `K))]
           ":="
           (Term.structInst
            "{"
            []
            [(group
              (Term.structInstField
               (Term.structInstLVal `toFun [])
               ":="
               (Term.fun
                "fun"
                (Term.basicFun [(Term.simpleBinder [`x] [])] "=>" (Cardinal.SetTheory.Cofinality.«term_^_» `x "^" `i))))
              [","])
             (group
              (Term.structInstField
               (Term.structInstLVal `map_one' [])
               ":="
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(group
                    (Tactic.rwSeq
                     "rw"
                     []
                     (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Units.coe_one) "," (Tactic.rwRule [] `one_pow)] "]")
                     [])
                    [])]))))
              [","])
             (group
              (Term.structInstField
               (Term.structInstLVal `map_mul' [])
               ":="
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(group (Tactic.intros "intros" []) [])
                   (group
                    (Tactic.rwSeq
                     "rw"
                     []
                     (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Units.coe_mul) "," (Tactic.rwRule [] `mul_powₓ)] "]")
                     [])
                    [])]))))
              [])]
            (Term.optEllipsis [])
            []
            "}"))))
        [])
       (group
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           []
           [(Term.typeSpec ":" (Term.app `Decidable [(«term_=_» `φ "=" (numLit "1"))]))]
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(group (Tactic.classical "classical") [])
               (group (Tactic.tacticInfer_instance "infer_instance") [])]))))))
        [])
       (group
        (tacticCalc_
         "calc"
         [(calcStep
           («term_=_»
            (Algebra.BigOperators.Basic.«term∑_,_»
             "∑"
             (Lean.explicitBinders
              (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] [":" (Term.app `Units [`K])]))
             ", "
             (Term.app `φ [`x]))
            "="
            (termIfThenElse
             "if"
             («term_=_» `φ "=" (numLit "1"))
             "then"
             (Term.app `Fintype.card [(Term.app `Units [`K])])
             "else"
             (numLit "0")))
           ":="
           (Term.app `sum_hom_units [`φ]))
          (calcStep
           («term_=_»
            (Term.hole "_")
            "="
            (termIfThenElse
             "if"
             (Init.Core.«term_∣_» («term_-_» (FieldTheory.Finite.Basic.termq "q") "-" (numLit "1")) " ∣ " `i)
             "then"
             («term-_» "-" (numLit "1"))
             "else"
             (numLit "0")))
           ":="
           (Term.hole "_"))])
        [])
       (group
        (Tactic.tacticSuffices_
         "suffices"
         (Term.sufficesDecl
          []
          («term_↔_»
           (Init.Core.«term_∣_» («term_-_» (FieldTheory.Finite.Basic.termq "q") "-" (numLit "1")) " ∣ " `i)
           "↔"
           («term_=_» `φ "=" (numLit "1")))
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group (Tactic.simp "simp" [] ["only"] ["[" [(Tactic.simpLemma [] [] `this)] "]"] []) [])
              (group (Tactic.splitIfs "split_ifs" [] ["with" [(Lean.binderIdent `h) (Lean.binderIdent `h)]]) [])
              (group (Tactic.swap "swap" []) [])
              (group (Tactic.tacticRfl "rfl") [])
              (group
               (Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule [] `Fintype.card_units)
                  ","
                  (Tactic.rwRule [] `Nat.cast_sub)
                  ","
                  (Tactic.rwRule [] `cast_card_eq_zero)
                  ","
                  (Tactic.rwRule [] `Nat.cast_one)
                  ","
                  (Tactic.rwRule [] `zero_sub)]
                 "]")
                [])
               [])
              (group (Tactic.tacticShow_ "show" («term_≤_» (numLit "1") "≤" (FieldTheory.Finite.Basic.termq "q"))) [])
              (group
               (Tactic.exact "exact" (Term.app `fintype.card_pos_iff.mpr [(Term.anonymousCtor "⟨" [(numLit "0")] "⟩")]))
               [])])))))
        [])
       (group
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule ["←"] `forall_pow_eq_one_iff) "," (Tactic.rwRule [] `MonoidHom.ext_iff)]
          "]")
         [])
        [])
       (group (Tactic.apply "apply" `forall_congrₓ) [])
       (group (Tactic.intro "intro" [`x]) [])
       (group
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule [] `Units.ext_iff)
           ","
           (Tactic.rwRule [] `Units.coe_pow)
           ","
           (Tactic.rwRule [] `Units.coe_one)
           ","
           (Tactic.rwRule [] `MonoidHom.one_apply)]
          "]")
         [])
        [])
       (group (Tactic.tacticRfl "rfl") [])])))
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
       (Tactic.tacticLet_
        "let"
        (Term.letDecl
         (Term.letIdDecl
          `φ
          [(Term.typeSpec ":" (Algebra.Group.Hom.«term_→*_» (Term.app `Units [`K]) " →* " `K))]
          ":="
          (Term.structInst
           "{"
           []
           [(group
             (Term.structInstField
              (Term.structInstLVal `toFun [])
              ":="
              (Term.fun
               "fun"
               (Term.basicFun [(Term.simpleBinder [`x] [])] "=>" (Cardinal.SetTheory.Cofinality.«term_^_» `x "^" `i))))
             [","])
            (group
             (Term.structInstField
              (Term.structInstLVal `map_one' [])
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(group
                   (Tactic.rwSeq
                    "rw"
                    []
                    (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Units.coe_one) "," (Tactic.rwRule [] `one_pow)] "]")
                    [])
                   [])]))))
             [","])
            (group
             (Term.structInstField
              (Term.structInstLVal `map_mul' [])
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(group (Tactic.intros "intros" []) [])
                  (group
                   (Tactic.rwSeq
                    "rw"
                    []
                    (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Units.coe_mul) "," (Tactic.rwRule [] `mul_powₓ)] "]")
                    [])
                   [])]))))
             [])]
           (Term.optEllipsis [])
           []
           "}"))))
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          []
          [(Term.typeSpec ":" (Term.app `Decidable [(«term_=_» `φ "=" (numLit "1"))]))]
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group (Tactic.classical "classical") []) (group (Tactic.tacticInfer_instance "infer_instance") [])]))))))
       [])
      (group
       (tacticCalc_
        "calc"
        [(calcStep
          («term_=_»
           (Algebra.BigOperators.Basic.«term∑_,_»
            "∑"
            (Lean.explicitBinders
             (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] [":" (Term.app `Units [`K])]))
            ", "
            (Term.app `φ [`x]))
           "="
           (termIfThenElse
            "if"
            («term_=_» `φ "=" (numLit "1"))
            "then"
            (Term.app `Fintype.card [(Term.app `Units [`K])])
            "else"
            (numLit "0")))
          ":="
          (Term.app `sum_hom_units [`φ]))
         (calcStep
          («term_=_»
           (Term.hole "_")
           "="
           (termIfThenElse
            "if"
            (Init.Core.«term_∣_» («term_-_» (FieldTheory.Finite.Basic.termq "q") "-" (numLit "1")) " ∣ " `i)
            "then"
            («term-_» "-" (numLit "1"))
            "else"
            (numLit "0")))
          ":="
          (Term.hole "_"))])
       [])
      (group
       (Tactic.tacticSuffices_
        "suffices"
        (Term.sufficesDecl
         []
         («term_↔_»
          (Init.Core.«term_∣_» («term_-_» (FieldTheory.Finite.Basic.termq "q") "-" (numLit "1")) " ∣ " `i)
          "↔"
          («term_=_» `φ "=" (numLit "1")))
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(group (Tactic.simp "simp" [] ["only"] ["[" [(Tactic.simpLemma [] [] `this)] "]"] []) [])
             (group (Tactic.splitIfs "split_ifs" [] ["with" [(Lean.binderIdent `h) (Lean.binderIdent `h)]]) [])
             (group (Tactic.swap "swap" []) [])
             (group (Tactic.tacticRfl "rfl") [])
             (group
              (Tactic.rwSeq
               "rw"
               []
               (Tactic.rwRuleSeq
                "["
                [(Tactic.rwRule [] `Fintype.card_units)
                 ","
                 (Tactic.rwRule [] `Nat.cast_sub)
                 ","
                 (Tactic.rwRule [] `cast_card_eq_zero)
                 ","
                 (Tactic.rwRule [] `Nat.cast_one)
                 ","
                 (Tactic.rwRule [] `zero_sub)]
                "]")
               [])
              [])
             (group (Tactic.tacticShow_ "show" («term_≤_» (numLit "1") "≤" (FieldTheory.Finite.Basic.termq "q"))) [])
             (group
              (Tactic.exact "exact" (Term.app `fintype.card_pos_iff.mpr [(Term.anonymousCtor "⟨" [(numLit "0")] "⟩")]))
              [])])))))
       [])
      (group
       (Tactic.rwSeq
        "rw"
        []
        (Tactic.rwRuleSeq
         "["
         [(Tactic.rwRule ["←"] `forall_pow_eq_one_iff) "," (Tactic.rwRule [] `MonoidHom.ext_iff)]
         "]")
        [])
       [])
      (group (Tactic.apply "apply" `forall_congrₓ) [])
      (group (Tactic.intro "intro" [`x]) [])
      (group
       (Tactic.rwSeq
        "rw"
        []
        (Tactic.rwRuleSeq
         "["
         [(Tactic.rwRule [] `Units.ext_iff)
          ","
          (Tactic.rwRule [] `Units.coe_pow)
          ","
          (Tactic.rwRule [] `Units.coe_one)
          ","
          (Tactic.rwRule [] `MonoidHom.one_apply)]
         "]")
        [])
       [])
      (group (Tactic.tacticRfl "rfl") [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.tacticRfl "rfl")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticRfl', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, tactic))
  (Tactic.rwSeq
   "rw"
   []
   (Tactic.rwRuleSeq
    "["
    [(Tactic.rwRule [] `Units.ext_iff)
     ","
     (Tactic.rwRule [] `Units.coe_pow)
     ","
     (Tactic.rwRule [] `Units.coe_one)
     ","
     (Tactic.rwRule [] `MonoidHom.one_apply)]
    "]")
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwSeq', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `MonoidHom.one_apply
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Units.coe_one
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Units.coe_pow
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Units.ext_iff
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
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
  (Tactic.apply "apply" `forall_congrₓ)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.apply', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `forall_congrₓ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.rwSeq
   "rw"
   []
   (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `forall_pow_eq_one_iff) "," (Tactic.rwRule [] `MonoidHom.ext_iff)] "]")
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwSeq', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `MonoidHom.ext_iff
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `forall_pow_eq_one_iff
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«←»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.tacticSuffices_
   "suffices"
   (Term.sufficesDecl
    []
    («term_↔_»
     (Init.Core.«term_∣_» («term_-_» (FieldTheory.Finite.Basic.termq "q") "-" (numLit "1")) " ∣ " `i)
     "↔"
     («term_=_» `φ "=" (numLit "1")))
    (Term.byTactic
     "by"
     (Tactic.tacticSeq
      (Tactic.tacticSeq1Indented
       [(group (Tactic.simp "simp" [] ["only"] ["[" [(Tactic.simpLemma [] [] `this)] "]"] []) [])
        (group (Tactic.splitIfs "split_ifs" [] ["with" [(Lean.binderIdent `h) (Lean.binderIdent `h)]]) [])
        (group (Tactic.swap "swap" []) [])
        (group (Tactic.tacticRfl "rfl") [])
        (group
         (Tactic.rwSeq
          "rw"
          []
          (Tactic.rwRuleSeq
           "["
           [(Tactic.rwRule [] `Fintype.card_units)
            ","
            (Tactic.rwRule [] `Nat.cast_sub)
            ","
            (Tactic.rwRule [] `cast_card_eq_zero)
            ","
            (Tactic.rwRule [] `Nat.cast_one)
            ","
            (Tactic.rwRule [] `zero_sub)]
           "]")
          [])
         [])
        (group (Tactic.tacticShow_ "show" («term_≤_» (numLit "1") "≤" (FieldTheory.Finite.Basic.termq "q"))) [])
        (group
         (Tactic.exact "exact" (Term.app `fintype.card_pos_iff.mpr [(Term.anonymousCtor "⟨" [(numLit "0")] "⟩")]))
         [])])))))
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
  (Tactic.exact "exact" (Term.app `fintype.card_pos_iff.mpr [(Term.anonymousCtor "⟨" [(numLit "0")] "⟩")]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.exact', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `fintype.card_pos_iff.mpr [(Term.anonymousCtor "⟨" [(numLit "0")] "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor "⟨" [(numLit "0")] "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "0")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `fintype.card_pos_iff.mpr
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.tacticShow_ "show" («term_≤_» (numLit "1") "≤" (FieldTheory.Finite.Basic.termq "q")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticShow_', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_≤_» (numLit "1") "≤" (FieldTheory.Finite.Basic.termq "q"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_≤_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (FieldTheory.Finite.Basic.termq "q")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'FieldTheory.Finite.Basic.termq', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (numLit "1")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.rwSeq
   "rw"
   []
   (Tactic.rwRuleSeq
    "["
    [(Tactic.rwRule [] `Fintype.card_units)
     ","
     (Tactic.rwRule [] `Nat.cast_sub)
     ","
     (Tactic.rwRule [] `cast_card_eq_zero)
     ","
     (Tactic.rwRule [] `Nat.cast_one)
     ","
     (Tactic.rwRule [] `zero_sub)]
    "]")
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwSeq', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `zero_sub
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Nat.cast_one
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `cast_card_eq_zero
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Nat.cast_sub
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Fintype.card_units
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.tacticRfl "rfl")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticRfl', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, tactic))
  (Tactic.swap "swap" [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.swap', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.splitIfs "split_ifs" [] ["with" [(Lean.binderIdent `h) (Lean.binderIdent `h)]])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.splitIfs', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.binderIdent', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.binderIdent', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.simp "simp" [] ["only"] ["[" [(Tactic.simpLemma [] [] `this)] "]"] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `this
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'only', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, [anonymous]))
  («term_↔_»
   (Init.Core.«term_∣_» («term_-_» (FieldTheory.Finite.Basic.termq "q") "-" (numLit "1")) " ∣ " `i)
   "↔"
   («term_=_» `φ "=" (numLit "1")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_↔_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_=_» `φ "=" (numLit "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "1")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  `φ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 21 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 20, term))
  (Init.Core.«term_∣_» («term_-_» (FieldTheory.Finite.Basic.termq "q") "-" (numLit "1")) " ∣ " `i)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Core.«term_∣_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `i
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  («term_-_» (FieldTheory.Finite.Basic.termq "q") "-" (numLit "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_-_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "1")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
  (FieldTheory.Finite.Basic.termq "q")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'FieldTheory.Finite.Basic.termq', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 50 >? 65, (some 66, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 21 >? 50, (some 51, term) <=? (some 20, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 20, (some 21, term) <=? (some 1022, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (tacticCalc_
   "calc"
   [(calcStep
     («term_=_»
      (Algebra.BigOperators.Basic.«term∑_,_»
       "∑"
       (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] [":" (Term.app `Units [`K])]))
       ", "
       (Term.app `φ [`x]))
      "="
      (termIfThenElse
       "if"
       («term_=_» `φ "=" (numLit "1"))
       "then"
       (Term.app `Fintype.card [(Term.app `Units [`K])])
       "else"
       (numLit "0")))
     ":="
     (Term.app `sum_hom_units [`φ]))
    (calcStep
     («term_=_»
      (Term.hole "_")
      "="
      (termIfThenElse
       "if"
       (Init.Core.«term_∣_» («term_-_» (FieldTheory.Finite.Basic.termq "q") "-" (numLit "1")) " ∣ " `i)
       "then"
       («term-_» "-" (numLit "1"))
       "else"
       (numLit "0")))
     ":="
     (Term.hole "_"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'tacticCalc_', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'calcStep', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_=_»
   (Term.hole "_")
   "="
   (termIfThenElse
    "if"
    (Init.Core.«term_∣_» («term_-_» (FieldTheory.Finite.Basic.termq "q") "-" (numLit "1")) " ∣ " `i)
    "then"
    («term-_» "-" (numLit "1"))
    "else"
    (numLit "0")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (termIfThenElse
   "if"
   (Init.Core.«term_∣_» («term_-_» (FieldTheory.Finite.Basic.termq "q") "-" (numLit "1")) " ∣ " `i)
   "then"
   («term-_» "-" (numLit "1"))
   "else"
   (numLit "0"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'termIfThenElse', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "0")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term-_» "-" (numLit "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term-_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "1")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 100 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 100, (some 100, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Core.«term_∣_» («term_-_» (FieldTheory.Finite.Basic.termq "q") "-" (numLit "1")) " ∣ " `i)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Core.«term_∣_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `i
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  («term_-_» (FieldTheory.Finite.Basic.termq "q") "-" (numLit "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_-_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "1")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
  (FieldTheory.Finite.Basic.termq "q")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'FieldTheory.Finite.Basic.termq', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 50 >? 65, (some 66, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'calcStep', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
  (Term.app `sum_hom_units [`φ])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `φ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `sum_hom_units
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_=_»
   (Algebra.BigOperators.Basic.«term∑_,_»
    "∑"
    (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] [":" (Term.app `Units [`K])]))
    ", "
    (Term.app `φ [`x]))
   "="
   (termIfThenElse
    "if"
    («term_=_» `φ "=" (numLit "1"))
    "then"
    (Term.app `Fintype.card [(Term.app `Units [`K])])
    "else"
    (numLit "0")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (termIfThenElse
   "if"
   («term_=_» `φ "=" (numLit "1"))
   "then"
   (Term.app `Fintype.card [(Term.app `Units [`K])])
   "else"
   (numLit "0"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'termIfThenElse', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "0")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Fintype.card [(Term.app `Units [`K])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Units [`K])
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
  `Units
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `Units [`K]) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Fintype.card
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_=_» `φ "=" (numLit "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "1")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  `φ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Algebra.BigOperators.Basic.«term∑_,_»
   "∑"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] [":" (Term.app `Units [`K])]))
   ", "
   (Term.app `φ [`x]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.BigOperators.Basic.«term∑_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `φ [`x])
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
  `φ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.explicitBinders', expected 'Mathlib.ExtendedBinder.extBinders'
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
/--
    The sum of `x ^ i` as `x` ranges over the units of a finite field of cardinality `q`
    is equal to `0` unless `(q - 1) ∣ i`, in which case the sum is `q - 1`. -/
  theorem
    sum_pow_units
    [ Fintype Units K ] ( i : ℕ ) : ∑ x : Units K , ( x ^ i : K ) = if q - 1 ∣ i then - 1 else 0
    :=
      by
        let
            φ
              : Units K →* K
              :=
              {
                toFun := fun x => x ^ i ,
                  map_one' := by rw [ Units.coe_one , one_pow ] ,
                  map_mul' := by intros rw [ Units.coe_mul , mul_powₓ ]
                }
          have : Decidable φ = 1 := by classical infer_instance
          calc
            ∑ x : Units K , φ x = if φ = 1 then Fintype.card Units K else 0 := sum_hom_units φ
              _ = if q - 1 ∣ i then - 1 else 0 := _
          suffices
            q - 1 ∣ i ↔ φ = 1
              by
                simp only [ this ]
                  split_ifs with h h
                  swap
                  rfl
                  rw [ Fintype.card_units , Nat.cast_sub , cast_card_eq_zero , Nat.cast_one , zero_sub ]
                  show 1 ≤ q
                  exact fintype.card_pos_iff.mpr ⟨ 0 ⟩
          rw [ ← forall_pow_eq_one_iff , MonoidHom.ext_iff ]
          apply forall_congrₓ
          intro x
          rw [ Units.ext_iff , Units.coe_pow , Units.coe_one , MonoidHom.one_apply ]
          rfl

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  [(Command.docComment
    "/--"
    " The sum of `x ^ i` as `x` ranges over a finite field of cardinality `q`\nis equal to `0` if `i < q - 1`. -/")]
  []
  []
  []
  []
  [])
 (Command.theorem
  "theorem"
  (Command.declId `sum_pow_lt_card_sub_one [])
  (Command.declSig
   [(Term.explicitBinder "(" [`i] [":" (termℕ "ℕ")] [] ")")
    (Term.explicitBinder
     "("
     [`h]
     [":" («term_<_» `i "<" («term_-_» (FieldTheory.Finite.Basic.termq "q") "-" (numLit "1")))]
     []
     ")")]
   (Term.typeSpec
    ":"
    («term_=_»
     (Algebra.BigOperators.Basic.«term∑_,_»
      "∑"
      (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] [":" `K]))
      ", "
      (Cardinal.SetTheory.Cofinality.«term_^_» `x "^" `i))
     "="
     (numLit "0"))))
  (Command.declValSimple
   ":="
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group (Tactic.byCases' "by_cases'" [`hi ":"] («term_=_» `i "=" (numLit "0"))) [])
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
               [(Tactic.simpLemma [] [] `hi)
                ","
                (Tactic.simpLemma [] [] `nsmul_one)
                ","
                (Tactic.simpLemma [] [] `sum_const)
                ","
                (Tactic.simpLemma [] [] `pow_zeroₓ)
                ","
                (Tactic.simpLemma [] [] `card_univ)
                ","
                (Tactic.simpLemma [] [] `cast_card_eq_zero)]
               "]"]
              [])
             [])])))
        [])
       (group (Tactic.classical "classical") [])
       (group
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`hiq []]
           [(Term.typeSpec
             ":"
             («term¬_»
              "¬"
              (Init.Core.«term_∣_» («term_-_» (FieldTheory.Finite.Basic.termq "q") "-" (numLit "1")) " ∣ " `i)))]
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(group (Tactic.contrapose! "contrapose!" [`h []]) [])
               (group
                (Tactic.exact "exact" (Term.app `Nat.le_of_dvdₓ [(Term.app `Nat.pos_of_ne_zeroₓ [`hi]) `h]))
                [])]))))))
        [])
       (group
        (Tactic.tacticLet_
         "let"
         (Term.letDecl
          (Term.letIdDecl
           `φ
           [(Term.typeSpec ":" (Function.Logic.Embedding.«term_↪_» (Term.app `Units [`K]) " ↪ " `K))]
           ":="
           (Term.anonymousCtor "⟨" [`coeₓ "," `Units.ext] "⟩"))))
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
              (Term.app `univ.map [`φ])
              "="
              (Init.Core.«term_\_» `univ " \\ " (Set.«term{_}» "{" [(numLit "0")] "}"))))]
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(group (Tactic.ext "ext" [(Tactic.rcasesPat.one `x)] []) [])
               (group
                (Tactic.simp
                 "simp"
                 []
                 ["only"]
                 ["["
                  [(Tactic.simpLemma [] [] `true_andₓ)
                   ","
                   (Tactic.simpLemma [] [] `embedding.coe_fn_mk)
                   ","
                   (Tactic.simpLemma [] [] `mem_sdiff)
                   ","
                   (Tactic.simpLemma [] [] `Units.exists_iff_ne_zero)
                   ","
                   (Tactic.simpLemma [] [] `mem_univ)
                   ","
                   (Tactic.simpLemma [] [] `mem_map)
                   ","
                   (Tactic.simpLemma [] [] `exists_prop_of_true)
                   ","
                   (Tactic.simpLemma [] [] `mem_singleton)]
                  "]"]
                 [])
                [])]))))))
        [])
       (group
        (tacticCalc_
         "calc"
         [(calcStep
           («term_=_»
            (Algebra.BigOperators.Basic.«term∑_,_»
             "∑"
             (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] [":" `K]))
             ", "
             (Cardinal.SetTheory.Cofinality.«term_^_» `x "^" `i))
            "="
            (Algebra.BigOperators.Basic.«term∑_in_,_»
             "∑"
             (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
             " in "
             (Init.Core.«term_\_»
              `univ
              " \\ "
              (Set.«term{_}» "{" [(Term.paren "(" [(numLit "0") [(Term.typeAscription ":" `K)]] ")")] "}"))
             ", "
             (Cardinal.SetTheory.Cofinality.«term_^_» `x "^" `i)))
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
                  [(Tactic.rwRule
                    ["←"]
                    (Term.app
                     `sum_sdiff
                     [(Term.proj
                       (Term.paren
                        "("
                        [(Set.«term{_}» "{" [(numLit "0")] "}") [(Term.typeAscription ":" (Term.app `Finset [`K]))]]
                        ")")
                       "."
                       `subset_univ)]))
                   ","
                   (Tactic.rwRule [] `sum_singleton)
                   ","
                   (Tactic.rwRule [] (Term.app `zero_pow [(Term.app `Nat.pos_of_ne_zeroₓ [`hi])]))
                   ","
                   (Tactic.rwRule [] `add_zeroₓ)]
                  "]")
                 [])
                [])]))))
          (calcStep
           («term_=_»
            (Term.hole "_")
            "="
            (Algebra.BigOperators.Basic.«term∑_,_»
             "∑"
             (Lean.explicitBinders
              (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] [":" (Term.app `Units [`K])]))
             ", "
             (Cardinal.SetTheory.Cofinality.«term_^_» `x "^" `i)))
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
                  [(Tactic.rwRule ["←"] `this) "," (Tactic.rwRule [] (Term.app `univ.sum_map [`φ]))]
                  "]")
                 [])
                [])
               (group (Tactic.tacticRfl "rfl") [])]))))
          (calcStep
           («term_=_» (Term.hole "_") "=" (numLit "0"))
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
                  [(Tactic.rwRule [] (Term.app `sum_pow_units [`K `i])) "," (Tactic.rwRule [] `if_neg)]
                  "]")
                 [])
                [])
               (group (Tactic.exact "exact" `hiq) [])]))))])
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
     [(group (Tactic.byCases' "by_cases'" [`hi ":"] («term_=_» `i "=" (numLit "0"))) [])
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
              [(Tactic.simpLemma [] [] `hi)
               ","
               (Tactic.simpLemma [] [] `nsmul_one)
               ","
               (Tactic.simpLemma [] [] `sum_const)
               ","
               (Tactic.simpLemma [] [] `pow_zeroₓ)
               ","
               (Tactic.simpLemma [] [] `card_univ)
               ","
               (Tactic.simpLemma [] [] `cast_card_eq_zero)]
              "]"]
             [])
            [])])))
       [])
      (group (Tactic.classical "classical") [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`hiq []]
          [(Term.typeSpec
            ":"
            («term¬_»
             "¬"
             (Init.Core.«term_∣_» («term_-_» (FieldTheory.Finite.Basic.termq "q") "-" (numLit "1")) " ∣ " `i)))]
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group (Tactic.contrapose! "contrapose!" [`h []]) [])
              (group
               (Tactic.exact "exact" (Term.app `Nat.le_of_dvdₓ [(Term.app `Nat.pos_of_ne_zeroₓ [`hi]) `h]))
               [])]))))))
       [])
      (group
       (Tactic.tacticLet_
        "let"
        (Term.letDecl
         (Term.letIdDecl
          `φ
          [(Term.typeSpec ":" (Function.Logic.Embedding.«term_↪_» (Term.app `Units [`K]) " ↪ " `K))]
          ":="
          (Term.anonymousCtor "⟨" [`coeₓ "," `Units.ext] "⟩"))))
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
             (Term.app `univ.map [`φ])
             "="
             (Init.Core.«term_\_» `univ " \\ " (Set.«term{_}» "{" [(numLit "0")] "}"))))]
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group (Tactic.ext "ext" [(Tactic.rcasesPat.one `x)] []) [])
              (group
               (Tactic.simp
                "simp"
                []
                ["only"]
                ["["
                 [(Tactic.simpLemma [] [] `true_andₓ)
                  ","
                  (Tactic.simpLemma [] [] `embedding.coe_fn_mk)
                  ","
                  (Tactic.simpLemma [] [] `mem_sdiff)
                  ","
                  (Tactic.simpLemma [] [] `Units.exists_iff_ne_zero)
                  ","
                  (Tactic.simpLemma [] [] `mem_univ)
                  ","
                  (Tactic.simpLemma [] [] `mem_map)
                  ","
                  (Tactic.simpLemma [] [] `exists_prop_of_true)
                  ","
                  (Tactic.simpLemma [] [] `mem_singleton)]
                 "]"]
                [])
               [])]))))))
       [])
      (group
       (tacticCalc_
        "calc"
        [(calcStep
          («term_=_»
           (Algebra.BigOperators.Basic.«term∑_,_»
            "∑"
            (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] [":" `K]))
            ", "
            (Cardinal.SetTheory.Cofinality.«term_^_» `x "^" `i))
           "="
           (Algebra.BigOperators.Basic.«term∑_in_,_»
            "∑"
            (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
            " in "
            (Init.Core.«term_\_»
             `univ
             " \\ "
             (Set.«term{_}» "{" [(Term.paren "(" [(numLit "0") [(Term.typeAscription ":" `K)]] ")")] "}"))
            ", "
            (Cardinal.SetTheory.Cofinality.«term_^_» `x "^" `i)))
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
                 [(Tactic.rwRule
                   ["←"]
                   (Term.app
                    `sum_sdiff
                    [(Term.proj
                      (Term.paren
                       "("
                       [(Set.«term{_}» "{" [(numLit "0")] "}") [(Term.typeAscription ":" (Term.app `Finset [`K]))]]
                       ")")
                      "."
                      `subset_univ)]))
                  ","
                  (Tactic.rwRule [] `sum_singleton)
                  ","
                  (Tactic.rwRule [] (Term.app `zero_pow [(Term.app `Nat.pos_of_ne_zeroₓ [`hi])]))
                  ","
                  (Tactic.rwRule [] `add_zeroₓ)]
                 "]")
                [])
               [])]))))
         (calcStep
          («term_=_»
           (Term.hole "_")
           "="
           (Algebra.BigOperators.Basic.«term∑_,_»
            "∑"
            (Lean.explicitBinders
             (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] [":" (Term.app `Units [`K])]))
            ", "
            (Cardinal.SetTheory.Cofinality.«term_^_» `x "^" `i)))
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
                 [(Tactic.rwRule ["←"] `this) "," (Tactic.rwRule [] (Term.app `univ.sum_map [`φ]))]
                 "]")
                [])
               [])
              (group (Tactic.tacticRfl "rfl") [])]))))
         (calcStep
          («term_=_» (Term.hole "_") "=" (numLit "0"))
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
                 [(Tactic.rwRule [] (Term.app `sum_pow_units [`K `i])) "," (Tactic.rwRule [] `if_neg)]
                 "]")
                [])
               [])
              (group (Tactic.exact "exact" `hiq) [])]))))])
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (tacticCalc_
   "calc"
   [(calcStep
     («term_=_»
      (Algebra.BigOperators.Basic.«term∑_,_»
       "∑"
       (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] [":" `K]))
       ", "
       (Cardinal.SetTheory.Cofinality.«term_^_» `x "^" `i))
      "="
      (Algebra.BigOperators.Basic.«term∑_in_,_»
       "∑"
       (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
       " in "
       (Init.Core.«term_\_»
        `univ
        " \\ "
        (Set.«term{_}» "{" [(Term.paren "(" [(numLit "0") [(Term.typeAscription ":" `K)]] ")")] "}"))
       ", "
       (Cardinal.SetTheory.Cofinality.«term_^_» `x "^" `i)))
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
            [(Tactic.rwRule
              ["←"]
              (Term.app
               `sum_sdiff
               [(Term.proj
                 (Term.paren
                  "("
                  [(Set.«term{_}» "{" [(numLit "0")] "}") [(Term.typeAscription ":" (Term.app `Finset [`K]))]]
                  ")")
                 "."
                 `subset_univ)]))
             ","
             (Tactic.rwRule [] `sum_singleton)
             ","
             (Tactic.rwRule [] (Term.app `zero_pow [(Term.app `Nat.pos_of_ne_zeroₓ [`hi])]))
             ","
             (Tactic.rwRule [] `add_zeroₓ)]
            "]")
           [])
          [])]))))
    (calcStep
     («term_=_»
      (Term.hole "_")
      "="
      (Algebra.BigOperators.Basic.«term∑_,_»
       "∑"
       (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] [":" (Term.app `Units [`K])]))
       ", "
       (Cardinal.SetTheory.Cofinality.«term_^_» `x "^" `i)))
     ":="
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(group
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `this) "," (Tactic.rwRule [] (Term.app `univ.sum_map [`φ]))] "]")
           [])
          [])
         (group (Tactic.tacticRfl "rfl") [])]))))
    (calcStep
     («term_=_» (Term.hole "_") "=" (numLit "0"))
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
            [(Tactic.rwRule [] (Term.app `sum_pow_units [`K `i])) "," (Tactic.rwRule [] `if_neg)]
            "]")
           [])
          [])
         (group (Tactic.exact "exact" `hiq) [])]))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'tacticCalc_', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'calcStep', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.rwSeq
        "rw"
        []
        (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `sum_pow_units [`K `i])) "," (Tactic.rwRule [] `if_neg)] "]")
        [])
       [])
      (group (Tactic.exact "exact" `hiq) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.exact "exact" `hiq)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.exact', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hiq
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.rwSeq
   "rw"
   []
   (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `sum_pow_units [`K `i])) "," (Tactic.rwRule [] `if_neg)] "]")
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwSeq', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `if_neg
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `sum_pow_units [`K `i])
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
  `K
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `sum_pow_units
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_=_» (Term.hole "_") "=" (numLit "0"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "0")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'calcStep', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.rwSeq
        "rw"
        []
        (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `this) "," (Tactic.rwRule [] (Term.app `univ.sum_map [`φ]))] "]")
        [])
       [])
      (group (Tactic.tacticRfl "rfl") [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.tacticRfl "rfl")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticRfl', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, tactic))
  (Tactic.rwSeq
   "rw"
   []
   (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `this) "," (Tactic.rwRule [] (Term.app `univ.sum_map [`φ]))] "]")
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwSeq', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `univ.sum_map [`φ])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `φ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `univ.sum_map
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `this
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«←»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_=_»
   (Term.hole "_")
   "="
   (Algebra.BigOperators.Basic.«term∑_,_»
    "∑"
    (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] [":" (Term.app `Units [`K])]))
    ", "
    (Cardinal.SetTheory.Cofinality.«term_^_» `x "^" `i)))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Algebra.BigOperators.Basic.«term∑_,_»
   "∑"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] [":" (Term.app `Units [`K])]))
   ", "
   (Cardinal.SetTheory.Cofinality.«term_^_» `x "^" `i))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.BigOperators.Basic.«term∑_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Cardinal.SetTheory.Cofinality.«term_^_» `x "^" `i)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Cardinal.SetTheory.Cofinality.«term_^_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `i
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 0, term))
  `x
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1 >? 1024, (none, [anonymous]) <=? (some 0, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 0, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.explicitBinders', expected 'Mathlib.ExtendedBinder.extBinders'
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
/--
    The sum of `x ^ i` as `x` ranges over a finite field of cardinality `q`
    is equal to `0` if `i < q - 1`. -/
  theorem
    sum_pow_lt_card_sub_one
    ( i : ℕ ) ( h : i < q - 1 ) : ∑ x : K , x ^ i = 0
    :=
      by
        by_cases' hi : i = 0
          · simp only [ hi , nsmul_one , sum_const , pow_zeroₓ , card_univ , cast_card_eq_zero ]
          classical
          have hiq : ¬ q - 1 ∣ i := by contrapose! h exact Nat.le_of_dvdₓ Nat.pos_of_ne_zeroₓ hi h
          let φ : Units K ↪ K := ⟨ coeₓ , Units.ext ⟩
          have
            : univ.map φ = univ \ { 0 }
              :=
              by
                ext x
                  simp
                    only
                    [
                      true_andₓ
                        ,
                        embedding.coe_fn_mk
                        ,
                        mem_sdiff
                        ,
                        Units.exists_iff_ne_zero
                        ,
                        mem_univ
                        ,
                        mem_map
                        ,
                        exists_prop_of_true
                        ,
                        mem_singleton
                      ]
          calc
            ∑ x : K , x ^ i = ∑ x in univ \ { ( 0 : K ) } , x ^ i
                :=
                by
                  rw
                    [
                      ← sum_sdiff ( { 0 } : Finset K ) . subset_univ
                        ,
                        sum_singleton
                        ,
                        zero_pow Nat.pos_of_ne_zeroₓ hi
                        ,
                        add_zeroₓ
                      ]
              _ = ∑ x : Units K , x ^ i := by rw [ ← this , univ.sum_map φ ] rfl
              _ = 0 := by rw [ sum_pow_units K i , if_neg ] exact hiq

section IsSplittingField

open Polynomial

section

variable (K' : Type _) [Field K'] {p n : ℕ}

theorem X_pow_card_sub_X_nat_degree_eq (hp : 1 < p) : ((X^p) - X : Polynomial K').natDegree = p := by
  have h1 : (X : Polynomial K').degree < (X^p : Polynomial K').degree := by
    rw [degree_X_pow, degree_X]
    exact_mod_cast hp
  rw [nat_degree_eq_of_degree_eq (degree_sub_eq_left_of_degree_lt h1), nat_degree_X_pow]

theorem X_pow_card_pow_sub_X_nat_degree_eq (hn : n ≠ 0) (hp : 1 < p) :
    ((X^p^n) - X : Polynomial K').natDegree = (p^n) :=
  X_pow_card_sub_X_nat_degree_eq K' $ Nat.one_lt_pow _ _ (Nat.pos_of_ne_zeroₓ hn) hp

theorem X_pow_card_sub_X_ne_zero (hp : 1 < p) : ((X^p) - X : Polynomial K') ≠ 0 :=
  ne_zero_of_nat_degree_gt $
    calc 1 < _ := hp
      _ = _ := (X_pow_card_sub_X_nat_degree_eq K' hp).symm
      

theorem X_pow_card_pow_sub_X_ne_zero (hn : n ≠ 0) (hp : 1 < p) : ((X^p^n) - X : Polynomial K') ≠ 0 :=
  X_pow_card_sub_X_ne_zero K' $ Nat.one_lt_pow _ _ (Nat.pos_of_ne_zeroₓ hn) hp

end

variable (p : ℕ) [Fact p.prime] [CharP K p]

theorem roots_X_pow_card_sub_X : roots ((X^q) - X : Polynomial K) = Finset.univ.val := by
  classical
  have aux : ((X^q) - X : Polynomial K) ≠ 0 := X_pow_card_sub_X_ne_zero K Fintype.one_lt_card
  have : (roots ((X^q) - X : Polynomial K)).toFinset = Finset.univ := by
    rw [eq_univ_iff_forall]
    intro x
    rw [Multiset.mem_to_finset, mem_roots aux, is_root.def, eval_sub, eval_pow, eval_X, sub_eq_zero, pow_card]
  rw [← this, Multiset.to_finset_val, eq_comm, Multiset.erase_dup_eq_self]
  apply nodup_roots
  rw [separable_def]
  convert is_coprime_one_right.neg_right
  rw [derivative_sub, derivative_X, derivative_X_pow, ← C_eq_nat_cast, C_eq_zero.mpr (CharP.cast_card_eq_zero K),
    zero_mul, zero_sub]

instance : is_splitting_field (Zmod p) K ((X^q) - X) where
  Splits := by
    have h : ((X^q) - X : Polynomial K).natDegree = q := X_pow_card_sub_X_nat_degree_eq K Fintype.one_lt_card
    rw [← splits_id_iff_splits, splits_iff_card_roots, Polynomial.map_sub, Polynomial.map_pow, map_X, h,
      roots_X_pow_card_sub_X K, ← Finset.card_def, Finset.card_univ]
  adjoin_roots := by
    classical
    trans Algebra.adjoin (Zmod p) ((roots ((X^q) - X : Polynomial K)).toFinset : Set K)
    ·
      simp only [Polynomial.map_pow, map_X, Polynomial.map_sub]
      convert rfl
    ·
      rw [roots_X_pow_card_sub_X, val_to_finset, coe_univ, Algebra.adjoin_univ]

end IsSplittingField

variable {K}

theorem frobenius_pow {p : ℕ} [Fact p.prime] [CharP K p] {n : ℕ} (hcard : q = (p^n)) : (frobenius K p^n) = 1 := by
  ext
  conv_rhs => rw [RingHom.one_def, RingHom.id_apply, ← pow_card x, hcard]
  clear hcard
  induction n
  ·
    simp
  rw [pow_succₓ, pow_succ'ₓ, pow_mulₓ, RingHom.mul_def, RingHom.comp_apply, frobenius_def, n_ih]

open Polynomial

theorem expand_card (f : Polynomial K) : expand K q f = (f^q) := by
  cases' CharP.exists K with p hp
  let this' := hp
  rcases FiniteField.card K p with ⟨⟨n, npos⟩, ⟨hp, hn⟩⟩
  have : Fact p.prime := ⟨hp⟩
  dsimp  at hn
  rw [hn, ← map_expand_pow_char, frobenius_pow hn, RingHom.one_def, map_id]

end FiniteField

namespace Zmod

open FiniteField Polynomial

theorem sq_add_sq (p : ℕ) [hp : Fact p.prime] (x : Zmod p) : ∃ a b : Zmod p, ((a^2)+b^2) = x := by
  cases' hp.1.eq_two_or_odd with hp2 hp_odd
  ·
    subst p
    change Finₓ 2 at x
    fin_cases x
    ·
      use 0
      simp
    ·
      use 0, 1
      simp
  let f : Polynomial (Zmod p) := X^2
  let g : Polynomial (Zmod p) := (X^2) - C x
  obtain ⟨a, b, hab⟩ : ∃ a b, (f.eval a+g.eval b) = 0 :=
    @exists_root_sum_quadratic _ _ _ _ f g (degree_X_pow 2)
      (degree_X_pow_sub_C
        (by
          decide)
        _)
      (by
        rw [Zmod.card, hp_odd])
  refine' ⟨a, b, _⟩
  rw [← sub_eq_zero]
  simpa only [eval_C, eval_X, eval_pow, eval_sub, ← add_sub_assoc] using hab

end Zmod

namespace CharP

theorem sq_add_sq (R : Type _) [CommRingₓ R] [IsDomain R] (p : ℕ) [Fact (0 < p)] [CharP R p] (x : ℤ) :
    ∃ a b : ℕ, ((a^2)+b^2 : R) = x := by
  have := char_is_prime_of_pos R p
  obtain ⟨a, b, hab⟩ := Zmod.sq_add_sq p x
  refine' ⟨a.val, b.val, _⟩
  simpa using congr_argₓ (Zmod.castHom dvd_rfl R) hab

end CharP

open_locale Nat

open Zmod

/--  The **Fermat-Euler totient theorem**. `nat.modeq.pow_totient` is an alternative statement
  of the same theorem. -/
@[simp]
theorem Zmod.pow_totient {n : ℕ} [Fact (0 < n)] (x : Units (Zmod n)) : (x^φ n) = 1 := by
  rw [← card_units_eq_totient, pow_card_eq_one]

/--  The **Fermat-Euler totient theorem**. `zmod.pow_totient` is an alternative statement
  of the same theorem. -/
theorem Nat.Modeq.pow_totient {x n : ℕ} (h : Nat.Coprime x n) : (x^φ n) ≡ 1 [MOD n] := by
  cases n
  ·
    simp
  rw [← Zmod.eq_iff_modeq_nat]
  let x' : Units (Zmod (n+1)) := Zmod.unitOfCoprime _ h
  have := Zmod.pow_totient x'
  apply_fun (coeₓ : Units (Zmod (n+1)) → Zmod (n+1))  at this
  simpa only [-Zmod.pow_totient, Nat.succ_eq_add_one, Nat.cast_pow, Units.coe_one, Nat.cast_one, coe_unit_of_coprime,
    Units.coe_pow]

section

variable {V : Type _} [Fintype K] [DivisionRing K] [AddCommGroupₓ V] [Module K V]

theorem card_eq_pow_finrank [Fintype V] : Fintype.card V = (q^FiniteDimensional.finrank K V) := by
  let b := IsNoetherian.finsetBasis K V
  rw [Module.card_fintype b, ← FiniteDimensional.finrank_eq_card_basis b]

end

open FiniteField

namespace Zmod

/--  A variation on Fermat's little theorem. See `zmod.pow_card_sub_one_eq_one` -/
@[simp]
theorem pow_card {p : ℕ} [Fact p.prime] (x : Zmod p) : (x^p) = x := by
  have h := FiniteField.pow_card x
  rwa [Zmod.card p] at h

@[simp]
theorem pow_card_pow {n p : ℕ} [Fact p.prime] (x : Zmod p) : (x^p^n) = x := by
  induction' n with n ih
  ·
    simp
  ·
    simp [pow_succₓ, pow_mulₓ, ih, pow_card]

@[simp]
theorem frobenius_zmod (p : ℕ) [Fact p.prime] : frobenius (Zmod p) p = RingHom.id _ := by
  ext a
  rw [frobenius_def, Zmod.pow_card, RingHom.id_apply]

@[simp]
theorem card_units (p : ℕ) [Fact p.prime] : Fintype.card (Units (Zmod p)) = p - 1 := by
  rw [Fintype.card_units, card]

/--  **Fermat's Little Theorem**: for every unit `a` of `zmod p`, we have `a ^ (p - 1) = 1`. -/
theorem units_pow_card_sub_one_eq_one (p : ℕ) [Fact p.prime] (a : Units (Zmod p)) : (a^p - 1) = 1 := by
  rw [← card_units p, pow_card_eq_one]

/--  **Fermat's Little Theorem**: for all nonzero `a : zmod p`, we have `a ^ (p - 1) = 1`. -/
theorem pow_card_sub_one_eq_one {p : ℕ} [Fact p.prime] {a : Zmod p} (ha : a ≠ 0) : (a^p - 1) = 1 := by
  have h := pow_card_sub_one_eq_one a ha
  rwa [Zmod.card p] at h

open Polynomial

theorem expand_card {p : ℕ} [Fact p.prime] (f : Polynomial (Zmod p)) : expand (Zmod p) p f = (f^p) := by
  have h := FiniteField.expand_card f
  rwa [Zmod.card p] at h

end Zmod

/--  **Fermat's Little Theorem**: for all `a : ℤ` coprime to `p`, we have
`a ^ (p - 1) ≡ 1 [ZMOD p]`. -/
theorem Int.Modeq.pow_card_sub_one_eq_one {p : ℕ} (hp : Nat.Prime p) {n : ℤ} (hpn : IsCoprime n p) :
    (n^p - 1) ≡ 1 [ZMOD p] := by
  have : Fact p.prime := ⟨hp⟩
  have : ¬(n : Zmod p) = 0 := by
    rw [CharP.int_cast_eq_zero_iff _ p, ← (nat.prime_iff_prime_int.mp hp).coprime_iff_not_dvd]
    ·
      exact hpn.symm
    exact Zmod.char_p p
  simpa [← Zmod.int_coe_eq_int_coe_iff] using Zmod.pow_card_sub_one_eq_one this

