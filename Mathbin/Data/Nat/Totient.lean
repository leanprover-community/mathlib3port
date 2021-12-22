import Mathbin.Algebra.BigOperators.Basic
import Mathbin.Data.Nat.Prime
import Mathbin.Data.Zmod.Basic

/-!
# Euler's totient function

This file defines [Euler's totient function](https://en.wikipedia.org/wiki/Euler's_totient_function)
`nat.totient n` which counts the number of naturals less than `n` that are coprime with `n`.
We prove the divisor sum formula, namely that `n` equals `φ` summed over the divisors of `n`. See
`sum_totient`. We also prove two lemmas to help compute totients, namely `totient_mul` and
`totient_prime_pow`.
-/


open Finset

open_locale BigOperators

namespace Nat

/--  Euler's totient function. This counts the number of naturals strictly less than `n` which are
coprime with `n`. -/
def totient (n : ℕ) : ℕ :=
  ((range n).filter (Nat.Coprime n)).card

localized [Nat] notation "φ" => Nat.totient

@[simp]
theorem totient_zero : φ 0 = 0 :=
  rfl

@[simp]
theorem totient_one : φ 1 = 1 := by
  simp [totient]

theorem totient_eq_card_coprime (n : ℕ) : φ n = ((range n).filter (Nat.Coprime n)).card :=
  rfl

theorem totient_le (n : ℕ) : φ n ≤ n :=
  calc totient n ≤ (range n).card := card_filter_le _ _
    _ = n := card_range _
    

theorem totient_lt (n : ℕ) (hn : 1 < n) : φ n < n :=
  calc totient n ≤ ((range n).filter (· ≠ 0)).card := by
    apply card_le_of_subset (monotone_filter_right _ _)
    intro n1 hn1 hn1'
    simpa only [hn1', coprime_zero_right, hn.ne'] using hn1
    _ = n - 1 := by
    simp only [filter_ne' (range n) 0, card_erase_of_mem, n.pred_eq_sub_one, card_range, pos_of_gt hn, mem_range]
    _ < n := Nat.sub_ltₓ (pos_of_gt hn) zero_lt_one
    

theorem totient_pos : ∀ {n : ℕ}, 0 < n → 0 < φ n
  | 0 => by
    decide
  | 1 => by
    simp [totient]
  | n+2 => fun h =>
    card_pos.2
      ⟨1,
        mem_filter.2
          ⟨mem_range.2
              (by
                decide),
            coprime_one_right _⟩⟩

open Zmod

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  [(Command.docComment
    "/--"
    " Note this takes an explicit `fintype (units (zmod n))` argument to avoid trouble with instance\ndiamonds. -/")]
  [(Term.attributes "@[" [(Term.attrInstance (Term.attrKind []) (Attr.simp "simp" [] []))] "]")]
  []
  []
  []
  [])
 (Command.theorem
  "theorem"
  (Command.declId `_root_.zmod.card_units_eq_totient [])
  (Command.declSig
   [(Term.explicitBinder "(" [`n] [":" (termℕ "ℕ")] [] ")")
    (Term.instBinder "[" [] (Term.app `Fact [(«term_<_» (numLit "0") "<" `n)]) "]")
    (Term.instBinder "[" [] (Term.app `Fintype [(Term.app `Units [(Term.app `Zmod [`n])])]) "]")]
   (Term.typeSpec
    ":"
    («term_=_»
     (Term.app `Fintype.card [(Term.app `Units [(Term.app `Zmod [`n])])])
     "="
     (Term.app (Nat.Data.Nat.Totient.termφ "φ") [`n]))))
  (Command.declValSimple
   ":="
   (calc
    "calc"
    [(calcStep
      («term_=_»
       (Term.app `Fintype.card [(Term.app `Units [(Term.app `Zmod [`n])])])
       "="
       (Term.app
        `Fintype.card
        [(«term{__:_//_}» "{" `x [":" (Term.app `Zmod [`n])] "//" (Term.app `x.val.coprime [`n]) "}")]))
      ":="
      (Term.app `Fintype.card_congr [`Zmod.unitsEquivCoprime]))
     (calcStep
      («term_=_» (Term.hole "_") "=" (Term.app (Nat.Data.Nat.Totient.termφ "φ") [`n]))
      ":="
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(group
           (Tactic.apply
            "apply"
            (Term.app
             `Finset.card_congr
             [(Term.fun
               "fun"
               (Term.basicFun
                [(Term.simpleBinder
                  [`a]
                  [(Term.typeSpec
                    ":"
                    («term{__:_//_}» "{" `x [":" (Term.app `Zmod [`n])] "//" (Term.app `x.val.coprime [`n]) "}"))])
                 (Term.simpleBinder [(Term.hole "_")] [])]
                "=>"
                (Term.proj (Term.proj `a "." (fieldIdx "1")) "." `val)))]))
           [])
          (group
           (Tactic.«tactic·._»
            "·"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(group (Tactic.intro "intro" [`a]) [])
               (group
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
                    (Term.proj (Term.paren "(" [`a [(Term.typeAscription ":" (Term.app `Zmod [`n]))]] ")") "." `val_lt))
                   ","
                   (Tactic.simpLemma [] [] `a.prop.symm)]
                  "]"]
                 [])
                [])])))
           [])
          (group
           (Tactic.«tactic·._»
            "·"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(group (Tactic.intro "intro" [(Term.hole "_") (Term.hole "_") (Term.hole "_") (Term.hole "_") `h]) [])
               (group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Subtype.ext_iff_val)] "]") []) [])
               (group (Tactic.apply "apply" `val_injective) [])
               (group (Tactic.exact "exact" `h) [])])))
           [])
          (group
           (Tactic.«tactic·._»
            "·"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(group (Tactic.intro "intro" [`b `hb]) [])
               (group
                (Tactic.rwSeq
                 "rw"
                 []
                 (Tactic.rwRuleSeq
                  "["
                  [(Tactic.rwRule [] `Finset.mem_filter) "," (Tactic.rwRule [] `Finset.mem_range)]
                  "]")
                 [(Tactic.location "at" (Tactic.locationHyp [`hb] []))])
                [])
               (group
                (Tactic.refine'
                 "refine'"
                 (Term.anonymousCtor
                  "⟨"
                  [(Term.anonymousCtor "⟨" [`b "," (Term.hole "_")] "⟩")
                   ","
                   (Term.app `Finset.mem_univ [(Term.hole "_")])
                   ","
                   (Term.hole "_")]
                  "⟩"))
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
                       (Term.letIdDecl
                        `u
                        []
                        ":="
                        (Term.app `unit_of_coprime [`b (Term.proj (Term.proj `hb "." (fieldIdx "2")) "." `symm)]))))
                     [])
                    (group (Tactic.exact "exact" (Term.app `val_coe_unit_coprime [`u])) [])])))
                [])
               (group
                (Tactic.«tactic·._»
                 "·"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(group
                     (Tactic.tacticShow_
                      "show"
                      («term_=_»
                       (Term.app
                        `Zmod.val
                        [(Term.paren "(" [`b [(Term.typeAscription ":" (Term.app `Zmod [`n]))]] ")")])
                       "="
                       `b))
                     [])
                    (group
                     (Tactic.rwSeq
                      "rw"
                      []
                      (Tactic.rwRuleSeq
                       "["
                       [(Tactic.rwRule [] `val_nat_cast)
                        ","
                        (Tactic.rwRule [] (Term.app `Nat.mod_eq_of_ltₓ [(Term.proj `hb "." (fieldIdx "1"))]))]
                       "]")
                      [])
                     [])])))
                [])])))
           [])]))))])
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
  (calc
   "calc"
   [(calcStep
     («term_=_»
      (Term.app `Fintype.card [(Term.app `Units [(Term.app `Zmod [`n])])])
      "="
      (Term.app
       `Fintype.card
       [(«term{__:_//_}» "{" `x [":" (Term.app `Zmod [`n])] "//" (Term.app `x.val.coprime [`n]) "}")]))
     ":="
     (Term.app `Fintype.card_congr [`Zmod.unitsEquivCoprime]))
    (calcStep
     («term_=_» (Term.hole "_") "=" (Term.app (Nat.Data.Nat.Totient.termφ "φ") [`n]))
     ":="
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(group
          (Tactic.apply
           "apply"
           (Term.app
            `Finset.card_congr
            [(Term.fun
              "fun"
              (Term.basicFun
               [(Term.simpleBinder
                 [`a]
                 [(Term.typeSpec
                   ":"
                   («term{__:_//_}» "{" `x [":" (Term.app `Zmod [`n])] "//" (Term.app `x.val.coprime [`n]) "}"))])
                (Term.simpleBinder [(Term.hole "_")] [])]
               "=>"
               (Term.proj (Term.proj `a "." (fieldIdx "1")) "." `val)))]))
          [])
         (group
          (Tactic.«tactic·._»
           "·"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group (Tactic.intro "intro" [`a]) [])
              (group
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
                   (Term.proj (Term.paren "(" [`a [(Term.typeAscription ":" (Term.app `Zmod [`n]))]] ")") "." `val_lt))
                  ","
                  (Tactic.simpLemma [] [] `a.prop.symm)]
                 "]"]
                [])
               [])])))
          [])
         (group
          (Tactic.«tactic·._»
           "·"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group (Tactic.intro "intro" [(Term.hole "_") (Term.hole "_") (Term.hole "_") (Term.hole "_") `h]) [])
              (group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Subtype.ext_iff_val)] "]") []) [])
              (group (Tactic.apply "apply" `val_injective) [])
              (group (Tactic.exact "exact" `h) [])])))
          [])
         (group
          (Tactic.«tactic·._»
           "·"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group (Tactic.intro "intro" [`b `hb]) [])
              (group
               (Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule [] `Finset.mem_filter) "," (Tactic.rwRule [] `Finset.mem_range)]
                 "]")
                [(Tactic.location "at" (Tactic.locationHyp [`hb] []))])
               [])
              (group
               (Tactic.refine'
                "refine'"
                (Term.anonymousCtor
                 "⟨"
                 [(Term.anonymousCtor "⟨" [`b "," (Term.hole "_")] "⟩")
                  ","
                  (Term.app `Finset.mem_univ [(Term.hole "_")])
                  ","
                  (Term.hole "_")]
                 "⟩"))
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
                      (Term.letIdDecl
                       `u
                       []
                       ":="
                       (Term.app `unit_of_coprime [`b (Term.proj (Term.proj `hb "." (fieldIdx "2")) "." `symm)]))))
                    [])
                   (group (Tactic.exact "exact" (Term.app `val_coe_unit_coprime [`u])) [])])))
               [])
              (group
               (Tactic.«tactic·._»
                "·"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(group
                    (Tactic.tacticShow_
                     "show"
                     («term_=_»
                      (Term.app `Zmod.val [(Term.paren "(" [`b [(Term.typeAscription ":" (Term.app `Zmod [`n]))]] ")")])
                      "="
                      `b))
                    [])
                   (group
                    (Tactic.rwSeq
                     "rw"
                     []
                     (Tactic.rwRuleSeq
                      "["
                      [(Tactic.rwRule [] `val_nat_cast)
                       ","
                       (Tactic.rwRule [] (Term.app `Nat.mod_eq_of_ltₓ [(Term.proj `hb "." (fieldIdx "1"))]))]
                      "]")
                     [])
                    [])])))
               [])])))
          [])]))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'calc', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'calcStep', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.apply
        "apply"
        (Term.app
         `Finset.card_congr
         [(Term.fun
           "fun"
           (Term.basicFun
            [(Term.simpleBinder
              [`a]
              [(Term.typeSpec
                ":"
                («term{__:_//_}» "{" `x [":" (Term.app `Zmod [`n])] "//" (Term.app `x.val.coprime [`n]) "}"))])
             (Term.simpleBinder [(Term.hole "_")] [])]
            "=>"
            (Term.proj (Term.proj `a "." (fieldIdx "1")) "." `val)))]))
       [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group (Tactic.intro "intro" [`a]) [])
           (group
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
                (Term.proj (Term.paren "(" [`a [(Term.typeAscription ":" (Term.app `Zmod [`n]))]] ")") "." `val_lt))
               ","
               (Tactic.simpLemma [] [] `a.prop.symm)]
              "]"]
             [])
            [])])))
       [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group (Tactic.intro "intro" [(Term.hole "_") (Term.hole "_") (Term.hole "_") (Term.hole "_") `h]) [])
           (group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Subtype.ext_iff_val)] "]") []) [])
           (group (Tactic.apply "apply" `val_injective) [])
           (group (Tactic.exact "exact" `h) [])])))
       [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group (Tactic.intro "intro" [`b `hb]) [])
           (group
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Finset.mem_filter) "," (Tactic.rwRule [] `Finset.mem_range)] "]")
             [(Tactic.location "at" (Tactic.locationHyp [`hb] []))])
            [])
           (group
            (Tactic.refine'
             "refine'"
             (Term.anonymousCtor
              "⟨"
              [(Term.anonymousCtor "⟨" [`b "," (Term.hole "_")] "⟩")
               ","
               (Term.app `Finset.mem_univ [(Term.hole "_")])
               ","
               (Term.hole "_")]
              "⟩"))
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
                   (Term.letIdDecl
                    `u
                    []
                    ":="
                    (Term.app `unit_of_coprime [`b (Term.proj (Term.proj `hb "." (fieldIdx "2")) "." `symm)]))))
                 [])
                (group (Tactic.exact "exact" (Term.app `val_coe_unit_coprime [`u])) [])])))
            [])
           (group
            (Tactic.«tactic·._»
             "·"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(group
                 (Tactic.tacticShow_
                  "show"
                  («term_=_»
                   (Term.app `Zmod.val [(Term.paren "(" [`b [(Term.typeAscription ":" (Term.app `Zmod [`n]))]] ")")])
                   "="
                   `b))
                 [])
                (group
                 (Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule [] `val_nat_cast)
                    ","
                    (Tactic.rwRule [] (Term.app `Nat.mod_eq_of_ltₓ [(Term.proj `hb "." (fieldIdx "1"))]))]
                   "]")
                  [])
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
     [(group (Tactic.intro "intro" [`b `hb]) [])
      (group
       (Tactic.rwSeq
        "rw"
        []
        (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Finset.mem_filter) "," (Tactic.rwRule [] `Finset.mem_range)] "]")
        [(Tactic.location "at" (Tactic.locationHyp [`hb] []))])
       [])
      (group
       (Tactic.refine'
        "refine'"
        (Term.anonymousCtor
         "⟨"
         [(Term.anonymousCtor "⟨" [`b "," (Term.hole "_")] "⟩")
          ","
          (Term.app `Finset.mem_univ [(Term.hole "_")])
          ","
          (Term.hole "_")]
         "⟩"))
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
              (Term.letIdDecl
               `u
               []
               ":="
               (Term.app `unit_of_coprime [`b (Term.proj (Term.proj `hb "." (fieldIdx "2")) "." `symm)]))))
            [])
           (group (Tactic.exact "exact" (Term.app `val_coe_unit_coprime [`u])) [])])))
       [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group
            (Tactic.tacticShow_
             "show"
             («term_=_»
              (Term.app `Zmod.val [(Term.paren "(" [`b [(Term.typeAscription ":" (Term.app `Zmod [`n]))]] ")")])
              "="
              `b))
            [])
           (group
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] `val_nat_cast)
               ","
               (Tactic.rwRule [] (Term.app `Nat.mod_eq_of_ltₓ [(Term.proj `hb "." (fieldIdx "1"))]))]
              "]")
             [])
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
     [(group
       (Tactic.tacticShow_
        "show"
        («term_=_»
         (Term.app `Zmod.val [(Term.paren "(" [`b [(Term.typeAscription ":" (Term.app `Zmod [`n]))]] ")")])
         "="
         `b))
       [])
      (group
       (Tactic.rwSeq
        "rw"
        []
        (Tactic.rwRuleSeq
         "["
         [(Tactic.rwRule [] `val_nat_cast)
          ","
          (Tactic.rwRule [] (Term.app `Nat.mod_eq_of_ltₓ [(Term.proj `hb "." (fieldIdx "1"))]))]
         "]")
        [])
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.«tactic·._»', expected 'antiquot'
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
    [(Tactic.rwRule [] `val_nat_cast)
     ","
     (Tactic.rwRule [] (Term.app `Nat.mod_eq_of_ltₓ [(Term.proj `hb "." (fieldIdx "1"))]))]
    "]")
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwSeq', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Nat.mod_eq_of_ltₓ [(Term.proj `hb "." (fieldIdx "1"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.proj `hb "." (fieldIdx "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `hb
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Nat.mod_eq_of_ltₓ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `val_nat_cast
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.tacticShow_
   "show"
   («term_=_»
    (Term.app `Zmod.val [(Term.paren "(" [`b [(Term.typeAscription ":" (Term.app `Zmod [`n]))]] ")")])
    "="
    `b))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticShow_', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_=_» (Term.app `Zmod.val [(Term.paren "(" [`b [(Term.typeAscription ":" (Term.app `Zmod [`n]))]] ")")]) "=" `b)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `b
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Term.app `Zmod.val [(Term.paren "(" [`b [(Term.typeAscription ":" (Term.app `Zmod [`n]))]] ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.paren "(" [`b [(Term.typeAscription ":" (Term.app `Zmod [`n]))]] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.paren.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.typeAscription.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Zmod [`n])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Zmod
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  `b
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Zmod.val
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.«tactic·._»
   "·"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.tacticLet_
        "let"
        (Term.letDecl
         (Term.letIdDecl
          `u
          []
          ":="
          (Term.app `unit_of_coprime [`b (Term.proj (Term.proj `hb "." (fieldIdx "2")) "." `symm)]))))
       [])
      (group (Tactic.exact "exact" (Term.app `val_coe_unit_coprime [`u])) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.«tactic·._»', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.exact "exact" (Term.app `val_coe_unit_coprime [`u]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.exact', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `val_coe_unit_coprime [`u])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `u
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `val_coe_unit_coprime
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.tacticLet_
   "let"
   (Term.letDecl
    (Term.letIdDecl
     `u
     []
     ":="
     (Term.app `unit_of_coprime [`b (Term.proj (Term.proj `hb "." (fieldIdx "2")) "." `symm)]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticLet_', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letDecl', expected 'Lean.Parser.Term.letDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letIdDecl', expected 'Lean.Parser.Term.letIdDecl.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `unit_of_coprime [`b (Term.proj (Term.proj `hb "." (fieldIdx "2")) "." `symm)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.proj (Term.proj `hb "." (fieldIdx "2")) "." `symm)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.proj `hb "." (fieldIdx "2"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `hb
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `b
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `unit_of_coprime
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.refine'
   "refine'"
   (Term.anonymousCtor
    "⟨"
    [(Term.anonymousCtor "⟨" [`b "," (Term.hole "_")] "⟩")
     ","
     (Term.app `Finset.mem_univ [(Term.hole "_")])
     ","
     (Term.hole "_")]
    "⟩"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.refine'', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor
   "⟨"
   [(Term.anonymousCtor "⟨" [`b "," (Term.hole "_")] "⟩")
    ","
    (Term.app `Finset.mem_univ [(Term.hole "_")])
    ","
    (Term.hole "_")]
   "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Finset.mem_univ [(Term.hole "_")])
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
  `Finset.mem_univ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor "⟨" [`b "," (Term.hole "_")] "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `b
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.rwSeq
   "rw"
   []
   (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Finset.mem_filter) "," (Tactic.rwRule [] `Finset.mem_range)] "]")
   [(Tactic.location "at" (Tactic.locationHyp [`hb] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwSeq', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.location', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hb
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Finset.mem_range
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Finset.mem_filter
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.intro "intro" [`b `hb])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.intro', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hb
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `b
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.«tactic·._»
   "·"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group (Tactic.intro "intro" [(Term.hole "_") (Term.hole "_") (Term.hole "_") (Term.hole "_") `h]) [])
      (group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Subtype.ext_iff_val)] "]") []) [])
      (group (Tactic.apply "apply" `val_injective) [])
      (group (Tactic.exact "exact" `h) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.«tactic·._»', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.exact "exact" `h)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.exact', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `h
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.apply "apply" `val_injective)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.apply', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `val_injective
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Subtype.ext_iff_val)] "]") [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwSeq', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Subtype.ext_iff_val
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.intro "intro" [(Term.hole "_") (Term.hole "_") (Term.hole "_") (Term.hole "_") `h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.intro', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `h
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.«tactic·._»
   "·"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group (Tactic.intro "intro" [`a]) [])
      (group
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
           (Term.proj (Term.paren "(" [`a [(Term.typeAscription ":" (Term.app `Zmod [`n]))]] ")") "." `val_lt))
          ","
          (Tactic.simpLemma [] [] `a.prop.symm)]
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
      (Term.proj (Term.paren "(" [`a [(Term.typeAscription ":" (Term.app `Zmod [`n]))]] ")") "." `val_lt))
     ","
     (Tactic.simpLemma [] [] `a.prop.symm)]
    "]"]
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `a.prop.symm
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.proj (Term.paren "(" [`a [(Term.typeAscription ":" (Term.app `Zmod [`n]))]] ")") "." `val_lt)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.paren "(" [`a [(Term.typeAscription ":" (Term.app `Zmod [`n]))]] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.paren.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.typeAscription.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Zmod [`n])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Zmod
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  `a
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«)»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«)»', expected 'Lean.Parser.Tactic.discharger'
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
      Note this takes an explicit `fintype (units (zmod n))` argument to avoid trouble with instance
      diamonds. -/
    @[ simp ]
  theorem
    _root_.zmod.card_units_eq_totient
    ( n : ℕ ) [ Fact 0 < n ] [ Fintype Units Zmod n ] : Fintype.card Units Zmod n = φ n
    :=
      calc
        Fintype.card Units Zmod n = Fintype.card { x : Zmod n // x.val.coprime n }
            :=
            Fintype.card_congr Zmod.unitsEquivCoprime
          _ = φ n
            :=
            by
              apply Finset.card_congr fun a : { x : Zmod n // x.val.coprime n } _ => a . 1 . val
                ·
                  intro a
                    simp
                      ( config := { contextual := Bool.true._@._internal._hyg.0 } )
                      [ ( a : Zmod n ) . val_lt , a.prop.symm ]
                · intro _ _ _ _ h rw [ Subtype.ext_iff_val ] apply val_injective exact h
                ·
                  intro b hb
                    rw [ Finset.mem_filter , Finset.mem_range ] at hb
                    refine' ⟨ ⟨ b , _ ⟩ , Finset.mem_univ _ , _ ⟩
                    · let u := unit_of_coprime b hb . 2 . symm exact val_coe_unit_coprime u
                    · show Zmod.val ( b : Zmod n ) = b rw [ val_nat_cast , Nat.mod_eq_of_ltₓ hb . 1 ]

theorem totient_mul {m n : ℕ} (h : m.coprime n) : φ (m*n) = φ m*φ n :=
  if hmn0 : (m*n) = 0 then by
    cases' Nat.mul_eq_zero.1 hmn0 with h h <;> simp only [totient_zero, mul_zero, zero_mul, h]
  else by
    have : Fact (0 < m*n) := ⟨Nat.pos_of_ne_zeroₓ hmn0⟩
    have : Fact (0 < m) := ⟨Nat.pos_of_ne_zeroₓ $ left_ne_zero_of_mul hmn0⟩
    have : Fact (0 < n) := ⟨Nat.pos_of_ne_zeroₓ $ right_ne_zero_of_mul hmn0⟩
    rw [← Zmod.card_units_eq_totient, ← Zmod.card_units_eq_totient, ← Zmod.card_units_eq_totient,
      Fintype.card_congr (Units.mapEquiv (Zmod.chineseRemainder h).toMulEquiv).toEquiv,
      Fintype.card_congr (@MulEquiv.prodUnits (Zmod m) (Zmod n) _ _).toEquiv, Fintype.card_prod]

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [] [] [] [] [] [])
 (Command.theorem
  "theorem"
  (Command.declId `sum_totient [])
  (Command.declSig
   [(Term.explicitBinder "(" [`n] [":" (termℕ "ℕ")] [] ")")]
   (Term.typeSpec
    ":"
    («term_=_»
     (Algebra.BigOperators.Basic.«term∑_in_,_»
      "∑"
      (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `m)] []))
      " in "
      (Term.app (Term.proj (Term.app `range [`n.succ]) "." `filter) [(Init.Core.«term_∣_» (Term.cdot "·") " ∣ " `n)])
      ", "
      (Term.app (Nat.Data.Nat.Totient.termφ "φ") [`m]))
     "="
     `n)))
  (Command.declValSimple
   ":="
   (termDepIfThenElse
    "if"
    `hn0
    ":"
    («term_=_» `n "=" (numLit "0"))
    "then"
    (Term.byTactic
     "by"
     (Tactic.tacticSeq
      (Tactic.tacticSeq1Indented [(group (Tactic.simp "simp" [] [] ["[" [(Tactic.simpLemma [] [] `hn0)] "]"] []) [])])))
    "else"
    (calc
     "calc"
     [(calcStep
       («term_=_»
        (Algebra.BigOperators.Basic.«term∑_in_,_»
         "∑"
         (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `m)] []))
         " in "
         (Term.app (Term.proj (Term.app `range [`n.succ]) "." `filter) [(Init.Core.«term_∣_» (Term.cdot "·") " ∣ " `n)])
         ", "
         (Term.app (Nat.Data.Nat.Totient.termφ "φ") [`m]))
        "="
        (Algebra.BigOperators.Basic.«term∑_in_,_»
         "∑"
         (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `d)] []))
         " in "
         (Term.app (Term.proj (Term.app `range [`n.succ]) "." `filter) [(Init.Core.«term_∣_» (Term.cdot "·") " ∣ " `n)])
         ", "
         (Term.proj
          (Term.app
           (Term.proj (Term.app `range [(«term_/_» `n "/" `d)]) "." `filter)
           [(Term.fun
             "fun"
             (Term.basicFun
              [(Term.simpleBinder [`m] [])]
              "=>"
              («term_=_» (Term.app `gcd [(«term_/_» `n "/" `d) `m]) "=" (numLit "1"))))])
          "."
          `card)))
       ":="
       («term_$__»
        `Eq.symm
        "$"
        (Term.app
         `sum_bij
         [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`d (Term.hole "_")] [])] "=>" («term_/_» `n "/" `d)))
          (Term.fun
           "fun"
           (Term.basicFun
            [(Term.simpleBinder [`d `hd] [])]
            "=>"
            (Term.app
             (Term.proj `mem_filter "." (fieldIdx "2"))
             [(Term.anonymousCtor
               "⟨"
               [(«term_$__»
                 (Term.proj `mem_range "." (fieldIdx "2"))
                 "$"
                 («term_$__» `lt_succ_of_le "$" (Term.app `Nat.div_le_selfₓ [(Term.hole "_") (Term.hole "_")])))
                ","
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(group
                     (Tactic.«tactic_<;>_»
                      (Tactic.Conv.conv
                       "conv"
                       []
                       []
                       "=>"
                       (Tactic.Conv.convSeq
                        (Tactic.Conv.convSeq1Indented
                         [(group (Tactic.Conv.rhs "rhs") [])
                          (group
                           (Tactic.Conv.convRw__
                            "rw"
                            []
                            (Tactic.rwRuleSeq
                             "["
                             [(Tactic.rwRule
                               ["←"]
                               (Term.app
                                `Nat.mul_div_cancel'ₓ
                                [(Term.proj
                                  (Term.app (Term.proj `mem_filter "." (fieldIdx "1")) [`hd])
                                  "."
                                  (fieldIdx "2"))]))]
                             "]"))
                           [])])))
                      "<;>"
                      (Tactic.simp "simp" [] [] [] []))
                     [])])))]
               "⟩")])))
          (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [(Term.hole "_") (Term.hole "_")] [])] "=>" `rfl))
          (Term.fun
           "fun"
           (Term.basicFun
            [(Term.simpleBinder [`a `b `ha `hb `h] [])]
            "=>"
            (Term.have
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               [`ha []]
               [(Term.typeSpec ":" («term_=_» (Finset.Data.Finset.Fold.«term_*_» `a "*" («term_/_» `n "/" `a)) "=" `n))]
               ":="
               (Term.app
                `Nat.mul_div_cancel'ₓ
                [(Term.proj (Term.app (Term.proj `mem_filter "." (fieldIdx "1")) [`ha]) "." (fieldIdx "2"))])))
             []
             (Term.have
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                []
                [(Term.typeSpec ":" («term_<_» (numLit "0") "<" («term_/_» `n "/" `a)))]
                ":="
                (Term.app
                 `Nat.pos_of_ne_zeroₓ
                 [(Term.fun
                   "fun"
                   (Term.basicFun
                    [(Term.simpleBinder [`h] [])]
                    "=>"
                    (Term.byTactic
                     "by"
                     (Tactic.tacticSeq
                      (Tactic.tacticSeq1Indented
                       [(group
                         (Tactic.simpAll "simp_all" [] [] ["[" [(Tactic.simpLemma [] [] `lt_irreflₓ)] "]"])
                         [])])))))])))
              []
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
                     [(Tactic.rwRule ["←"] (Term.app `Nat.mul_left_inj [`this]))
                      ","
                      (Tactic.rwRule [] `ha)
                      ","
                      (Tactic.rwRule [] `h)
                      ","
                      (Tactic.rwRule
                       []
                       (Term.app
                        `Nat.mul_div_cancel'ₓ
                        [(Term.proj (Term.app (Term.proj `mem_filter "." (fieldIdx "1")) [`hb]) "." (fieldIdx "2"))]))]
                     "]")
                    [])
                   [])])))))))
          (Term.fun
           "fun"
           (Term.basicFun
            [(Term.simpleBinder [`b `hb] [])]
            "=>"
            (Term.have
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               [`hb []]
               [(Term.typeSpec ":" («term_∧_» («term_<_» `b "<" `n.succ) "∧" (Init.Core.«term_∣_» `b " ∣ " `n)))]
               ":="
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(group
                    (Tactic.simpa "simpa" [] [] ["[" [(Tactic.simpErase "-" `range_succ)] "]"] [] ["using" `hb])
                    [])])))))
             []
             (Term.have
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                [`hbn []]
                [(Term.typeSpec ":" (Init.Core.«term_∣_» («term_/_» `n "/" `b) " ∣ " `n))]
                ":="
                (Term.anonymousCtor
                 "⟨"
                 [`b
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
                         [(Tactic.rwRule [] (Term.app `Nat.div_mul_cancelₓ [(Term.proj `hb "." (fieldIdx "2"))]))]
                         "]")
                        [])
                       [])])))]
                 "⟩")))
              []
              (Term.have
               "have"
               (Term.haveDecl
                (Term.haveIdDecl
                 [`hnb0 []]
                 [(Term.typeSpec ":" («term_≠_» («term_/_» `n "/" `b) "≠" (numLit "0")))]
                 ":="
                 (Term.fun
                  "fun"
                  (Term.basicFun
                   [(Term.simpleBinder [`h] [])]
                   "=>"
                   (Term.byTactic
                    "by"
                    (Tactic.tacticSeq
                     (Tactic.tacticSeq1Indented
                      [(group
                        (Tactic.simpa
                         "simpa"
                         []
                         []
                         ["[" [(Tactic.simpLemma [] [] `h) "," (Tactic.simpLemma [] [] (Term.app `Ne.symm [`hn0]))] "]"]
                         []
                         ["using" (Term.app `Nat.div_mul_cancelₓ [`hbn])])
                        [])])))))))
               []
               (Term.anonymousCtor
                "⟨"
                [(«term_/_» `n "/" `b)
                 ","
                 (Term.app
                  (Term.proj `mem_filter "." (fieldIdx "2"))
                  [(Term.anonymousCtor
                    "⟨"
                    [(«term_$__»
                      (Term.proj `mem_range "." (fieldIdx "2"))
                      "$"
                      («term_$__» `lt_succ_of_le "$" (Term.app `Nat.div_le_selfₓ [(Term.hole "_") (Term.hole "_")])))
                     ","
                     `hbn]
                    "⟩")])
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
                        [(Tactic.rwRule ["←"] (Term.app `Nat.mul_left_inj [(Term.app `Nat.pos_of_ne_zeroₓ [`hnb0])]))
                         ","
                         (Tactic.rwRule [] (Term.app `Nat.mul_div_cancel'ₓ [(Term.proj `hb "." (fieldIdx "2"))]))
                         ","
                         (Tactic.rwRule [] (Term.app `Nat.div_mul_cancelₓ [`hbn]))]
                        "]")
                       [])
                      [])])))]
                "⟩"))))))])))
      (calcStep
       («term_=_»
        (Term.hole "_")
        "="
        (Algebra.BigOperators.Basic.«term∑_in_,_»
         "∑"
         (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `d)] []))
         " in "
         (Term.app (Term.proj (Term.app `range [`n.succ]) "." `filter) [(Init.Core.«term_∣_» (Term.cdot "·") " ∣ " `n)])
         ", "
         (Term.proj
          (Term.app
           (Term.proj (Term.app `range [`n]) "." `filter)
           [(Term.fun
             "fun"
             (Term.basicFun [(Term.simpleBinder [`m] [])] "=>" («term_=_» (Term.app `gcd [`n `m]) "=" `d)))])
          "."
          `card)))
       ":="
       (Term.app
        `sum_congr
        [`rfl
         (Term.fun
          "fun"
          (Term.basicFun
           [(Term.simpleBinder [`d `hd] [])]
           "=>"
           (Term.have
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`hd []]
              [(Term.typeSpec ":" (Init.Core.«term_∣_» `d " ∣ " `n))]
              ":="
              (Term.proj (Term.app (Term.proj `mem_filter "." (fieldIdx "1")) [`hd]) "." (fieldIdx "2"))))
            []
            (Term.have
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               [`hd0 []]
               [(Term.typeSpec ":" («term_<_» (numLit "0") "<" `d))]
               ":="
               (Term.app
                `Nat.pos_of_ne_zeroₓ
                [(Term.fun
                  "fun"
                  (Term.basicFun
                   [(Term.simpleBinder [`h] [])]
                   "=>"
                   (Term.app `hn0 [(«term_$__» `eq_zero_of_zero_dvd "$" (Term.subst `h "▸" [`hd]))])))])))
             []
             (Term.app
              `card_congr
              [(Term.fun
                "fun"
                (Term.basicFun [(Term.simpleBinder [`m `hm] [])] "=>" (Finset.Data.Finset.Fold.«term_*_» `d "*" `m)))
               (Term.fun
                "fun"
                (Term.basicFun
                 [(Term.simpleBinder [`m `hm] [])]
                 "=>"
                 (Term.have
                  "have"
                  (Term.haveDecl
                   (Term.haveIdDecl
                    [`hm []]
                    [(Term.typeSpec
                      ":"
                      («term_∧_»
                       («term_<_» `m "<" («term_/_» `n "/" `d))
                       "∧"
                       («term_=_» (Term.app `gcd [(«term_/_» `n "/" `d) `m]) "=" (numLit "1"))))]
                    ":="
                    (Term.byTactic
                     "by"
                     (Tactic.tacticSeq
                      (Tactic.tacticSeq1Indented [(group (Tactic.simpa "simpa" [] [] [] [] ["using" `hm]) [])])))))
                  []
                  (Term.app
                   (Term.proj `mem_filter "." (fieldIdx "2"))
                   [(Term.anonymousCtor
                     "⟨"
                     [(«term_$__»
                       (Term.proj `mem_range "." (fieldIdx "2"))
                       "$"
                       (Term.subst
                        (Term.app `Nat.mul_div_cancel'ₓ [`hd])
                        "▸"
                        [(Term.app
                          (Term.proj (Term.app `mul_lt_mul_left [`hd0]) "." (fieldIdx "2"))
                          [(Term.proj `hm "." (fieldIdx "1"))])]))
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
                             [(Tactic.rwRule ["←"] (Term.app `Nat.mul_div_cancel'ₓ [`hd]))
                              ","
                              (Tactic.rwRule [] `gcd_mul_left)
                              ","
                              (Tactic.rwRule [] (Term.proj `hm "." (fieldIdx "2")))
                              ","
                              (Tactic.rwRule [] `mul_oneₓ)]
                             "]")
                            [])
                           [])])))]
                     "⟩")]))))
               (Term.fun
                "fun"
                (Term.basicFun
                 [(Term.simpleBinder [`a `b `ha `hb `h] [])]
                 "=>"
                 (Term.app (Term.proj (Term.app `Nat.mul_right_inj [`hd0]) "." (fieldIdx "1")) [`h])))
               (Term.fun
                "fun"
                (Term.basicFun
                 [(Term.simpleBinder [`b `hb] [])]
                 "=>"
                 (Term.have
                  "have"
                  (Term.haveDecl
                   (Term.haveIdDecl
                    [`hb []]
                    [(Term.typeSpec
                      ":"
                      («term_∧_» («term_<_» `b "<" `n) "∧" («term_=_» (Term.app `gcd [`n `b]) "=" `d)))]
                    ":="
                    (Term.byTactic
                     "by"
                     (Tactic.tacticSeq
                      (Tactic.tacticSeq1Indented [(group (Tactic.simpa "simpa" [] [] [] [] ["using" `hb]) [])])))))
                  []
                  (Term.anonymousCtor
                   "⟨"
                   [(«term_/_» `b "/" `d)
                    ","
                    (Term.app
                     (Term.proj `mem_filter "." (fieldIdx "2"))
                     [(Term.anonymousCtor
                       "⟨"
                       [(Term.app
                         (Term.proj `mem_range "." (fieldIdx "2"))
                         [(Term.app
                           (Term.proj
                            (Term.app
                             `mul_lt_mul_left
                             [(Term.show
                               "show"
                               («term_<_» (numLit "0") "<" `d)
                               (Term.fromTerm
                                "from"
                                (Term.subst
                                 (Term.proj `hb "." (fieldIdx "2"))
                                 "▸"
                                 [(Term.subst (Term.proj (Term.proj `hb "." (fieldIdx "2")) "." `symm) "▸" [`hd0])])))])
                            "."
                            (fieldIdx "1"))
                           [(Term.byTactic
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
                                    [(Tactic.rwRule ["←"] (Term.proj `hb "." (fieldIdx "2")))
                                     ","
                                     (Tactic.rwRule
                                      []
                                      (Term.app
                                       `Nat.mul_div_cancel'ₓ
                                       [(Term.app `gcd_dvd_left [(Term.hole "_") (Term.hole "_")])]))
                                     ","
                                     (Tactic.rwRule
                                      []
                                      (Term.app
                                       `Nat.mul_div_cancel'ₓ
                                       [(Term.app `gcd_dvd_right [(Term.hole "_") (Term.hole "_")])]))]
                                    "]")
                                   [])
                                  "<;>"
                                  (Tactic.exact "exact" (Term.proj `hb "." (fieldIdx "1"))))
                                 [])])))])])
                        ","
                        (Term.subst
                         (Term.proj `hb "." (fieldIdx "2"))
                         "▸"
                         [(Term.app
                           `coprime_div_gcd_div_gcd
                           [(Term.subst (Term.proj (Term.proj `hb "." (fieldIdx "2")) "." `symm) "▸" [`hd0])])])]
                       "⟩")])
                    ","
                    (Term.subst
                     (Term.proj `hb "." (fieldIdx "2"))
                     "▸"
                     [(Term.app `Nat.mul_div_cancel'ₓ [(Term.app `gcd_dvd_right [(Term.hole "_") (Term.hole "_")])])])]
                   "⟩"))))])))))]))
      (calcStep
       («term_=_»
        (Term.hole "_")
        "="
        (Term.proj
         (Term.app
          (Term.proj
           (Term.app `filter [(Init.Core.«term_∣_» (Term.cdot "·") " ∣ " `n) (Term.app `range [`n.succ])])
           "."
           `bUnion)
          [(Term.fun
            "fun"
            (Term.basicFun
             [(Term.simpleBinder [`d] [])]
             "=>"
             (Term.app
              (Term.proj (Term.app `range [`n]) "." `filter)
              [(Term.fun
                "fun"
                (Term.basicFun [(Term.simpleBinder [`m] [])] "=>" («term_=_» (Term.app `gcd [`n `m]) "=" `d)))])))])
         "."
         `card))
       ":="
       (Term.proj
        (Term.app
         `card_bUnion
         [(Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group
               (Tactic.«tactic_<;>_»
                (Tactic.intros "intros" [])
                "<;>"
                (Tactic.«tactic_<;>_»
                 (Tactic.apply "apply" (Term.proj `disjoint_filter "." (fieldIdx "2")))
                 "<;>"
                 (Tactic.cc "cc")))
               [])])))])
        "."
        `symm))
      (calcStep
       («term_=_» (Term.hole "_") "=" (Term.proj (Term.app `range [`n]) "." `card))
       ":="
       (Term.app
        `congr_argₓ
        [`card
         (Term.app
          `Finset.ext
          [(Term.fun
            "fun"
            (Term.basicFun
             [(Term.simpleBinder [`m] [])]
             "=>"
             (Term.anonymousCtor
              "⟨"
              [(Term.byTactic
                "by"
                (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.finish "finish" [] [] []) [])])))
               ","
               (Term.fun
                "fun"
                (Term.basicFun
                 [(Term.simpleBinder [`hm] [])]
                 "=>"
                 (Term.have
                  "have"
                  (Term.haveDecl
                   (Term.haveIdDecl
                    [`h []]
                    [(Term.typeSpec ":" («term_<_» `m "<" `n))]
                    ":="
                    (Term.app (Term.proj `mem_range "." (fieldIdx "1")) [`hm])))
                  []
                  (Term.app
                   (Term.proj `mem_bUnion "." (fieldIdx "2"))
                   [(Term.anonymousCtor
                     "⟨"
                     [(Term.app `gcd [`n `m])
                      ","
                      (Term.app
                       (Term.proj `mem_filter "." (fieldIdx "2"))
                       [(Term.anonymousCtor
                         "⟨"
                         [(Term.app
                           (Term.proj `mem_range "." (fieldIdx "2"))
                           [(Term.app
                             `lt_succ_of_le
                             [(Term.app
                               `le_of_dvd
                               [(Term.app `lt_of_le_of_ltₓ [(Term.app `zero_le [(Term.hole "_")]) `h])
                                (Term.app `gcd_dvd_left [(Term.hole "_") (Term.hole "_")])])])])
                          ","
                          (Term.app `gcd_dvd_left [(Term.hole "_") (Term.hole "_")])]
                         "⟩")])
                      ","
                      (Term.app
                       (Term.proj `mem_filter "." (fieldIdx "2"))
                       [(Term.anonymousCtor "⟨" [`hm "," `rfl] "⟩")])]
                     "⟩")]))))]
              "⟩")))])]))
      (calcStep («term_=_» (Term.hole "_") "=" `n) ":=" (Term.app `card_range [(Term.hole "_")]))]))
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
  (termDepIfThenElse
   "if"
   `hn0
   ":"
   («term_=_» `n "=" (numLit "0"))
   "then"
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented [(group (Tactic.simp "simp" [] [] ["[" [(Tactic.simpLemma [] [] `hn0)] "]"] []) [])])))
   "else"
   (calc
    "calc"
    [(calcStep
      («term_=_»
       (Algebra.BigOperators.Basic.«term∑_in_,_»
        "∑"
        (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `m)] []))
        " in "
        (Term.app (Term.proj (Term.app `range [`n.succ]) "." `filter) [(Init.Core.«term_∣_» (Term.cdot "·") " ∣ " `n)])
        ", "
        (Term.app (Nat.Data.Nat.Totient.termφ "φ") [`m]))
       "="
       (Algebra.BigOperators.Basic.«term∑_in_,_»
        "∑"
        (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `d)] []))
        " in "
        (Term.app (Term.proj (Term.app `range [`n.succ]) "." `filter) [(Init.Core.«term_∣_» (Term.cdot "·") " ∣ " `n)])
        ", "
        (Term.proj
         (Term.app
          (Term.proj (Term.app `range [(«term_/_» `n "/" `d)]) "." `filter)
          [(Term.fun
            "fun"
            (Term.basicFun
             [(Term.simpleBinder [`m] [])]
             "=>"
             («term_=_» (Term.app `gcd [(«term_/_» `n "/" `d) `m]) "=" (numLit "1"))))])
         "."
         `card)))
      ":="
      («term_$__»
       `Eq.symm
       "$"
       (Term.app
        `sum_bij
        [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`d (Term.hole "_")] [])] "=>" («term_/_» `n "/" `d)))
         (Term.fun
          "fun"
          (Term.basicFun
           [(Term.simpleBinder [`d `hd] [])]
           "=>"
           (Term.app
            (Term.proj `mem_filter "." (fieldIdx "2"))
            [(Term.anonymousCtor
              "⟨"
              [(«term_$__»
                (Term.proj `mem_range "." (fieldIdx "2"))
                "$"
                («term_$__» `lt_succ_of_le "$" (Term.app `Nat.div_le_selfₓ [(Term.hole "_") (Term.hole "_")])))
               ","
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(group
                    (Tactic.«tactic_<;>_»
                     (Tactic.Conv.conv
                      "conv"
                      []
                      []
                      "=>"
                      (Tactic.Conv.convSeq
                       (Tactic.Conv.convSeq1Indented
                        [(group (Tactic.Conv.rhs "rhs") [])
                         (group
                          (Tactic.Conv.convRw__
                           "rw"
                           []
                           (Tactic.rwRuleSeq
                            "["
                            [(Tactic.rwRule
                              ["←"]
                              (Term.app
                               `Nat.mul_div_cancel'ₓ
                               [(Term.proj
                                 (Term.app (Term.proj `mem_filter "." (fieldIdx "1")) [`hd])
                                 "."
                                 (fieldIdx "2"))]))]
                            "]"))
                          [])])))
                     "<;>"
                     (Tactic.simp "simp" [] [] [] []))
                    [])])))]
              "⟩")])))
         (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [(Term.hole "_") (Term.hole "_")] [])] "=>" `rfl))
         (Term.fun
          "fun"
          (Term.basicFun
           [(Term.simpleBinder [`a `b `ha `hb `h] [])]
           "=>"
           (Term.have
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`ha []]
              [(Term.typeSpec ":" («term_=_» (Finset.Data.Finset.Fold.«term_*_» `a "*" («term_/_» `n "/" `a)) "=" `n))]
              ":="
              (Term.app
               `Nat.mul_div_cancel'ₓ
               [(Term.proj (Term.app (Term.proj `mem_filter "." (fieldIdx "1")) [`ha]) "." (fieldIdx "2"))])))
            []
            (Term.have
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               []
               [(Term.typeSpec ":" («term_<_» (numLit "0") "<" («term_/_» `n "/" `a)))]
               ":="
               (Term.app
                `Nat.pos_of_ne_zeroₓ
                [(Term.fun
                  "fun"
                  (Term.basicFun
                   [(Term.simpleBinder [`h] [])]
                   "=>"
                   (Term.byTactic
                    "by"
                    (Tactic.tacticSeq
                     (Tactic.tacticSeq1Indented
                      [(group
                        (Tactic.simpAll "simp_all" [] [] ["[" [(Tactic.simpLemma [] [] `lt_irreflₓ)] "]"])
                        [])])))))])))
             []
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
                    [(Tactic.rwRule ["←"] (Term.app `Nat.mul_left_inj [`this]))
                     ","
                     (Tactic.rwRule [] `ha)
                     ","
                     (Tactic.rwRule [] `h)
                     ","
                     (Tactic.rwRule
                      []
                      (Term.app
                       `Nat.mul_div_cancel'ₓ
                       [(Term.proj (Term.app (Term.proj `mem_filter "." (fieldIdx "1")) [`hb]) "." (fieldIdx "2"))]))]
                    "]")
                   [])
                  [])])))))))
         (Term.fun
          "fun"
          (Term.basicFun
           [(Term.simpleBinder [`b `hb] [])]
           "=>"
           (Term.have
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`hb []]
              [(Term.typeSpec ":" («term_∧_» («term_<_» `b "<" `n.succ) "∧" (Init.Core.«term_∣_» `b " ∣ " `n)))]
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(group
                   (Tactic.simpa "simpa" [] [] ["[" [(Tactic.simpErase "-" `range_succ)] "]"] [] ["using" `hb])
                   [])])))))
            []
            (Term.have
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               [`hbn []]
               [(Term.typeSpec ":" (Init.Core.«term_∣_» («term_/_» `n "/" `b) " ∣ " `n))]
               ":="
               (Term.anonymousCtor
                "⟨"
                [`b
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
                        [(Tactic.rwRule [] (Term.app `Nat.div_mul_cancelₓ [(Term.proj `hb "." (fieldIdx "2"))]))]
                        "]")
                       [])
                      [])])))]
                "⟩")))
             []
             (Term.have
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                [`hnb0 []]
                [(Term.typeSpec ":" («term_≠_» («term_/_» `n "/" `b) "≠" (numLit "0")))]
                ":="
                (Term.fun
                 "fun"
                 (Term.basicFun
                  [(Term.simpleBinder [`h] [])]
                  "=>"
                  (Term.byTactic
                   "by"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented
                     [(group
                       (Tactic.simpa
                        "simpa"
                        []
                        []
                        ["[" [(Tactic.simpLemma [] [] `h) "," (Tactic.simpLemma [] [] (Term.app `Ne.symm [`hn0]))] "]"]
                        []
                        ["using" (Term.app `Nat.div_mul_cancelₓ [`hbn])])
                       [])])))))))
              []
              (Term.anonymousCtor
               "⟨"
               [(«term_/_» `n "/" `b)
                ","
                (Term.app
                 (Term.proj `mem_filter "." (fieldIdx "2"))
                 [(Term.anonymousCtor
                   "⟨"
                   [(«term_$__»
                     (Term.proj `mem_range "." (fieldIdx "2"))
                     "$"
                     («term_$__» `lt_succ_of_le "$" (Term.app `Nat.div_le_selfₓ [(Term.hole "_") (Term.hole "_")])))
                    ","
                    `hbn]
                   "⟩")])
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
                       [(Tactic.rwRule ["←"] (Term.app `Nat.mul_left_inj [(Term.app `Nat.pos_of_ne_zeroₓ [`hnb0])]))
                        ","
                        (Tactic.rwRule [] (Term.app `Nat.mul_div_cancel'ₓ [(Term.proj `hb "." (fieldIdx "2"))]))
                        ","
                        (Tactic.rwRule [] (Term.app `Nat.div_mul_cancelₓ [`hbn]))]
                       "]")
                      [])
                     [])])))]
               "⟩"))))))])))
     (calcStep
      («term_=_»
       (Term.hole "_")
       "="
       (Algebra.BigOperators.Basic.«term∑_in_,_»
        "∑"
        (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `d)] []))
        " in "
        (Term.app (Term.proj (Term.app `range [`n.succ]) "." `filter) [(Init.Core.«term_∣_» (Term.cdot "·") " ∣ " `n)])
        ", "
        (Term.proj
         (Term.app
          (Term.proj (Term.app `range [`n]) "." `filter)
          [(Term.fun
            "fun"
            (Term.basicFun [(Term.simpleBinder [`m] [])] "=>" («term_=_» (Term.app `gcd [`n `m]) "=" `d)))])
         "."
         `card)))
      ":="
      (Term.app
       `sum_congr
       [`rfl
        (Term.fun
         "fun"
         (Term.basicFun
          [(Term.simpleBinder [`d `hd] [])]
          "=>"
          (Term.have
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`hd []]
             [(Term.typeSpec ":" (Init.Core.«term_∣_» `d " ∣ " `n))]
             ":="
             (Term.proj (Term.app (Term.proj `mem_filter "." (fieldIdx "1")) [`hd]) "." (fieldIdx "2"))))
           []
           (Term.have
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`hd0 []]
              [(Term.typeSpec ":" («term_<_» (numLit "0") "<" `d))]
              ":="
              (Term.app
               `Nat.pos_of_ne_zeroₓ
               [(Term.fun
                 "fun"
                 (Term.basicFun
                  [(Term.simpleBinder [`h] [])]
                  "=>"
                  (Term.app `hn0 [(«term_$__» `eq_zero_of_zero_dvd "$" (Term.subst `h "▸" [`hd]))])))])))
            []
            (Term.app
             `card_congr
             [(Term.fun
               "fun"
               (Term.basicFun [(Term.simpleBinder [`m `hm] [])] "=>" (Finset.Data.Finset.Fold.«term_*_» `d "*" `m)))
              (Term.fun
               "fun"
               (Term.basicFun
                [(Term.simpleBinder [`m `hm] [])]
                "=>"
                (Term.have
                 "have"
                 (Term.haveDecl
                  (Term.haveIdDecl
                   [`hm []]
                   [(Term.typeSpec
                     ":"
                     («term_∧_»
                      («term_<_» `m "<" («term_/_» `n "/" `d))
                      "∧"
                      («term_=_» (Term.app `gcd [(«term_/_» `n "/" `d) `m]) "=" (numLit "1"))))]
                   ":="
                   (Term.byTactic
                    "by"
                    (Tactic.tacticSeq
                     (Tactic.tacticSeq1Indented [(group (Tactic.simpa "simpa" [] [] [] [] ["using" `hm]) [])])))))
                 []
                 (Term.app
                  (Term.proj `mem_filter "." (fieldIdx "2"))
                  [(Term.anonymousCtor
                    "⟨"
                    [(«term_$__»
                      (Term.proj `mem_range "." (fieldIdx "2"))
                      "$"
                      (Term.subst
                       (Term.app `Nat.mul_div_cancel'ₓ [`hd])
                       "▸"
                       [(Term.app
                         (Term.proj (Term.app `mul_lt_mul_left [`hd0]) "." (fieldIdx "2"))
                         [(Term.proj `hm "." (fieldIdx "1"))])]))
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
                            [(Tactic.rwRule ["←"] (Term.app `Nat.mul_div_cancel'ₓ [`hd]))
                             ","
                             (Tactic.rwRule [] `gcd_mul_left)
                             ","
                             (Tactic.rwRule [] (Term.proj `hm "." (fieldIdx "2")))
                             ","
                             (Tactic.rwRule [] `mul_oneₓ)]
                            "]")
                           [])
                          [])])))]
                    "⟩")]))))
              (Term.fun
               "fun"
               (Term.basicFun
                [(Term.simpleBinder [`a `b `ha `hb `h] [])]
                "=>"
                (Term.app (Term.proj (Term.app `Nat.mul_right_inj [`hd0]) "." (fieldIdx "1")) [`h])))
              (Term.fun
               "fun"
               (Term.basicFun
                [(Term.simpleBinder [`b `hb] [])]
                "=>"
                (Term.have
                 "have"
                 (Term.haveDecl
                  (Term.haveIdDecl
                   [`hb []]
                   [(Term.typeSpec
                     ":"
                     («term_∧_» («term_<_» `b "<" `n) "∧" («term_=_» (Term.app `gcd [`n `b]) "=" `d)))]
                   ":="
                   (Term.byTactic
                    "by"
                    (Tactic.tacticSeq
                     (Tactic.tacticSeq1Indented [(group (Tactic.simpa "simpa" [] [] [] [] ["using" `hb]) [])])))))
                 []
                 (Term.anonymousCtor
                  "⟨"
                  [(«term_/_» `b "/" `d)
                   ","
                   (Term.app
                    (Term.proj `mem_filter "." (fieldIdx "2"))
                    [(Term.anonymousCtor
                      "⟨"
                      [(Term.app
                        (Term.proj `mem_range "." (fieldIdx "2"))
                        [(Term.app
                          (Term.proj
                           (Term.app
                            `mul_lt_mul_left
                            [(Term.show
                              "show"
                              («term_<_» (numLit "0") "<" `d)
                              (Term.fromTerm
                               "from"
                               (Term.subst
                                (Term.proj `hb "." (fieldIdx "2"))
                                "▸"
                                [(Term.subst (Term.proj (Term.proj `hb "." (fieldIdx "2")) "." `symm) "▸" [`hd0])])))])
                           "."
                           (fieldIdx "1"))
                          [(Term.byTactic
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
                                   [(Tactic.rwRule ["←"] (Term.proj `hb "." (fieldIdx "2")))
                                    ","
                                    (Tactic.rwRule
                                     []
                                     (Term.app
                                      `Nat.mul_div_cancel'ₓ
                                      [(Term.app `gcd_dvd_left [(Term.hole "_") (Term.hole "_")])]))
                                    ","
                                    (Tactic.rwRule
                                     []
                                     (Term.app
                                      `Nat.mul_div_cancel'ₓ
                                      [(Term.app `gcd_dvd_right [(Term.hole "_") (Term.hole "_")])]))]
                                   "]")
                                  [])
                                 "<;>"
                                 (Tactic.exact "exact" (Term.proj `hb "." (fieldIdx "1"))))
                                [])])))])])
                       ","
                       (Term.subst
                        (Term.proj `hb "." (fieldIdx "2"))
                        "▸"
                        [(Term.app
                          `coprime_div_gcd_div_gcd
                          [(Term.subst (Term.proj (Term.proj `hb "." (fieldIdx "2")) "." `symm) "▸" [`hd0])])])]
                      "⟩")])
                   ","
                   (Term.subst
                    (Term.proj `hb "." (fieldIdx "2"))
                    "▸"
                    [(Term.app `Nat.mul_div_cancel'ₓ [(Term.app `gcd_dvd_right [(Term.hole "_") (Term.hole "_")])])])]
                  "⟩"))))])))))]))
     (calcStep
      («term_=_»
       (Term.hole "_")
       "="
       (Term.proj
        (Term.app
         (Term.proj
          (Term.app `filter [(Init.Core.«term_∣_» (Term.cdot "·") " ∣ " `n) (Term.app `range [`n.succ])])
          "."
          `bUnion)
         [(Term.fun
           "fun"
           (Term.basicFun
            [(Term.simpleBinder [`d] [])]
            "=>"
            (Term.app
             (Term.proj (Term.app `range [`n]) "." `filter)
             [(Term.fun
               "fun"
               (Term.basicFun [(Term.simpleBinder [`m] [])] "=>" («term_=_» (Term.app `gcd [`n `m]) "=" `d)))])))])
        "."
        `card))
      ":="
      (Term.proj
       (Term.app
        `card_bUnion
        [(Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(group
              (Tactic.«tactic_<;>_»
               (Tactic.intros "intros" [])
               "<;>"
               (Tactic.«tactic_<;>_»
                (Tactic.apply "apply" (Term.proj `disjoint_filter "." (fieldIdx "2")))
                "<;>"
                (Tactic.cc "cc")))
              [])])))])
       "."
       `symm))
     (calcStep
      («term_=_» (Term.hole "_") "=" (Term.proj (Term.app `range [`n]) "." `card))
      ":="
      (Term.app
       `congr_argₓ
       [`card
        (Term.app
         `Finset.ext
         [(Term.fun
           "fun"
           (Term.basicFun
            [(Term.simpleBinder [`m] [])]
            "=>"
            (Term.anonymousCtor
             "⟨"
             [(Term.byTactic
               "by"
               (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.finish "finish" [] [] []) [])])))
              ","
              (Term.fun
               "fun"
               (Term.basicFun
                [(Term.simpleBinder [`hm] [])]
                "=>"
                (Term.have
                 "have"
                 (Term.haveDecl
                  (Term.haveIdDecl
                   [`h []]
                   [(Term.typeSpec ":" («term_<_» `m "<" `n))]
                   ":="
                   (Term.app (Term.proj `mem_range "." (fieldIdx "1")) [`hm])))
                 []
                 (Term.app
                  (Term.proj `mem_bUnion "." (fieldIdx "2"))
                  [(Term.anonymousCtor
                    "⟨"
                    [(Term.app `gcd [`n `m])
                     ","
                     (Term.app
                      (Term.proj `mem_filter "." (fieldIdx "2"))
                      [(Term.anonymousCtor
                        "⟨"
                        [(Term.app
                          (Term.proj `mem_range "." (fieldIdx "2"))
                          [(Term.app
                            `lt_succ_of_le
                            [(Term.app
                              `le_of_dvd
                              [(Term.app `lt_of_le_of_ltₓ [(Term.app `zero_le [(Term.hole "_")]) `h])
                               (Term.app `gcd_dvd_left [(Term.hole "_") (Term.hole "_")])])])])
                         ","
                         (Term.app `gcd_dvd_left [(Term.hole "_") (Term.hole "_")])]
                        "⟩")])
                     ","
                     (Term.app
                      (Term.proj `mem_filter "." (fieldIdx "2"))
                      [(Term.anonymousCtor "⟨" [`hm "," `rfl] "⟩")])]
                    "⟩")]))))]
             "⟩")))])]))
     (calcStep («term_=_» (Term.hole "_") "=" `n) ":=" (Term.app `card_range [(Term.hole "_")]))]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'termDepIfThenElse', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (calc
   "calc"
   [(calcStep
     («term_=_»
      (Algebra.BigOperators.Basic.«term∑_in_,_»
       "∑"
       (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `m)] []))
       " in "
       (Term.app (Term.proj (Term.app `range [`n.succ]) "." `filter) [(Init.Core.«term_∣_» (Term.cdot "·") " ∣ " `n)])
       ", "
       (Term.app (Nat.Data.Nat.Totient.termφ "φ") [`m]))
      "="
      (Algebra.BigOperators.Basic.«term∑_in_,_»
       "∑"
       (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `d)] []))
       " in "
       (Term.app (Term.proj (Term.app `range [`n.succ]) "." `filter) [(Init.Core.«term_∣_» (Term.cdot "·") " ∣ " `n)])
       ", "
       (Term.proj
        (Term.app
         (Term.proj (Term.app `range [(«term_/_» `n "/" `d)]) "." `filter)
         [(Term.fun
           "fun"
           (Term.basicFun
            [(Term.simpleBinder [`m] [])]
            "=>"
            («term_=_» (Term.app `gcd [(«term_/_» `n "/" `d) `m]) "=" (numLit "1"))))])
        "."
        `card)))
     ":="
     («term_$__»
      `Eq.symm
      "$"
      (Term.app
       `sum_bij
       [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`d (Term.hole "_")] [])] "=>" («term_/_» `n "/" `d)))
        (Term.fun
         "fun"
         (Term.basicFun
          [(Term.simpleBinder [`d `hd] [])]
          "=>"
          (Term.app
           (Term.proj `mem_filter "." (fieldIdx "2"))
           [(Term.anonymousCtor
             "⟨"
             [(«term_$__»
               (Term.proj `mem_range "." (fieldIdx "2"))
               "$"
               («term_$__» `lt_succ_of_le "$" (Term.app `Nat.div_le_selfₓ [(Term.hole "_") (Term.hole "_")])))
              ","
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(group
                   (Tactic.«tactic_<;>_»
                    (Tactic.Conv.conv
                     "conv"
                     []
                     []
                     "=>"
                     (Tactic.Conv.convSeq
                      (Tactic.Conv.convSeq1Indented
                       [(group (Tactic.Conv.rhs "rhs") [])
                        (group
                         (Tactic.Conv.convRw__
                          "rw"
                          []
                          (Tactic.rwRuleSeq
                           "["
                           [(Tactic.rwRule
                             ["←"]
                             (Term.app
                              `Nat.mul_div_cancel'ₓ
                              [(Term.proj
                                (Term.app (Term.proj `mem_filter "." (fieldIdx "1")) [`hd])
                                "."
                                (fieldIdx "2"))]))]
                           "]"))
                         [])])))
                    "<;>"
                    (Tactic.simp "simp" [] [] [] []))
                   [])])))]
             "⟩")])))
        (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [(Term.hole "_") (Term.hole "_")] [])] "=>" `rfl))
        (Term.fun
         "fun"
         (Term.basicFun
          [(Term.simpleBinder [`a `b `ha `hb `h] [])]
          "=>"
          (Term.have
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`ha []]
             [(Term.typeSpec ":" («term_=_» (Finset.Data.Finset.Fold.«term_*_» `a "*" («term_/_» `n "/" `a)) "=" `n))]
             ":="
             (Term.app
              `Nat.mul_div_cancel'ₓ
              [(Term.proj (Term.app (Term.proj `mem_filter "." (fieldIdx "1")) [`ha]) "." (fieldIdx "2"))])))
           []
           (Term.have
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              []
              [(Term.typeSpec ":" («term_<_» (numLit "0") "<" («term_/_» `n "/" `a)))]
              ":="
              (Term.app
               `Nat.pos_of_ne_zeroₓ
               [(Term.fun
                 "fun"
                 (Term.basicFun
                  [(Term.simpleBinder [`h] [])]
                  "=>"
                  (Term.byTactic
                   "by"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented
                     [(group
                       (Tactic.simpAll "simp_all" [] [] ["[" [(Tactic.simpLemma [] [] `lt_irreflₓ)] "]"])
                       [])])))))])))
            []
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
                   [(Tactic.rwRule ["←"] (Term.app `Nat.mul_left_inj [`this]))
                    ","
                    (Tactic.rwRule [] `ha)
                    ","
                    (Tactic.rwRule [] `h)
                    ","
                    (Tactic.rwRule
                     []
                     (Term.app
                      `Nat.mul_div_cancel'ₓ
                      [(Term.proj (Term.app (Term.proj `mem_filter "." (fieldIdx "1")) [`hb]) "." (fieldIdx "2"))]))]
                   "]")
                  [])
                 [])])))))))
        (Term.fun
         "fun"
         (Term.basicFun
          [(Term.simpleBinder [`b `hb] [])]
          "=>"
          (Term.have
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`hb []]
             [(Term.typeSpec ":" («term_∧_» («term_<_» `b "<" `n.succ) "∧" (Init.Core.«term_∣_» `b " ∣ " `n)))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(group
                  (Tactic.simpa "simpa" [] [] ["[" [(Tactic.simpErase "-" `range_succ)] "]"] [] ["using" `hb])
                  [])])))))
           []
           (Term.have
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`hbn []]
              [(Term.typeSpec ":" (Init.Core.«term_∣_» («term_/_» `n "/" `b) " ∣ " `n))]
              ":="
              (Term.anonymousCtor
               "⟨"
               [`b
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
                       [(Tactic.rwRule [] (Term.app `Nat.div_mul_cancelₓ [(Term.proj `hb "." (fieldIdx "2"))]))]
                       "]")
                      [])
                     [])])))]
               "⟩")))
            []
            (Term.have
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               [`hnb0 []]
               [(Term.typeSpec ":" («term_≠_» («term_/_» `n "/" `b) "≠" (numLit "0")))]
               ":="
               (Term.fun
                "fun"
                (Term.basicFun
                 [(Term.simpleBinder [`h] [])]
                 "=>"
                 (Term.byTactic
                  "by"
                  (Tactic.tacticSeq
                   (Tactic.tacticSeq1Indented
                    [(group
                      (Tactic.simpa
                       "simpa"
                       []
                       []
                       ["[" [(Tactic.simpLemma [] [] `h) "," (Tactic.simpLemma [] [] (Term.app `Ne.symm [`hn0]))] "]"]
                       []
                       ["using" (Term.app `Nat.div_mul_cancelₓ [`hbn])])
                      [])])))))))
             []
             (Term.anonymousCtor
              "⟨"
              [(«term_/_» `n "/" `b)
               ","
               (Term.app
                (Term.proj `mem_filter "." (fieldIdx "2"))
                [(Term.anonymousCtor
                  "⟨"
                  [(«term_$__»
                    (Term.proj `mem_range "." (fieldIdx "2"))
                    "$"
                    («term_$__» `lt_succ_of_le "$" (Term.app `Nat.div_le_selfₓ [(Term.hole "_") (Term.hole "_")])))
                   ","
                   `hbn]
                  "⟩")])
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
                      [(Tactic.rwRule ["←"] (Term.app `Nat.mul_left_inj [(Term.app `Nat.pos_of_ne_zeroₓ [`hnb0])]))
                       ","
                       (Tactic.rwRule [] (Term.app `Nat.mul_div_cancel'ₓ [(Term.proj `hb "." (fieldIdx "2"))]))
                       ","
                       (Tactic.rwRule [] (Term.app `Nat.div_mul_cancelₓ [`hbn]))]
                      "]")
                     [])
                    [])])))]
              "⟩"))))))])))
    (calcStep
     («term_=_»
      (Term.hole "_")
      "="
      (Algebra.BigOperators.Basic.«term∑_in_,_»
       "∑"
       (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `d)] []))
       " in "
       (Term.app (Term.proj (Term.app `range [`n.succ]) "." `filter) [(Init.Core.«term_∣_» (Term.cdot "·") " ∣ " `n)])
       ", "
       (Term.proj
        (Term.app
         (Term.proj (Term.app `range [`n]) "." `filter)
         [(Term.fun
           "fun"
           (Term.basicFun [(Term.simpleBinder [`m] [])] "=>" («term_=_» (Term.app `gcd [`n `m]) "=" `d)))])
        "."
        `card)))
     ":="
     (Term.app
      `sum_congr
      [`rfl
       (Term.fun
        "fun"
        (Term.basicFun
         [(Term.simpleBinder [`d `hd] [])]
         "=>"
         (Term.have
          "have"
          (Term.haveDecl
           (Term.haveIdDecl
            [`hd []]
            [(Term.typeSpec ":" (Init.Core.«term_∣_» `d " ∣ " `n))]
            ":="
            (Term.proj (Term.app (Term.proj `mem_filter "." (fieldIdx "1")) [`hd]) "." (fieldIdx "2"))))
          []
          (Term.have
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`hd0 []]
             [(Term.typeSpec ":" («term_<_» (numLit "0") "<" `d))]
             ":="
             (Term.app
              `Nat.pos_of_ne_zeroₓ
              [(Term.fun
                "fun"
                (Term.basicFun
                 [(Term.simpleBinder [`h] [])]
                 "=>"
                 (Term.app `hn0 [(«term_$__» `eq_zero_of_zero_dvd "$" (Term.subst `h "▸" [`hd]))])))])))
           []
           (Term.app
            `card_congr
            [(Term.fun
              "fun"
              (Term.basicFun [(Term.simpleBinder [`m `hm] [])] "=>" (Finset.Data.Finset.Fold.«term_*_» `d "*" `m)))
             (Term.fun
              "fun"
              (Term.basicFun
               [(Term.simpleBinder [`m `hm] [])]
               "=>"
               (Term.have
                "have"
                (Term.haveDecl
                 (Term.haveIdDecl
                  [`hm []]
                  [(Term.typeSpec
                    ":"
                    («term_∧_»
                     («term_<_» `m "<" («term_/_» `n "/" `d))
                     "∧"
                     («term_=_» (Term.app `gcd [(«term_/_» `n "/" `d) `m]) "=" (numLit "1"))))]
                  ":="
                  (Term.byTactic
                   "by"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented [(group (Tactic.simpa "simpa" [] [] [] [] ["using" `hm]) [])])))))
                []
                (Term.app
                 (Term.proj `mem_filter "." (fieldIdx "2"))
                 [(Term.anonymousCtor
                   "⟨"
                   [(«term_$__»
                     (Term.proj `mem_range "." (fieldIdx "2"))
                     "$"
                     (Term.subst
                      (Term.app `Nat.mul_div_cancel'ₓ [`hd])
                      "▸"
                      [(Term.app
                        (Term.proj (Term.app `mul_lt_mul_left [`hd0]) "." (fieldIdx "2"))
                        [(Term.proj `hm "." (fieldIdx "1"))])]))
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
                           [(Tactic.rwRule ["←"] (Term.app `Nat.mul_div_cancel'ₓ [`hd]))
                            ","
                            (Tactic.rwRule [] `gcd_mul_left)
                            ","
                            (Tactic.rwRule [] (Term.proj `hm "." (fieldIdx "2")))
                            ","
                            (Tactic.rwRule [] `mul_oneₓ)]
                           "]")
                          [])
                         [])])))]
                   "⟩")]))))
             (Term.fun
              "fun"
              (Term.basicFun
               [(Term.simpleBinder [`a `b `ha `hb `h] [])]
               "=>"
               (Term.app (Term.proj (Term.app `Nat.mul_right_inj [`hd0]) "." (fieldIdx "1")) [`h])))
             (Term.fun
              "fun"
              (Term.basicFun
               [(Term.simpleBinder [`b `hb] [])]
               "=>"
               (Term.have
                "have"
                (Term.haveDecl
                 (Term.haveIdDecl
                  [`hb []]
                  [(Term.typeSpec ":" («term_∧_» («term_<_» `b "<" `n) "∧" («term_=_» (Term.app `gcd [`n `b]) "=" `d)))]
                  ":="
                  (Term.byTactic
                   "by"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented [(group (Tactic.simpa "simpa" [] [] [] [] ["using" `hb]) [])])))))
                []
                (Term.anonymousCtor
                 "⟨"
                 [(«term_/_» `b "/" `d)
                  ","
                  (Term.app
                   (Term.proj `mem_filter "." (fieldIdx "2"))
                   [(Term.anonymousCtor
                     "⟨"
                     [(Term.app
                       (Term.proj `mem_range "." (fieldIdx "2"))
                       [(Term.app
                         (Term.proj
                          (Term.app
                           `mul_lt_mul_left
                           [(Term.show
                             "show"
                             («term_<_» (numLit "0") "<" `d)
                             (Term.fromTerm
                              "from"
                              (Term.subst
                               (Term.proj `hb "." (fieldIdx "2"))
                               "▸"
                               [(Term.subst (Term.proj (Term.proj `hb "." (fieldIdx "2")) "." `symm) "▸" [`hd0])])))])
                          "."
                          (fieldIdx "1"))
                         [(Term.byTactic
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
                                  [(Tactic.rwRule ["←"] (Term.proj `hb "." (fieldIdx "2")))
                                   ","
                                   (Tactic.rwRule
                                    []
                                    (Term.app
                                     `Nat.mul_div_cancel'ₓ
                                     [(Term.app `gcd_dvd_left [(Term.hole "_") (Term.hole "_")])]))
                                   ","
                                   (Tactic.rwRule
                                    []
                                    (Term.app
                                     `Nat.mul_div_cancel'ₓ
                                     [(Term.app `gcd_dvd_right [(Term.hole "_") (Term.hole "_")])]))]
                                  "]")
                                 [])
                                "<;>"
                                (Tactic.exact "exact" (Term.proj `hb "." (fieldIdx "1"))))
                               [])])))])])
                      ","
                      (Term.subst
                       (Term.proj `hb "." (fieldIdx "2"))
                       "▸"
                       [(Term.app
                         `coprime_div_gcd_div_gcd
                         [(Term.subst (Term.proj (Term.proj `hb "." (fieldIdx "2")) "." `symm) "▸" [`hd0])])])]
                     "⟩")])
                  ","
                  (Term.subst
                   (Term.proj `hb "." (fieldIdx "2"))
                   "▸"
                   [(Term.app `Nat.mul_div_cancel'ₓ [(Term.app `gcd_dvd_right [(Term.hole "_") (Term.hole "_")])])])]
                 "⟩"))))])))))]))
    (calcStep
     («term_=_»
      (Term.hole "_")
      "="
      (Term.proj
       (Term.app
        (Term.proj
         (Term.app `filter [(Init.Core.«term_∣_» (Term.cdot "·") " ∣ " `n) (Term.app `range [`n.succ])])
         "."
         `bUnion)
        [(Term.fun
          "fun"
          (Term.basicFun
           [(Term.simpleBinder [`d] [])]
           "=>"
           (Term.app
            (Term.proj (Term.app `range [`n]) "." `filter)
            [(Term.fun
              "fun"
              (Term.basicFun [(Term.simpleBinder [`m] [])] "=>" («term_=_» (Term.app `gcd [`n `m]) "=" `d)))])))])
       "."
       `card))
     ":="
     (Term.proj
      (Term.app
       `card_bUnion
       [(Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group
             (Tactic.«tactic_<;>_»
              (Tactic.intros "intros" [])
              "<;>"
              (Tactic.«tactic_<;>_»
               (Tactic.apply "apply" (Term.proj `disjoint_filter "." (fieldIdx "2")))
               "<;>"
               (Tactic.cc "cc")))
             [])])))])
      "."
      `symm))
    (calcStep
     («term_=_» (Term.hole "_") "=" (Term.proj (Term.app `range [`n]) "." `card))
     ":="
     (Term.app
      `congr_argₓ
      [`card
       (Term.app
        `Finset.ext
        [(Term.fun
          "fun"
          (Term.basicFun
           [(Term.simpleBinder [`m] [])]
           "=>"
           (Term.anonymousCtor
            "⟨"
            [(Term.byTactic
              "by"
              (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.finish "finish" [] [] []) [])])))
             ","
             (Term.fun
              "fun"
              (Term.basicFun
               [(Term.simpleBinder [`hm] [])]
               "=>"
               (Term.have
                "have"
                (Term.haveDecl
                 (Term.haveIdDecl
                  [`h []]
                  [(Term.typeSpec ":" («term_<_» `m "<" `n))]
                  ":="
                  (Term.app (Term.proj `mem_range "." (fieldIdx "1")) [`hm])))
                []
                (Term.app
                 (Term.proj `mem_bUnion "." (fieldIdx "2"))
                 [(Term.anonymousCtor
                   "⟨"
                   [(Term.app `gcd [`n `m])
                    ","
                    (Term.app
                     (Term.proj `mem_filter "." (fieldIdx "2"))
                     [(Term.anonymousCtor
                       "⟨"
                       [(Term.app
                         (Term.proj `mem_range "." (fieldIdx "2"))
                         [(Term.app
                           `lt_succ_of_le
                           [(Term.app
                             `le_of_dvd
                             [(Term.app `lt_of_le_of_ltₓ [(Term.app `zero_le [(Term.hole "_")]) `h])
                              (Term.app `gcd_dvd_left [(Term.hole "_") (Term.hole "_")])])])])
                        ","
                        (Term.app `gcd_dvd_left [(Term.hole "_") (Term.hole "_")])]
                       "⟩")])
                    ","
                    (Term.app (Term.proj `mem_filter "." (fieldIdx "2")) [(Term.anonymousCtor "⟨" [`hm "," `rfl] "⟩")])]
                   "⟩")]))))]
            "⟩")))])]))
    (calcStep («term_=_» (Term.hole "_") "=" `n) ":=" (Term.app `card_range [(Term.hole "_")]))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'calc', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'calcStep', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `card_range [(Term.hole "_")])
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
  `card_range
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_=_» (Term.hole "_") "=" `n)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'calcStep', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
  (Term.app
   `congr_argₓ
   [`card
    (Term.app
     `Finset.ext
     [(Term.fun
       "fun"
       (Term.basicFun
        [(Term.simpleBinder [`m] [])]
        "=>"
        (Term.anonymousCtor
         "⟨"
         [(Term.byTactic
           "by"
           (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.finish "finish" [] [] []) [])])))
          ","
          (Term.fun
           "fun"
           (Term.basicFun
            [(Term.simpleBinder [`hm] [])]
            "=>"
            (Term.have
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               [`h []]
               [(Term.typeSpec ":" («term_<_» `m "<" `n))]
               ":="
               (Term.app (Term.proj `mem_range "." (fieldIdx "1")) [`hm])))
             []
             (Term.app
              (Term.proj `mem_bUnion "." (fieldIdx "2"))
              [(Term.anonymousCtor
                "⟨"
                [(Term.app `gcd [`n `m])
                 ","
                 (Term.app
                  (Term.proj `mem_filter "." (fieldIdx "2"))
                  [(Term.anonymousCtor
                    "⟨"
                    [(Term.app
                      (Term.proj `mem_range "." (fieldIdx "2"))
                      [(Term.app
                        `lt_succ_of_le
                        [(Term.app
                          `le_of_dvd
                          [(Term.app `lt_of_le_of_ltₓ [(Term.app `zero_le [(Term.hole "_")]) `h])
                           (Term.app `gcd_dvd_left [(Term.hole "_") (Term.hole "_")])])])])
                     ","
                     (Term.app `gcd_dvd_left [(Term.hole "_") (Term.hole "_")])]
                    "⟩")])
                 ","
                 (Term.app (Term.proj `mem_filter "." (fieldIdx "2")) [(Term.anonymousCtor "⟨" [`hm "," `rfl] "⟩")])]
                "⟩")]))))]
         "⟩")))])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `Finset.ext
   [(Term.fun
     "fun"
     (Term.basicFun
      [(Term.simpleBinder [`m] [])]
      "=>"
      (Term.anonymousCtor
       "⟨"
       [(Term.byTactic
         "by"
         (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.finish "finish" [] [] []) [])])))
        ","
        (Term.fun
         "fun"
         (Term.basicFun
          [(Term.simpleBinder [`hm] [])]
          "=>"
          (Term.have
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`h []]
             [(Term.typeSpec ":" («term_<_» `m "<" `n))]
             ":="
             (Term.app (Term.proj `mem_range "." (fieldIdx "1")) [`hm])))
           []
           (Term.app
            (Term.proj `mem_bUnion "." (fieldIdx "2"))
            [(Term.anonymousCtor
              "⟨"
              [(Term.app `gcd [`n `m])
               ","
               (Term.app
                (Term.proj `mem_filter "." (fieldIdx "2"))
                [(Term.anonymousCtor
                  "⟨"
                  [(Term.app
                    (Term.proj `mem_range "." (fieldIdx "2"))
                    [(Term.app
                      `lt_succ_of_le
                      [(Term.app
                        `le_of_dvd
                        [(Term.app `lt_of_le_of_ltₓ [(Term.app `zero_le [(Term.hole "_")]) `h])
                         (Term.app `gcd_dvd_left [(Term.hole "_") (Term.hole "_")])])])])
                   ","
                   (Term.app `gcd_dvd_left [(Term.hole "_") (Term.hole "_")])]
                  "⟩")])
               ","
               (Term.app (Term.proj `mem_filter "." (fieldIdx "2")) [(Term.anonymousCtor "⟨" [`hm "," `rfl] "⟩")])]
              "⟩")]))))]
       "⟩")))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [`m] [])]
    "=>"
    (Term.anonymousCtor
     "⟨"
     [(Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.finish "finish" [] [] []) [])])))
      ","
      (Term.fun
       "fun"
       (Term.basicFun
        [(Term.simpleBinder [`hm] [])]
        "=>"
        (Term.have
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`h []]
           [(Term.typeSpec ":" («term_<_» `m "<" `n))]
           ":="
           (Term.app (Term.proj `mem_range "." (fieldIdx "1")) [`hm])))
         []
         (Term.app
          (Term.proj `mem_bUnion "." (fieldIdx "2"))
          [(Term.anonymousCtor
            "⟨"
            [(Term.app `gcd [`n `m])
             ","
             (Term.app
              (Term.proj `mem_filter "." (fieldIdx "2"))
              [(Term.anonymousCtor
                "⟨"
                [(Term.app
                  (Term.proj `mem_range "." (fieldIdx "2"))
                  [(Term.app
                    `lt_succ_of_le
                    [(Term.app
                      `le_of_dvd
                      [(Term.app `lt_of_le_of_ltₓ [(Term.app `zero_le [(Term.hole "_")]) `h])
                       (Term.app `gcd_dvd_left [(Term.hole "_") (Term.hole "_")])])])])
                 ","
                 (Term.app `gcd_dvd_left [(Term.hole "_") (Term.hole "_")])]
                "⟩")])
             ","
             (Term.app (Term.proj `mem_filter "." (fieldIdx "2")) [(Term.anonymousCtor "⟨" [`hm "," `rfl] "⟩")])]
            "⟩")]))))]
     "⟩")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor
   "⟨"
   [(Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.finish "finish" [] [] []) [])])))
    ","
    (Term.fun
     "fun"
     (Term.basicFun
      [(Term.simpleBinder [`hm] [])]
      "=>"
      (Term.have
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`h []]
         [(Term.typeSpec ":" («term_<_» `m "<" `n))]
         ":="
         (Term.app (Term.proj `mem_range "." (fieldIdx "1")) [`hm])))
       []
       (Term.app
        (Term.proj `mem_bUnion "." (fieldIdx "2"))
        [(Term.anonymousCtor
          "⟨"
          [(Term.app `gcd [`n `m])
           ","
           (Term.app
            (Term.proj `mem_filter "." (fieldIdx "2"))
            [(Term.anonymousCtor
              "⟨"
              [(Term.app
                (Term.proj `mem_range "." (fieldIdx "2"))
                [(Term.app
                  `lt_succ_of_le
                  [(Term.app
                    `le_of_dvd
                    [(Term.app `lt_of_le_of_ltₓ [(Term.app `zero_le [(Term.hole "_")]) `h])
                     (Term.app `gcd_dvd_left [(Term.hole "_") (Term.hole "_")])])])])
               ","
               (Term.app `gcd_dvd_left [(Term.hole "_") (Term.hole "_")])]
              "⟩")])
           ","
           (Term.app (Term.proj `mem_filter "." (fieldIdx "2")) [(Term.anonymousCtor "⟨" [`hm "," `rfl] "⟩")])]
          "⟩")]))))]
   "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [`hm] [])]
    "=>"
    (Term.have
     "have"
     (Term.haveDecl
      (Term.haveIdDecl
       [`h []]
       [(Term.typeSpec ":" («term_<_» `m "<" `n))]
       ":="
       (Term.app (Term.proj `mem_range "." (fieldIdx "1")) [`hm])))
     []
     (Term.app
      (Term.proj `mem_bUnion "." (fieldIdx "2"))
      [(Term.anonymousCtor
        "⟨"
        [(Term.app `gcd [`n `m])
         ","
         (Term.app
          (Term.proj `mem_filter "." (fieldIdx "2"))
          [(Term.anonymousCtor
            "⟨"
            [(Term.app
              (Term.proj `mem_range "." (fieldIdx "2"))
              [(Term.app
                `lt_succ_of_le
                [(Term.app
                  `le_of_dvd
                  [(Term.app `lt_of_le_of_ltₓ [(Term.app `zero_le [(Term.hole "_")]) `h])
                   (Term.app `gcd_dvd_left [(Term.hole "_") (Term.hole "_")])])])])
             ","
             (Term.app `gcd_dvd_left [(Term.hole "_") (Term.hole "_")])]
            "⟩")])
         ","
         (Term.app (Term.proj `mem_filter "." (fieldIdx "2")) [(Term.anonymousCtor "⟨" [`hm "," `rfl] "⟩")])]
        "⟩")]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.have
   "have"
   (Term.haveDecl
    (Term.haveIdDecl
     [`h []]
     [(Term.typeSpec ":" («term_<_» `m "<" `n))]
     ":="
     (Term.app (Term.proj `mem_range "." (fieldIdx "1")) [`hm])))
   []
   (Term.app
    (Term.proj `mem_bUnion "." (fieldIdx "2"))
    [(Term.anonymousCtor
      "⟨"
      [(Term.app `gcd [`n `m])
       ","
       (Term.app
        (Term.proj `mem_filter "." (fieldIdx "2"))
        [(Term.anonymousCtor
          "⟨"
          [(Term.app
            (Term.proj `mem_range "." (fieldIdx "2"))
            [(Term.app
              `lt_succ_of_le
              [(Term.app
                `le_of_dvd
                [(Term.app `lt_of_le_of_ltₓ [(Term.app `zero_le [(Term.hole "_")]) `h])
                 (Term.app `gcd_dvd_left [(Term.hole "_") (Term.hole "_")])])])])
           ","
           (Term.app `gcd_dvd_left [(Term.hole "_") (Term.hole "_")])]
          "⟩")])
       ","
       (Term.app (Term.proj `mem_filter "." (fieldIdx "2")) [(Term.anonymousCtor "⟨" [`hm "," `rfl] "⟩")])]
      "⟩")]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.have', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.have', expected 'Lean.Parser.Term.have.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   (Term.proj `mem_bUnion "." (fieldIdx "2"))
   [(Term.anonymousCtor
     "⟨"
     [(Term.app `gcd [`n `m])
      ","
      (Term.app
       (Term.proj `mem_filter "." (fieldIdx "2"))
       [(Term.anonymousCtor
         "⟨"
         [(Term.app
           (Term.proj `mem_range "." (fieldIdx "2"))
           [(Term.app
             `lt_succ_of_le
             [(Term.app
               `le_of_dvd
               [(Term.app `lt_of_le_of_ltₓ [(Term.app `zero_le [(Term.hole "_")]) `h])
                (Term.app `gcd_dvd_left [(Term.hole "_") (Term.hole "_")])])])])
          ","
          (Term.app `gcd_dvd_left [(Term.hole "_") (Term.hole "_")])]
         "⟩")])
      ","
      (Term.app (Term.proj `mem_filter "." (fieldIdx "2")) [(Term.anonymousCtor "⟨" [`hm "," `rfl] "⟩")])]
     "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor
   "⟨"
   [(Term.app `gcd [`n `m])
    ","
    (Term.app
     (Term.proj `mem_filter "." (fieldIdx "2"))
     [(Term.anonymousCtor
       "⟨"
       [(Term.app
         (Term.proj `mem_range "." (fieldIdx "2"))
         [(Term.app
           `lt_succ_of_le
           [(Term.app
             `le_of_dvd
             [(Term.app `lt_of_le_of_ltₓ [(Term.app `zero_le [(Term.hole "_")]) `h])
              (Term.app `gcd_dvd_left [(Term.hole "_") (Term.hole "_")])])])])
        ","
        (Term.app `gcd_dvd_left [(Term.hole "_") (Term.hole "_")])]
       "⟩")])
    ","
    (Term.app (Term.proj `mem_filter "." (fieldIdx "2")) [(Term.anonymousCtor "⟨" [`hm "," `rfl] "⟩")])]
   "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app (Term.proj `mem_filter "." (fieldIdx "2")) [(Term.anonymousCtor "⟨" [`hm "," `rfl] "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor "⟨" [`hm "," `rfl] "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `rfl
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hm
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.proj `mem_filter "." (fieldIdx "2"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `mem_filter
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   (Term.proj `mem_filter "." (fieldIdx "2"))
   [(Term.anonymousCtor
     "⟨"
     [(Term.app
       (Term.proj `mem_range "." (fieldIdx "2"))
       [(Term.app
         `lt_succ_of_le
         [(Term.app
           `le_of_dvd
           [(Term.app `lt_of_le_of_ltₓ [(Term.app `zero_le [(Term.hole "_")]) `h])
            (Term.app `gcd_dvd_left [(Term.hole "_") (Term.hole "_")])])])])
      ","
      (Term.app `gcd_dvd_left [(Term.hole "_") (Term.hole "_")])]
     "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor
   "⟨"
   [(Term.app
     (Term.proj `mem_range "." (fieldIdx "2"))
     [(Term.app
       `lt_succ_of_le
       [(Term.app
         `le_of_dvd
         [(Term.app `lt_of_le_of_ltₓ [(Term.app `zero_le [(Term.hole "_")]) `h])
          (Term.app `gcd_dvd_left [(Term.hole "_") (Term.hole "_")])])])])
    ","
    (Term.app `gcd_dvd_left [(Term.hole "_") (Term.hole "_")])]
   "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `gcd_dvd_left [(Term.hole "_") (Term.hole "_")])
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
  `gcd_dvd_left
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   (Term.proj `mem_range "." (fieldIdx "2"))
   [(Term.app
     `lt_succ_of_le
     [(Term.app
       `le_of_dvd
       [(Term.app `lt_of_le_of_ltₓ [(Term.app `zero_le [(Term.hole "_")]) `h])
        (Term.app `gcd_dvd_left [(Term.hole "_") (Term.hole "_")])])])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `lt_succ_of_le
   [(Term.app
     `le_of_dvd
     [(Term.app `lt_of_le_of_ltₓ [(Term.app `zero_le [(Term.hole "_")]) `h])
      (Term.app `gcd_dvd_left [(Term.hole "_") (Term.hole "_")])])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `le_of_dvd
   [(Term.app `lt_of_le_of_ltₓ [(Term.app `zero_le [(Term.hole "_")]) `h])
    (Term.app `gcd_dvd_left [(Term.hole "_") (Term.hole "_")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `gcd_dvd_left [(Term.hole "_") (Term.hole "_")])
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
  `gcd_dvd_left
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app `gcd_dvd_left [(Term.hole "_") (Term.hole "_")]) []]
 ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `lt_of_le_of_ltₓ [(Term.app `zero_le [(Term.hole "_")]) `h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `h
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `zero_le [(Term.hole "_")])
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
  `zero_le
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `zero_le [(Term.hole "_")]) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `lt_of_le_of_ltₓ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app `lt_of_le_of_ltₓ [(Term.paren "(" [(Term.app `zero_le [(Term.hole "_")]) []] ")") `h]) []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `le_of_dvd
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app
   `le_of_dvd
   [(Term.paren
     "("
     [(Term.app `lt_of_le_of_ltₓ [(Term.paren "(" [(Term.app `zero_le [(Term.hole "_")]) []] ")") `h]) []]
     ")")
    (Term.paren "(" [(Term.app `gcd_dvd_left [(Term.hole "_") (Term.hole "_")]) []] ")")])
  []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `lt_succ_of_le
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app
   `lt_succ_of_le
   [(Term.paren
     "("
     [(Term.app
       `le_of_dvd
       [(Term.paren
         "("
         [(Term.app `lt_of_le_of_ltₓ [(Term.paren "(" [(Term.app `zero_le [(Term.hole "_")]) []] ")") `h]) []]
         ")")
        (Term.paren "(" [(Term.app `gcd_dvd_left [(Term.hole "_") (Term.hole "_")]) []] ")")])
      []]
     ")")])
  []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.proj `mem_range "." (fieldIdx "2"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `mem_range
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.proj `mem_filter "." (fieldIdx "2"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `mem_filter
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `gcd [`n `m])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `m
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `gcd
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.proj `mem_bUnion "." (fieldIdx "2"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `mem_bUnion
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveDecl', expected 'Lean.Parser.Term.haveDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveIdDecl.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
  (Term.app (Term.proj `mem_range "." (fieldIdx "1")) [`hm])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hm
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.proj `mem_range "." (fieldIdx "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `mem_range
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_<_» `m "<" `n)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_<_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  `m
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
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
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.finish "finish" [] [] []) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.finish "finish" [] [] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.finish', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
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
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Finset.ext
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app
   `Finset.ext
   [(Term.fun
     "fun"
     (Term.basicFun
      [(Term.simpleBinder [`m] [])]
      "=>"
      (Term.anonymousCtor
       "⟨"
       [(Term.byTactic
         "by"
         (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.finish "finish" [] [] []) [])])))
        ","
        (Term.fun
         "fun"
         (Term.basicFun
          [(Term.simpleBinder [`hm] [])]
          "=>"
          (Term.have
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`h []]
             [(Term.typeSpec ":" («term_<_» `m "<" `n))]
             ":="
             (Term.app (Term.proj `mem_range "." (fieldIdx "1")) [`hm])))
           []
           (Term.app
            (Term.proj `mem_bUnion "." (fieldIdx "2"))
            [(Term.anonymousCtor
              "⟨"
              [(Term.app `gcd [`n `m])
               ","
               (Term.app
                (Term.proj `mem_filter "." (fieldIdx "2"))
                [(Term.anonymousCtor
                  "⟨"
                  [(Term.app
                    (Term.proj `mem_range "." (fieldIdx "2"))
                    [(Term.paren
                      "("
                      [(Term.app
                        `lt_succ_of_le
                        [(Term.paren
                          "("
                          [(Term.app
                            `le_of_dvd
                            [(Term.paren
                              "("
                              [(Term.app
                                `lt_of_le_of_ltₓ
                                [(Term.paren "(" [(Term.app `zero_le [(Term.hole "_")]) []] ")") `h])
                               []]
                              ")")
                             (Term.paren "(" [(Term.app `gcd_dvd_left [(Term.hole "_") (Term.hole "_")]) []] ")")])
                           []]
                          ")")])
                       []]
                      ")")])
                   ","
                   (Term.app `gcd_dvd_left [(Term.hole "_") (Term.hole "_")])]
                  "⟩")])
               ","
               (Term.app (Term.proj `mem_filter "." (fieldIdx "2")) [(Term.anonymousCtor "⟨" [`hm "," `rfl] "⟩")])]
              "⟩")]))))]
       "⟩")))])
  []]
 ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `card
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `congr_argₓ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_=_» (Term.hole "_") "=" (Term.proj (Term.app `range [`n]) "." `card))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.proj (Term.app `range [`n]) "." `card)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `range [`n])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `range
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `range [`n]) []] ")")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'calcStep', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
  (Term.proj
   (Term.app
    `card_bUnion
    [(Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(group
          (Tactic.«tactic_<;>_»
           (Tactic.intros "intros" [])
           "<;>"
           (Tactic.«tactic_<;>_»
            (Tactic.apply "apply" (Term.proj `disjoint_filter "." (fieldIdx "2")))
            "<;>"
            (Tactic.cc "cc")))
          [])])))])
   "."
   `symm)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app
   `card_bUnion
   [(Term.byTactic
     "by"
     (Tactic.tacticSeq
      (Tactic.tacticSeq1Indented
       [(group
         (Tactic.«tactic_<;>_»
          (Tactic.intros "intros" [])
          "<;>"
          (Tactic.«tactic_<;>_»
           (Tactic.apply "apply" (Term.proj `disjoint_filter "." (fieldIdx "2")))
           "<;>"
           (Tactic.cc "cc")))
         [])])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.«tactic_<;>_»
        (Tactic.intros "intros" [])
        "<;>"
        (Tactic.«tactic_<;>_»
         (Tactic.apply "apply" (Term.proj `disjoint_filter "." (fieldIdx "2")))
         "<;>"
         (Tactic.cc "cc")))
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.«tactic_<;>_»
   (Tactic.intros "intros" [])
   "<;>"
   (Tactic.«tactic_<;>_» (Tactic.apply "apply" (Term.proj `disjoint_filter "." (fieldIdx "2"))) "<;>" (Tactic.cc "cc")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.«tactic_<;>_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.«tactic_<;>_» (Tactic.apply "apply" (Term.proj `disjoint_filter "." (fieldIdx "2"))) "<;>" (Tactic.cc "cc"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.«tactic_<;>_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.cc "cc")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.cc', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
  (Tactic.apply "apply" (Term.proj `disjoint_filter "." (fieldIdx "2")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.apply', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.proj `disjoint_filter "." (fieldIdx "2"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `disjoint_filter
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
  (Tactic.intros "intros" [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.intros', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.«tactic_<;>_»
        (Tactic.intros "intros" [])
        "<;>"
        (Tactic.«tactic_<;>_»
         (Tactic.apply "apply" (Term.proj `disjoint_filter "." (fieldIdx "2")))
         "<;>"
         (Tactic.cc "cc")))
       [])])))
  []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `card_bUnion
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app
   `card_bUnion
   [(Term.paren
     "("
     [(Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(group
           (Tactic.«tactic_<;>_»
            (Tactic.intros "intros" [])
            "<;>"
            (Tactic.«tactic_<;>_»
             (Tactic.apply "apply" (Term.proj `disjoint_filter "." (fieldIdx "2")))
             "<;>"
             (Tactic.cc "cc")))
           [])])))
      []]
     ")")])
  []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_=_»
   (Term.hole "_")
   "="
   (Term.proj
    (Term.app
     (Term.proj
      (Term.app `filter [(Init.Core.«term_∣_» (Term.cdot "·") " ∣ " `n) (Term.app `range [`n.succ])])
      "."
      `bUnion)
     [(Term.fun
       "fun"
       (Term.basicFun
        [(Term.simpleBinder [`d] [])]
        "=>"
        (Term.app
         (Term.proj (Term.app `range [`n]) "." `filter)
         [(Term.fun
           "fun"
           (Term.basicFun [(Term.simpleBinder [`m] [])] "=>" («term_=_» (Term.app `gcd [`n `m]) "=" `d)))])))])
    "."
    `card))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.proj
   (Term.app
    (Term.proj
     (Term.app `filter [(Init.Core.«term_∣_» (Term.cdot "·") " ∣ " `n) (Term.app `range [`n.succ])])
     "."
     `bUnion)
    [(Term.fun
      "fun"
      (Term.basicFun
       [(Term.simpleBinder [`d] [])]
       "=>"
       (Term.app
        (Term.proj (Term.app `range [`n]) "." `filter)
        [(Term.fun
          "fun"
          (Term.basicFun [(Term.simpleBinder [`m] [])] "=>" («term_=_» (Term.app `gcd [`n `m]) "=" `d)))])))])
   "."
   `card)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app
   (Term.proj
    (Term.app `filter [(Init.Core.«term_∣_» (Term.cdot "·") " ∣ " `n) (Term.app `range [`n.succ])])
    "."
    `bUnion)
   [(Term.fun
     "fun"
     (Term.basicFun
      [(Term.simpleBinder [`d] [])]
      "=>"
      (Term.app
       (Term.proj (Term.app `range [`n]) "." `filter)
       [(Term.fun
         "fun"
         (Term.basicFun [(Term.simpleBinder [`m] [])] "=>" («term_=_» (Term.app `gcd [`n `m]) "=" `d)))])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [`d] [])]
    "=>"
    (Term.app
     (Term.proj (Term.app `range [`n]) "." `filter)
     [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`m] [])] "=>" («term_=_» (Term.app `gcd [`n `m]) "=" `d)))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   (Term.proj (Term.app `range [`n]) "." `filter)
   [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`m] [])] "=>" («term_=_» (Term.app `gcd [`n `m]) "=" `d)))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`m] [])] "=>" («term_=_» (Term.app `gcd [`n `m]) "=" `d)))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_=_» (Term.app `gcd [`n `m]) "=" `d)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `d
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Term.app `gcd [`n `m])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `m
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `gcd
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
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
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.proj (Term.app `range [`n]) "." `filter)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `range [`n])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `range
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `range [`n]) []] ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
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
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.proj
   (Term.app `filter [(Init.Core.«term_∣_» (Term.cdot "·") " ∣ " `n) (Term.app `range [`n.succ])])
   "."
   `bUnion)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `filter [(Init.Core.«term_∣_» (Term.cdot "·") " ∣ " `n) (Term.app `range [`n.succ])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `range [`n.succ])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `n.succ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `range
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `range [`n.succ]) []] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Core.«term_∣_»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Core.«term_∣_»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Core.«term_∣_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Core.«term_∣_»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Core.«term_∣_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Init.Core.«term_∣_» (Term.cdot "·") " ∣ " `n)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Core.«term_∣_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Term.cdot "·")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.cdot', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.cdot', expected 'Lean.Parser.Term.cdot.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 50 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 50, (some 51, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Init.Core.«term_∣_» (Term.cdot "·") " ∣ " `n) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `filter
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app
   `filter
   [(Term.paren "(" [(Init.Core.«term_∣_» (Term.cdot "·") " ∣ " `n) []] ")")
    (Term.paren "(" [(Term.app `range [`n.succ]) []] ")")])
  []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app
   (Term.proj
    (Term.paren
     "("
     [(Term.app
       `filter
       [(Term.paren "(" [(Init.Core.«term_∣_» (Term.cdot "·") " ∣ " `n) []] ")")
        (Term.paren "(" [(Term.app `range [`n.succ]) []] ")")])
      []]
     ")")
    "."
    `bUnion)
   [(Term.fun
     "fun"
     (Term.basicFun
      [(Term.simpleBinder [`d] [])]
      "=>"
      (Term.app
       (Term.proj (Term.paren "(" [(Term.app `range [`n]) []] ")") "." `filter)
       [(Term.fun
         "fun"
         (Term.basicFun [(Term.simpleBinder [`m] [])] "=>" («term_=_» (Term.app `gcd [`n `m]) "=" `d)))])))])
  []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'calcStep', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
  (Term.app
   `sum_congr
   [`rfl
    (Term.fun
     "fun"
     (Term.basicFun
      [(Term.simpleBinder [`d `hd] [])]
      "=>"
      (Term.have
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`hd []]
         [(Term.typeSpec ":" (Init.Core.«term_∣_» `d " ∣ " `n))]
         ":="
         (Term.proj (Term.app (Term.proj `mem_filter "." (fieldIdx "1")) [`hd]) "." (fieldIdx "2"))))
       []
       (Term.have
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`hd0 []]
          [(Term.typeSpec ":" («term_<_» (numLit "0") "<" `d))]
          ":="
          (Term.app
           `Nat.pos_of_ne_zeroₓ
           [(Term.fun
             "fun"
             (Term.basicFun
              [(Term.simpleBinder [`h] [])]
              "=>"
              (Term.app `hn0 [(«term_$__» `eq_zero_of_zero_dvd "$" (Term.subst `h "▸" [`hd]))])))])))
        []
        (Term.app
         `card_congr
         [(Term.fun
           "fun"
           (Term.basicFun [(Term.simpleBinder [`m `hm] [])] "=>" (Finset.Data.Finset.Fold.«term_*_» `d "*" `m)))
          (Term.fun
           "fun"
           (Term.basicFun
            [(Term.simpleBinder [`m `hm] [])]
            "=>"
            (Term.have
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               [`hm []]
               [(Term.typeSpec
                 ":"
                 («term_∧_»
                  («term_<_» `m "<" («term_/_» `n "/" `d))
                  "∧"
                  («term_=_» (Term.app `gcd [(«term_/_» `n "/" `d) `m]) "=" (numLit "1"))))]
               ":="
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented [(group (Tactic.simpa "simpa" [] [] [] [] ["using" `hm]) [])])))))
             []
             (Term.app
              (Term.proj `mem_filter "." (fieldIdx "2"))
              [(Term.anonymousCtor
                "⟨"
                [(«term_$__»
                  (Term.proj `mem_range "." (fieldIdx "2"))
                  "$"
                  (Term.subst
                   (Term.app `Nat.mul_div_cancel'ₓ [`hd])
                   "▸"
                   [(Term.app
                     (Term.proj (Term.app `mul_lt_mul_left [`hd0]) "." (fieldIdx "2"))
                     [(Term.proj `hm "." (fieldIdx "1"))])]))
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
                        [(Tactic.rwRule ["←"] (Term.app `Nat.mul_div_cancel'ₓ [`hd]))
                         ","
                         (Tactic.rwRule [] `gcd_mul_left)
                         ","
                         (Tactic.rwRule [] (Term.proj `hm "." (fieldIdx "2")))
                         ","
                         (Tactic.rwRule [] `mul_oneₓ)]
                        "]")
                       [])
                      [])])))]
                "⟩")]))))
          (Term.fun
           "fun"
           (Term.basicFun
            [(Term.simpleBinder [`a `b `ha `hb `h] [])]
            "=>"
            (Term.app (Term.proj (Term.app `Nat.mul_right_inj [`hd0]) "." (fieldIdx "1")) [`h])))
          (Term.fun
           "fun"
           (Term.basicFun
            [(Term.simpleBinder [`b `hb] [])]
            "=>"
            (Term.have
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               [`hb []]
               [(Term.typeSpec ":" («term_∧_» («term_<_» `b "<" `n) "∧" («term_=_» (Term.app `gcd [`n `b]) "=" `d)))]
               ":="
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented [(group (Tactic.simpa "simpa" [] [] [] [] ["using" `hb]) [])])))))
             []
             (Term.anonymousCtor
              "⟨"
              [(«term_/_» `b "/" `d)
               ","
               (Term.app
                (Term.proj `mem_filter "." (fieldIdx "2"))
                [(Term.anonymousCtor
                  "⟨"
                  [(Term.app
                    (Term.proj `mem_range "." (fieldIdx "2"))
                    [(Term.app
                      (Term.proj
                       (Term.app
                        `mul_lt_mul_left
                        [(Term.show
                          "show"
                          («term_<_» (numLit "0") "<" `d)
                          (Term.fromTerm
                           "from"
                           (Term.subst
                            (Term.proj `hb "." (fieldIdx "2"))
                            "▸"
                            [(Term.subst (Term.proj (Term.proj `hb "." (fieldIdx "2")) "." `symm) "▸" [`hd0])])))])
                       "."
                       (fieldIdx "1"))
                      [(Term.byTactic
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
                               [(Tactic.rwRule ["←"] (Term.proj `hb "." (fieldIdx "2")))
                                ","
                                (Tactic.rwRule
                                 []
                                 (Term.app
                                  `Nat.mul_div_cancel'ₓ
                                  [(Term.app `gcd_dvd_left [(Term.hole "_") (Term.hole "_")])]))
                                ","
                                (Tactic.rwRule
                                 []
                                 (Term.app
                                  `Nat.mul_div_cancel'ₓ
                                  [(Term.app `gcd_dvd_right [(Term.hole "_") (Term.hole "_")])]))]
                               "]")
                              [])
                             "<;>"
                             (Tactic.exact "exact" (Term.proj `hb "." (fieldIdx "1"))))
                            [])])))])])
                   ","
                   (Term.subst
                    (Term.proj `hb "." (fieldIdx "2"))
                    "▸"
                    [(Term.app
                      `coprime_div_gcd_div_gcd
                      [(Term.subst (Term.proj (Term.proj `hb "." (fieldIdx "2")) "." `symm) "▸" [`hd0])])])]
                  "⟩")])
               ","
               (Term.subst
                (Term.proj `hb "." (fieldIdx "2"))
                "▸"
                [(Term.app `Nat.mul_div_cancel'ₓ [(Term.app `gcd_dvd_right [(Term.hole "_") (Term.hole "_")])])])]
              "⟩"))))])))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [`d `hd] [])]
    "=>"
    (Term.have
     "have"
     (Term.haveDecl
      (Term.haveIdDecl
       [`hd []]
       [(Term.typeSpec ":" (Init.Core.«term_∣_» `d " ∣ " `n))]
       ":="
       (Term.proj (Term.app (Term.proj `mem_filter "." (fieldIdx "1")) [`hd]) "." (fieldIdx "2"))))
     []
     (Term.have
      "have"
      (Term.haveDecl
       (Term.haveIdDecl
        [`hd0 []]
        [(Term.typeSpec ":" («term_<_» (numLit "0") "<" `d))]
        ":="
        (Term.app
         `Nat.pos_of_ne_zeroₓ
         [(Term.fun
           "fun"
           (Term.basicFun
            [(Term.simpleBinder [`h] [])]
            "=>"
            (Term.app `hn0 [(«term_$__» `eq_zero_of_zero_dvd "$" (Term.subst `h "▸" [`hd]))])))])))
      []
      (Term.app
       `card_congr
       [(Term.fun
         "fun"
         (Term.basicFun [(Term.simpleBinder [`m `hm] [])] "=>" (Finset.Data.Finset.Fold.«term_*_» `d "*" `m)))
        (Term.fun
         "fun"
         (Term.basicFun
          [(Term.simpleBinder [`m `hm] [])]
          "=>"
          (Term.have
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`hm []]
             [(Term.typeSpec
               ":"
               («term_∧_»
                («term_<_» `m "<" («term_/_» `n "/" `d))
                "∧"
                («term_=_» (Term.app `gcd [(«term_/_» `n "/" `d) `m]) "=" (numLit "1"))))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented [(group (Tactic.simpa "simpa" [] [] [] [] ["using" `hm]) [])])))))
           []
           (Term.app
            (Term.proj `mem_filter "." (fieldIdx "2"))
            [(Term.anonymousCtor
              "⟨"
              [(«term_$__»
                (Term.proj `mem_range "." (fieldIdx "2"))
                "$"
                (Term.subst
                 (Term.app `Nat.mul_div_cancel'ₓ [`hd])
                 "▸"
                 [(Term.app
                   (Term.proj (Term.app `mul_lt_mul_left [`hd0]) "." (fieldIdx "2"))
                   [(Term.proj `hm "." (fieldIdx "1"))])]))
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
                      [(Tactic.rwRule ["←"] (Term.app `Nat.mul_div_cancel'ₓ [`hd]))
                       ","
                       (Tactic.rwRule [] `gcd_mul_left)
                       ","
                       (Tactic.rwRule [] (Term.proj `hm "." (fieldIdx "2")))
                       ","
                       (Tactic.rwRule [] `mul_oneₓ)]
                      "]")
                     [])
                    [])])))]
              "⟩")]))))
        (Term.fun
         "fun"
         (Term.basicFun
          [(Term.simpleBinder [`a `b `ha `hb `h] [])]
          "=>"
          (Term.app (Term.proj (Term.app `Nat.mul_right_inj [`hd0]) "." (fieldIdx "1")) [`h])))
        (Term.fun
         "fun"
         (Term.basicFun
          [(Term.simpleBinder [`b `hb] [])]
          "=>"
          (Term.have
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`hb []]
             [(Term.typeSpec ":" («term_∧_» («term_<_» `b "<" `n) "∧" («term_=_» (Term.app `gcd [`n `b]) "=" `d)))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented [(group (Tactic.simpa "simpa" [] [] [] [] ["using" `hb]) [])])))))
           []
           (Term.anonymousCtor
            "⟨"
            [(«term_/_» `b "/" `d)
             ","
             (Term.app
              (Term.proj `mem_filter "." (fieldIdx "2"))
              [(Term.anonymousCtor
                "⟨"
                [(Term.app
                  (Term.proj `mem_range "." (fieldIdx "2"))
                  [(Term.app
                    (Term.proj
                     (Term.app
                      `mul_lt_mul_left
                      [(Term.show
                        "show"
                        («term_<_» (numLit "0") "<" `d)
                        (Term.fromTerm
                         "from"
                         (Term.subst
                          (Term.proj `hb "." (fieldIdx "2"))
                          "▸"
                          [(Term.subst (Term.proj (Term.proj `hb "." (fieldIdx "2")) "." `symm) "▸" [`hd0])])))])
                     "."
                     (fieldIdx "1"))
                    [(Term.byTactic
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
                             [(Tactic.rwRule ["←"] (Term.proj `hb "." (fieldIdx "2")))
                              ","
                              (Tactic.rwRule
                               []
                               (Term.app
                                `Nat.mul_div_cancel'ₓ
                                [(Term.app `gcd_dvd_left [(Term.hole "_") (Term.hole "_")])]))
                              ","
                              (Tactic.rwRule
                               []
                               (Term.app
                                `Nat.mul_div_cancel'ₓ
                                [(Term.app `gcd_dvd_right [(Term.hole "_") (Term.hole "_")])]))]
                             "]")
                            [])
                           "<;>"
                           (Tactic.exact "exact" (Term.proj `hb "." (fieldIdx "1"))))
                          [])])))])])
                 ","
                 (Term.subst
                  (Term.proj `hb "." (fieldIdx "2"))
                  "▸"
                  [(Term.app
                    `coprime_div_gcd_div_gcd
                    [(Term.subst (Term.proj (Term.proj `hb "." (fieldIdx "2")) "." `symm) "▸" [`hd0])])])]
                "⟩")])
             ","
             (Term.subst
              (Term.proj `hb "." (fieldIdx "2"))
              "▸"
              [(Term.app `Nat.mul_div_cancel'ₓ [(Term.app `gcd_dvd_right [(Term.hole "_") (Term.hole "_")])])])]
            "⟩"))))])))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.have
   "have"
   (Term.haveDecl
    (Term.haveIdDecl
     [`hd []]
     [(Term.typeSpec ":" (Init.Core.«term_∣_» `d " ∣ " `n))]
     ":="
     (Term.proj (Term.app (Term.proj `mem_filter "." (fieldIdx "1")) [`hd]) "." (fieldIdx "2"))))
   []
   (Term.have
    "have"
    (Term.haveDecl
     (Term.haveIdDecl
      [`hd0 []]
      [(Term.typeSpec ":" («term_<_» (numLit "0") "<" `d))]
      ":="
      (Term.app
       `Nat.pos_of_ne_zeroₓ
       [(Term.fun
         "fun"
         (Term.basicFun
          [(Term.simpleBinder [`h] [])]
          "=>"
          (Term.app `hn0 [(«term_$__» `eq_zero_of_zero_dvd "$" (Term.subst `h "▸" [`hd]))])))])))
    []
    (Term.app
     `card_congr
     [(Term.fun
       "fun"
       (Term.basicFun [(Term.simpleBinder [`m `hm] [])] "=>" (Finset.Data.Finset.Fold.«term_*_» `d "*" `m)))
      (Term.fun
       "fun"
       (Term.basicFun
        [(Term.simpleBinder [`m `hm] [])]
        "=>"
        (Term.have
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`hm []]
           [(Term.typeSpec
             ":"
             («term_∧_»
              («term_<_» `m "<" («term_/_» `n "/" `d))
              "∧"
              («term_=_» (Term.app `gcd [(«term_/_» `n "/" `d) `m]) "=" (numLit "1"))))]
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented [(group (Tactic.simpa "simpa" [] [] [] [] ["using" `hm]) [])])))))
         []
         (Term.app
          (Term.proj `mem_filter "." (fieldIdx "2"))
          [(Term.anonymousCtor
            "⟨"
            [(«term_$__»
              (Term.proj `mem_range "." (fieldIdx "2"))
              "$"
              (Term.subst
               (Term.app `Nat.mul_div_cancel'ₓ [`hd])
               "▸"
               [(Term.app
                 (Term.proj (Term.app `mul_lt_mul_left [`hd0]) "." (fieldIdx "2"))
                 [(Term.proj `hm "." (fieldIdx "1"))])]))
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
                    [(Tactic.rwRule ["←"] (Term.app `Nat.mul_div_cancel'ₓ [`hd]))
                     ","
                     (Tactic.rwRule [] `gcd_mul_left)
                     ","
                     (Tactic.rwRule [] (Term.proj `hm "." (fieldIdx "2")))
                     ","
                     (Tactic.rwRule [] `mul_oneₓ)]
                    "]")
                   [])
                  [])])))]
            "⟩")]))))
      (Term.fun
       "fun"
       (Term.basicFun
        [(Term.simpleBinder [`a `b `ha `hb `h] [])]
        "=>"
        (Term.app (Term.proj (Term.app `Nat.mul_right_inj [`hd0]) "." (fieldIdx "1")) [`h])))
      (Term.fun
       "fun"
       (Term.basicFun
        [(Term.simpleBinder [`b `hb] [])]
        "=>"
        (Term.have
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`hb []]
           [(Term.typeSpec ":" («term_∧_» («term_<_» `b "<" `n) "∧" («term_=_» (Term.app `gcd [`n `b]) "=" `d)))]
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented [(group (Tactic.simpa "simpa" [] [] [] [] ["using" `hb]) [])])))))
         []
         (Term.anonymousCtor
          "⟨"
          [(«term_/_» `b "/" `d)
           ","
           (Term.app
            (Term.proj `mem_filter "." (fieldIdx "2"))
            [(Term.anonymousCtor
              "⟨"
              [(Term.app
                (Term.proj `mem_range "." (fieldIdx "2"))
                [(Term.app
                  (Term.proj
                   (Term.app
                    `mul_lt_mul_left
                    [(Term.show
                      "show"
                      («term_<_» (numLit "0") "<" `d)
                      (Term.fromTerm
                       "from"
                       (Term.subst
                        (Term.proj `hb "." (fieldIdx "2"))
                        "▸"
                        [(Term.subst (Term.proj (Term.proj `hb "." (fieldIdx "2")) "." `symm) "▸" [`hd0])])))])
                   "."
                   (fieldIdx "1"))
                  [(Term.byTactic
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
                           [(Tactic.rwRule ["←"] (Term.proj `hb "." (fieldIdx "2")))
                            ","
                            (Tactic.rwRule
                             []
                             (Term.app
                              `Nat.mul_div_cancel'ₓ
                              [(Term.app `gcd_dvd_left [(Term.hole "_") (Term.hole "_")])]))
                            ","
                            (Tactic.rwRule
                             []
                             (Term.app
                              `Nat.mul_div_cancel'ₓ
                              [(Term.app `gcd_dvd_right [(Term.hole "_") (Term.hole "_")])]))]
                           "]")
                          [])
                         "<;>"
                         (Tactic.exact "exact" (Term.proj `hb "." (fieldIdx "1"))))
                        [])])))])])
               ","
               (Term.subst
                (Term.proj `hb "." (fieldIdx "2"))
                "▸"
                [(Term.app
                  `coprime_div_gcd_div_gcd
                  [(Term.subst (Term.proj (Term.proj `hb "." (fieldIdx "2")) "." `symm) "▸" [`hd0])])])]
              "⟩")])
           ","
           (Term.subst
            (Term.proj `hb "." (fieldIdx "2"))
            "▸"
            [(Term.app `Nat.mul_div_cancel'ₓ [(Term.app `gcd_dvd_right [(Term.hole "_") (Term.hole "_")])])])]
          "⟩"))))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.have', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.have', expected 'Lean.Parser.Term.have.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.have
   "have"
   (Term.haveDecl
    (Term.haveIdDecl
     [`hd0 []]
     [(Term.typeSpec ":" («term_<_» (numLit "0") "<" `d))]
     ":="
     (Term.app
      `Nat.pos_of_ne_zeroₓ
      [(Term.fun
        "fun"
        (Term.basicFun
         [(Term.simpleBinder [`h] [])]
         "=>"
         (Term.app `hn0 [(«term_$__» `eq_zero_of_zero_dvd "$" (Term.subst `h "▸" [`hd]))])))])))
   []
   (Term.app
    `card_congr
    [(Term.fun
      "fun"
      (Term.basicFun [(Term.simpleBinder [`m `hm] [])] "=>" (Finset.Data.Finset.Fold.«term_*_» `d "*" `m)))
     (Term.fun
      "fun"
      (Term.basicFun
       [(Term.simpleBinder [`m `hm] [])]
       "=>"
       (Term.have
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`hm []]
          [(Term.typeSpec
            ":"
            («term_∧_»
             («term_<_» `m "<" («term_/_» `n "/" `d))
             "∧"
             («term_=_» (Term.app `gcd [(«term_/_» `n "/" `d) `m]) "=" (numLit "1"))))]
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented [(group (Tactic.simpa "simpa" [] [] [] [] ["using" `hm]) [])])))))
        []
        (Term.app
         (Term.proj `mem_filter "." (fieldIdx "2"))
         [(Term.anonymousCtor
           "⟨"
           [(«term_$__»
             (Term.proj `mem_range "." (fieldIdx "2"))
             "$"
             (Term.subst
              (Term.app `Nat.mul_div_cancel'ₓ [`hd])
              "▸"
              [(Term.app
                (Term.proj (Term.app `mul_lt_mul_left [`hd0]) "." (fieldIdx "2"))
                [(Term.proj `hm "." (fieldIdx "1"))])]))
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
                   [(Tactic.rwRule ["←"] (Term.app `Nat.mul_div_cancel'ₓ [`hd]))
                    ","
                    (Tactic.rwRule [] `gcd_mul_left)
                    ","
                    (Tactic.rwRule [] (Term.proj `hm "." (fieldIdx "2")))
                    ","
                    (Tactic.rwRule [] `mul_oneₓ)]
                   "]")
                  [])
                 [])])))]
           "⟩")]))))
     (Term.fun
      "fun"
      (Term.basicFun
       [(Term.simpleBinder [`a `b `ha `hb `h] [])]
       "=>"
       (Term.app (Term.proj (Term.app `Nat.mul_right_inj [`hd0]) "." (fieldIdx "1")) [`h])))
     (Term.fun
      "fun"
      (Term.basicFun
       [(Term.simpleBinder [`b `hb] [])]
       "=>"
       (Term.have
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`hb []]
          [(Term.typeSpec ":" («term_∧_» («term_<_» `b "<" `n) "∧" («term_=_» (Term.app `gcd [`n `b]) "=" `d)))]
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented [(group (Tactic.simpa "simpa" [] [] [] [] ["using" `hb]) [])])))))
        []
        (Term.anonymousCtor
         "⟨"
         [(«term_/_» `b "/" `d)
          ","
          (Term.app
           (Term.proj `mem_filter "." (fieldIdx "2"))
           [(Term.anonymousCtor
             "⟨"
             [(Term.app
               (Term.proj `mem_range "." (fieldIdx "2"))
               [(Term.app
                 (Term.proj
                  (Term.app
                   `mul_lt_mul_left
                   [(Term.show
                     "show"
                     («term_<_» (numLit "0") "<" `d)
                     (Term.fromTerm
                      "from"
                      (Term.subst
                       (Term.proj `hb "." (fieldIdx "2"))
                       "▸"
                       [(Term.subst (Term.proj (Term.proj `hb "." (fieldIdx "2")) "." `symm) "▸" [`hd0])])))])
                  "."
                  (fieldIdx "1"))
                 [(Term.byTactic
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
                          [(Tactic.rwRule ["←"] (Term.proj `hb "." (fieldIdx "2")))
                           ","
                           (Tactic.rwRule
                            []
                            (Term.app
                             `Nat.mul_div_cancel'ₓ
                             [(Term.app `gcd_dvd_left [(Term.hole "_") (Term.hole "_")])]))
                           ","
                           (Tactic.rwRule
                            []
                            (Term.app
                             `Nat.mul_div_cancel'ₓ
                             [(Term.app `gcd_dvd_right [(Term.hole "_") (Term.hole "_")])]))]
                          "]")
                         [])
                        "<;>"
                        (Tactic.exact "exact" (Term.proj `hb "." (fieldIdx "1"))))
                       [])])))])])
              ","
              (Term.subst
               (Term.proj `hb "." (fieldIdx "2"))
               "▸"
               [(Term.app
                 `coprime_div_gcd_div_gcd
                 [(Term.subst (Term.proj (Term.proj `hb "." (fieldIdx "2")) "." `symm) "▸" [`hd0])])])]
             "⟩")])
          ","
          (Term.subst
           (Term.proj `hb "." (fieldIdx "2"))
           "▸"
           [(Term.app `Nat.mul_div_cancel'ₓ [(Term.app `gcd_dvd_right [(Term.hole "_") (Term.hole "_")])])])]
         "⟩"))))]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.have', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.have', expected 'Lean.Parser.Term.have.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `card_congr
   [(Term.fun
     "fun"
     (Term.basicFun [(Term.simpleBinder [`m `hm] [])] "=>" (Finset.Data.Finset.Fold.«term_*_» `d "*" `m)))
    (Term.fun
     "fun"
     (Term.basicFun
      [(Term.simpleBinder [`m `hm] [])]
      "=>"
      (Term.have
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`hm []]
         [(Term.typeSpec
           ":"
           («term_∧_»
            («term_<_» `m "<" («term_/_» `n "/" `d))
            "∧"
            («term_=_» (Term.app `gcd [(«term_/_» `n "/" `d) `m]) "=" (numLit "1"))))]
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented [(group (Tactic.simpa "simpa" [] [] [] [] ["using" `hm]) [])])))))
       []
       (Term.app
        (Term.proj `mem_filter "." (fieldIdx "2"))
        [(Term.anonymousCtor
          "⟨"
          [(«term_$__»
            (Term.proj `mem_range "." (fieldIdx "2"))
            "$"
            (Term.subst
             (Term.app `Nat.mul_div_cancel'ₓ [`hd])
             "▸"
             [(Term.app
               (Term.proj (Term.app `mul_lt_mul_left [`hd0]) "." (fieldIdx "2"))
               [(Term.proj `hm "." (fieldIdx "1"))])]))
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
                  [(Tactic.rwRule ["←"] (Term.app `Nat.mul_div_cancel'ₓ [`hd]))
                   ","
                   (Tactic.rwRule [] `gcd_mul_left)
                   ","
                   (Tactic.rwRule [] (Term.proj `hm "." (fieldIdx "2")))
                   ","
                   (Tactic.rwRule [] `mul_oneₓ)]
                  "]")
                 [])
                [])])))]
          "⟩")]))))
    (Term.fun
     "fun"
     (Term.basicFun
      [(Term.simpleBinder [`a `b `ha `hb `h] [])]
      "=>"
      (Term.app (Term.proj (Term.app `Nat.mul_right_inj [`hd0]) "." (fieldIdx "1")) [`h])))
    (Term.fun
     "fun"
     (Term.basicFun
      [(Term.simpleBinder [`b `hb] [])]
      "=>"
      (Term.have
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`hb []]
         [(Term.typeSpec ":" («term_∧_» («term_<_» `b "<" `n) "∧" («term_=_» (Term.app `gcd [`n `b]) "=" `d)))]
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented [(group (Tactic.simpa "simpa" [] [] [] [] ["using" `hb]) [])])))))
       []
       (Term.anonymousCtor
        "⟨"
        [(«term_/_» `b "/" `d)
         ","
         (Term.app
          (Term.proj `mem_filter "." (fieldIdx "2"))
          [(Term.anonymousCtor
            "⟨"
            [(Term.app
              (Term.proj `mem_range "." (fieldIdx "2"))
              [(Term.app
                (Term.proj
                 (Term.app
                  `mul_lt_mul_left
                  [(Term.show
                    "show"
                    («term_<_» (numLit "0") "<" `d)
                    (Term.fromTerm
                     "from"
                     (Term.subst
                      (Term.proj `hb "." (fieldIdx "2"))
                      "▸"
                      [(Term.subst (Term.proj (Term.proj `hb "." (fieldIdx "2")) "." `symm) "▸" [`hd0])])))])
                 "."
                 (fieldIdx "1"))
                [(Term.byTactic
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
                         [(Tactic.rwRule ["←"] (Term.proj `hb "." (fieldIdx "2")))
                          ","
                          (Tactic.rwRule
                           []
                           (Term.app
                            `Nat.mul_div_cancel'ₓ
                            [(Term.app `gcd_dvd_left [(Term.hole "_") (Term.hole "_")])]))
                          ","
                          (Tactic.rwRule
                           []
                           (Term.app
                            `Nat.mul_div_cancel'ₓ
                            [(Term.app `gcd_dvd_right [(Term.hole "_") (Term.hole "_")])]))]
                         "]")
                        [])
                       "<;>"
                       (Tactic.exact "exact" (Term.proj `hb "." (fieldIdx "1"))))
                      [])])))])])
             ","
             (Term.subst
              (Term.proj `hb "." (fieldIdx "2"))
              "▸"
              [(Term.app
                `coprime_div_gcd_div_gcd
                [(Term.subst (Term.proj (Term.proj `hb "." (fieldIdx "2")) "." `symm) "▸" [`hd0])])])]
            "⟩")])
         ","
         (Term.subst
          (Term.proj `hb "." (fieldIdx "2"))
          "▸"
          [(Term.app `Nat.mul_div_cancel'ₓ [(Term.app `gcd_dvd_right [(Term.hole "_") (Term.hole "_")])])])]
        "⟩"))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [`b `hb] [])]
    "=>"
    (Term.have
     "have"
     (Term.haveDecl
      (Term.haveIdDecl
       [`hb []]
       [(Term.typeSpec ":" («term_∧_» («term_<_» `b "<" `n) "∧" («term_=_» (Term.app `gcd [`n `b]) "=" `d)))]
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.simpa "simpa" [] [] [] [] ["using" `hb]) [])])))))
     []
     (Term.anonymousCtor
      "⟨"
      [(«term_/_» `b "/" `d)
       ","
       (Term.app
        (Term.proj `mem_filter "." (fieldIdx "2"))
        [(Term.anonymousCtor
          "⟨"
          [(Term.app
            (Term.proj `mem_range "." (fieldIdx "2"))
            [(Term.app
              (Term.proj
               (Term.app
                `mul_lt_mul_left
                [(Term.show
                  "show"
                  («term_<_» (numLit "0") "<" `d)
                  (Term.fromTerm
                   "from"
                   (Term.subst
                    (Term.proj `hb "." (fieldIdx "2"))
                    "▸"
                    [(Term.subst (Term.proj (Term.proj `hb "." (fieldIdx "2")) "." `symm) "▸" [`hd0])])))])
               "."
               (fieldIdx "1"))
              [(Term.byTactic
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
                       [(Tactic.rwRule ["←"] (Term.proj `hb "." (fieldIdx "2")))
                        ","
                        (Tactic.rwRule
                         []
                         (Term.app `Nat.mul_div_cancel'ₓ [(Term.app `gcd_dvd_left [(Term.hole "_") (Term.hole "_")])]))
                        ","
                        (Tactic.rwRule
                         []
                         (Term.app
                          `Nat.mul_div_cancel'ₓ
                          [(Term.app `gcd_dvd_right [(Term.hole "_") (Term.hole "_")])]))]
                       "]")
                      [])
                     "<;>"
                     (Tactic.exact "exact" (Term.proj `hb "." (fieldIdx "1"))))
                    [])])))])])
           ","
           (Term.subst
            (Term.proj `hb "." (fieldIdx "2"))
            "▸"
            [(Term.app
              `coprime_div_gcd_div_gcd
              [(Term.subst (Term.proj (Term.proj `hb "." (fieldIdx "2")) "." `symm) "▸" [`hd0])])])]
          "⟩")])
       ","
       (Term.subst
        (Term.proj `hb "." (fieldIdx "2"))
        "▸"
        [(Term.app `Nat.mul_div_cancel'ₓ [(Term.app `gcd_dvd_right [(Term.hole "_") (Term.hole "_")])])])]
      "⟩"))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.have
   "have"
   (Term.haveDecl
    (Term.haveIdDecl
     [`hb []]
     [(Term.typeSpec ":" («term_∧_» («term_<_» `b "<" `n) "∧" («term_=_» (Term.app `gcd [`n `b]) "=" `d)))]
     ":="
     (Term.byTactic
      "by"
      (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.simpa "simpa" [] [] [] [] ["using" `hb]) [])])))))
   []
   (Term.anonymousCtor
    "⟨"
    [(«term_/_» `b "/" `d)
     ","
     (Term.app
      (Term.proj `mem_filter "." (fieldIdx "2"))
      [(Term.anonymousCtor
        "⟨"
        [(Term.app
          (Term.proj `mem_range "." (fieldIdx "2"))
          [(Term.app
            (Term.proj
             (Term.app
              `mul_lt_mul_left
              [(Term.show
                "show"
                («term_<_» (numLit "0") "<" `d)
                (Term.fromTerm
                 "from"
                 (Term.subst
                  (Term.proj `hb "." (fieldIdx "2"))
                  "▸"
                  [(Term.subst (Term.proj (Term.proj `hb "." (fieldIdx "2")) "." `symm) "▸" [`hd0])])))])
             "."
             (fieldIdx "1"))
            [(Term.byTactic
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
                     [(Tactic.rwRule ["←"] (Term.proj `hb "." (fieldIdx "2")))
                      ","
                      (Tactic.rwRule
                       []
                       (Term.app `Nat.mul_div_cancel'ₓ [(Term.app `gcd_dvd_left [(Term.hole "_") (Term.hole "_")])]))
                      ","
                      (Tactic.rwRule
                       []
                       (Term.app `Nat.mul_div_cancel'ₓ [(Term.app `gcd_dvd_right [(Term.hole "_") (Term.hole "_")])]))]
                     "]")
                    [])
                   "<;>"
                   (Tactic.exact "exact" (Term.proj `hb "." (fieldIdx "1"))))
                  [])])))])])
         ","
         (Term.subst
          (Term.proj `hb "." (fieldIdx "2"))
          "▸"
          [(Term.app
            `coprime_div_gcd_div_gcd
            [(Term.subst (Term.proj (Term.proj `hb "." (fieldIdx "2")) "." `symm) "▸" [`hd0])])])]
        "⟩")])
     ","
     (Term.subst
      (Term.proj `hb "." (fieldIdx "2"))
      "▸"
      [(Term.app `Nat.mul_div_cancel'ₓ [(Term.app `gcd_dvd_right [(Term.hole "_") (Term.hole "_")])])])]
    "⟩"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.have', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.have', expected 'Lean.Parser.Term.have.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor
   "⟨"
   [(«term_/_» `b "/" `d)
    ","
    (Term.app
     (Term.proj `mem_filter "." (fieldIdx "2"))
     [(Term.anonymousCtor
       "⟨"
       [(Term.app
         (Term.proj `mem_range "." (fieldIdx "2"))
         [(Term.app
           (Term.proj
            (Term.app
             `mul_lt_mul_left
             [(Term.show
               "show"
               («term_<_» (numLit "0") "<" `d)
               (Term.fromTerm
                "from"
                (Term.subst
                 (Term.proj `hb "." (fieldIdx "2"))
                 "▸"
                 [(Term.subst (Term.proj (Term.proj `hb "." (fieldIdx "2")) "." `symm) "▸" [`hd0])])))])
            "."
            (fieldIdx "1"))
           [(Term.byTactic
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
                    [(Tactic.rwRule ["←"] (Term.proj `hb "." (fieldIdx "2")))
                     ","
                     (Tactic.rwRule
                      []
                      (Term.app `Nat.mul_div_cancel'ₓ [(Term.app `gcd_dvd_left [(Term.hole "_") (Term.hole "_")])]))
                     ","
                     (Tactic.rwRule
                      []
                      (Term.app `Nat.mul_div_cancel'ₓ [(Term.app `gcd_dvd_right [(Term.hole "_") (Term.hole "_")])]))]
                    "]")
                   [])
                  "<;>"
                  (Tactic.exact "exact" (Term.proj `hb "." (fieldIdx "1"))))
                 [])])))])])
        ","
        (Term.subst
         (Term.proj `hb "." (fieldIdx "2"))
         "▸"
         [(Term.app
           `coprime_div_gcd_div_gcd
           [(Term.subst (Term.proj (Term.proj `hb "." (fieldIdx "2")) "." `symm) "▸" [`hd0])])])]
       "⟩")])
    ","
    (Term.subst
     (Term.proj `hb "." (fieldIdx "2"))
     "▸"
     [(Term.app `Nat.mul_div_cancel'ₓ [(Term.app `gcd_dvd_right [(Term.hole "_") (Term.hole "_")])])])]
   "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.subst', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.subst
   (Term.proj `hb "." (fieldIdx "2"))
   "▸"
   [(Term.app `Nat.mul_div_cancel'ₓ [(Term.app `gcd_dvd_right [(Term.hole "_") (Term.hole "_")])])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.subst', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Nat.mul_div_cancel'ₓ [(Term.app `gcd_dvd_right [(Term.hole "_") (Term.hole "_")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `gcd_dvd_right [(Term.hole "_") (Term.hole "_")])
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
  `gcd_dvd_right
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app `gcd_dvd_right [(Term.hole "_") (Term.hole "_")]) []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Nat.mul_div_cancel'ₓ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 75 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 75, term))
  (Term.proj `hb "." (fieldIdx "2"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `hb
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 75, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 75, (some 75, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   (Term.proj `mem_filter "." (fieldIdx "2"))
   [(Term.anonymousCtor
     "⟨"
     [(Term.app
       (Term.proj `mem_range "." (fieldIdx "2"))
       [(Term.app
         (Term.proj
          (Term.app
           `mul_lt_mul_left
           [(Term.show
             "show"
             («term_<_» (numLit "0") "<" `d)
             (Term.fromTerm
              "from"
              (Term.subst
               (Term.proj `hb "." (fieldIdx "2"))
               "▸"
               [(Term.subst (Term.proj (Term.proj `hb "." (fieldIdx "2")) "." `symm) "▸" [`hd0])])))])
          "."
          (fieldIdx "1"))
         [(Term.byTactic
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
                  [(Tactic.rwRule ["←"] (Term.proj `hb "." (fieldIdx "2")))
                   ","
                   (Tactic.rwRule
                    []
                    (Term.app `Nat.mul_div_cancel'ₓ [(Term.app `gcd_dvd_left [(Term.hole "_") (Term.hole "_")])]))
                   ","
                   (Tactic.rwRule
                    []
                    (Term.app `Nat.mul_div_cancel'ₓ [(Term.app `gcd_dvd_right [(Term.hole "_") (Term.hole "_")])]))]
                  "]")
                 [])
                "<;>"
                (Tactic.exact "exact" (Term.proj `hb "." (fieldIdx "1"))))
               [])])))])])
      ","
      (Term.subst
       (Term.proj `hb "." (fieldIdx "2"))
       "▸"
       [(Term.app
         `coprime_div_gcd_div_gcd
         [(Term.subst (Term.proj (Term.proj `hb "." (fieldIdx "2")) "." `symm) "▸" [`hd0])])])]
     "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor
   "⟨"
   [(Term.app
     (Term.proj `mem_range "." (fieldIdx "2"))
     [(Term.app
       (Term.proj
        (Term.app
         `mul_lt_mul_left
         [(Term.show
           "show"
           («term_<_» (numLit "0") "<" `d)
           (Term.fromTerm
            "from"
            (Term.subst
             (Term.proj `hb "." (fieldIdx "2"))
             "▸"
             [(Term.subst (Term.proj (Term.proj `hb "." (fieldIdx "2")) "." `symm) "▸" [`hd0])])))])
        "."
        (fieldIdx "1"))
       [(Term.byTactic
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
                [(Tactic.rwRule ["←"] (Term.proj `hb "." (fieldIdx "2")))
                 ","
                 (Tactic.rwRule
                  []
                  (Term.app `Nat.mul_div_cancel'ₓ [(Term.app `gcd_dvd_left [(Term.hole "_") (Term.hole "_")])]))
                 ","
                 (Tactic.rwRule
                  []
                  (Term.app `Nat.mul_div_cancel'ₓ [(Term.app `gcd_dvd_right [(Term.hole "_") (Term.hole "_")])]))]
                "]")
               [])
              "<;>"
              (Tactic.exact "exact" (Term.proj `hb "." (fieldIdx "1"))))
             [])])))])])
    ","
    (Term.subst
     (Term.proj `hb "." (fieldIdx "2"))
     "▸"
     [(Term.app
       `coprime_div_gcd_div_gcd
       [(Term.subst (Term.proj (Term.proj `hb "." (fieldIdx "2")) "." `symm) "▸" [`hd0])])])]
   "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.subst', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.subst
   (Term.proj `hb "." (fieldIdx "2"))
   "▸"
   [(Term.app
     `coprime_div_gcd_div_gcd
     [(Term.subst (Term.proj (Term.proj `hb "." (fieldIdx "2")) "." `symm) "▸" [`hd0])])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.subst', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `coprime_div_gcd_div_gcd [(Term.subst (Term.proj (Term.proj `hb "." (fieldIdx "2")) "." `symm) "▸" [`hd0])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.subst', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.subst', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.subst', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.subst', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.subst', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.subst (Term.proj (Term.proj `hb "." (fieldIdx "2")) "." `symm) "▸" [`hd0])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.subst', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hd0
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 75 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 75, term))
  (Term.proj (Term.proj `hb "." (fieldIdx "2")) "." `symm)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.proj `hb "." (fieldIdx "2"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `hb
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 75, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 75, (some 75, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.subst (Term.proj (Term.proj `hb "." (fieldIdx "2")) "." `symm) "▸" [`hd0]) []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `coprime_div_gcd_div_gcd
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 75 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 75, term))
  (Term.proj `hb "." (fieldIdx "2"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `hb
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 75, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 75, (some 75, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   (Term.proj `mem_range "." (fieldIdx "2"))
   [(Term.app
     (Term.proj
      (Term.app
       `mul_lt_mul_left
       [(Term.show
         "show"
         («term_<_» (numLit "0") "<" `d)
         (Term.fromTerm
          "from"
          (Term.subst
           (Term.proj `hb "." (fieldIdx "2"))
           "▸"
           [(Term.subst (Term.proj (Term.proj `hb "." (fieldIdx "2")) "." `symm) "▸" [`hd0])])))])
      "."
      (fieldIdx "1"))
     [(Term.byTactic
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
              [(Tactic.rwRule ["←"] (Term.proj `hb "." (fieldIdx "2")))
               ","
               (Tactic.rwRule
                []
                (Term.app `Nat.mul_div_cancel'ₓ [(Term.app `gcd_dvd_left [(Term.hole "_") (Term.hole "_")])]))
               ","
               (Tactic.rwRule
                []
                (Term.app `Nat.mul_div_cancel'ₓ [(Term.app `gcd_dvd_right [(Term.hole "_") (Term.hole "_")])]))]
              "]")
             [])
            "<;>"
            (Tactic.exact "exact" (Term.proj `hb "." (fieldIdx "1"))))
           [])])))])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   (Term.proj
    (Term.app
     `mul_lt_mul_left
     [(Term.show
       "show"
       («term_<_» (numLit "0") "<" `d)
       (Term.fromTerm
        "from"
        (Term.subst
         (Term.proj `hb "." (fieldIdx "2"))
         "▸"
         [(Term.subst (Term.proj (Term.proj `hb "." (fieldIdx "2")) "." `symm) "▸" [`hd0])])))])
    "."
    (fieldIdx "1"))
   [(Term.byTactic
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
            [(Tactic.rwRule ["←"] (Term.proj `hb "." (fieldIdx "2")))
             ","
             (Tactic.rwRule
              []
              (Term.app `Nat.mul_div_cancel'ₓ [(Term.app `gcd_dvd_left [(Term.hole "_") (Term.hole "_")])]))
             ","
             (Tactic.rwRule
              []
              (Term.app `Nat.mul_div_cancel'ₓ [(Term.app `gcd_dvd_right [(Term.hole "_") (Term.hole "_")])]))]
            "]")
           [])
          "<;>"
          (Tactic.exact "exact" (Term.proj `hb "." (fieldIdx "1"))))
         [])])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
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
          [(Tactic.rwRule ["←"] (Term.proj `hb "." (fieldIdx "2")))
           ","
           (Tactic.rwRule
            []
            (Term.app `Nat.mul_div_cancel'ₓ [(Term.app `gcd_dvd_left [(Term.hole "_") (Term.hole "_")])]))
           ","
           (Tactic.rwRule
            []
            (Term.app `Nat.mul_div_cancel'ₓ [(Term.app `gcd_dvd_right [(Term.hole "_") (Term.hole "_")])]))]
          "]")
         [])
        "<;>"
        (Tactic.exact "exact" (Term.proj `hb "." (fieldIdx "1"))))
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.«tactic_<;>_»
   (Tactic.rwSeq
    "rw"
    []
    (Tactic.rwRuleSeq
     "["
     [(Tactic.rwRule ["←"] (Term.proj `hb "." (fieldIdx "2")))
      ","
      (Tactic.rwRule [] (Term.app `Nat.mul_div_cancel'ₓ [(Term.app `gcd_dvd_left [(Term.hole "_") (Term.hole "_")])]))
      ","
      (Tactic.rwRule [] (Term.app `Nat.mul_div_cancel'ₓ [(Term.app `gcd_dvd_right [(Term.hole "_") (Term.hole "_")])]))]
     "]")
    [])
   "<;>"
   (Tactic.exact "exact" (Term.proj `hb "." (fieldIdx "1"))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.«tactic_<;>_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.exact "exact" (Term.proj `hb "." (fieldIdx "1")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.exact', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.proj `hb "." (fieldIdx "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `hb
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
  (Tactic.rwSeq
   "rw"
   []
   (Tactic.rwRuleSeq
    "["
    [(Tactic.rwRule ["←"] (Term.proj `hb "." (fieldIdx "2")))
     ","
     (Tactic.rwRule [] (Term.app `Nat.mul_div_cancel'ₓ [(Term.app `gcd_dvd_left [(Term.hole "_") (Term.hole "_")])]))
     ","
     (Tactic.rwRule [] (Term.app `Nat.mul_div_cancel'ₓ [(Term.app `gcd_dvd_right [(Term.hole "_") (Term.hole "_")])]))]
    "]")
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwSeq', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Nat.mul_div_cancel'ₓ [(Term.app `gcd_dvd_right [(Term.hole "_") (Term.hole "_")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `gcd_dvd_right [(Term.hole "_") (Term.hole "_")])
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
  `gcd_dvd_right
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app `gcd_dvd_right [(Term.hole "_") (Term.hole "_")]) []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Nat.mul_div_cancel'ₓ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Nat.mul_div_cancel'ₓ [(Term.app `gcd_dvd_left [(Term.hole "_") (Term.hole "_")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `gcd_dvd_left [(Term.hole "_") (Term.hole "_")])
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
  `gcd_dvd_left
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app `gcd_dvd_left [(Term.hole "_") (Term.hole "_")]) []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Nat.mul_div_cancel'ₓ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.proj `hb "." (fieldIdx "2"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `hb
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«←»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.byTactic
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
          [(Tactic.rwRule ["←"] (Term.proj `hb "." (fieldIdx "2")))
           ","
           (Tactic.rwRule
            []
            (Term.app
             `Nat.mul_div_cancel'ₓ
             [(Term.paren "(" [(Term.app `gcd_dvd_left [(Term.hole "_") (Term.hole "_")]) []] ")")]))
           ","
           (Tactic.rwRule
            []
            (Term.app
             `Nat.mul_div_cancel'ₓ
             [(Term.paren "(" [(Term.app `gcd_dvd_right [(Term.hole "_") (Term.hole "_")]) []] ")")]))]
          "]")
         [])
        "<;>"
        (Tactic.exact "exact" (Term.proj `hb "." (fieldIdx "1"))))
       [])])))
  []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.proj
   (Term.app
    `mul_lt_mul_left
    [(Term.show
      "show"
      («term_<_» (numLit "0") "<" `d)
      (Term.fromTerm
       "from"
       (Term.subst
        (Term.proj `hb "." (fieldIdx "2"))
        "▸"
        [(Term.subst (Term.proj (Term.proj `hb "." (fieldIdx "2")) "." `symm) "▸" [`hd0])])))])
   "."
   (fieldIdx "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app
   `mul_lt_mul_left
   [(Term.show
     "show"
     («term_<_» (numLit "0") "<" `d)
     (Term.fromTerm
      "from"
      (Term.subst
       (Term.proj `hb "." (fieldIdx "2"))
       "▸"
       [(Term.subst (Term.proj (Term.proj `hb "." (fieldIdx "2")) "." `symm) "▸" [`hd0])])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.show', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.show', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.show', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.show', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.show', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.show
   "show"
   («term_<_» (numLit "0") "<" `d)
   (Term.fromTerm
    "from"
    (Term.subst
     (Term.proj `hb "." (fieldIdx "2"))
     "▸"
     [(Term.subst (Term.proj (Term.proj `hb "." (fieldIdx "2")) "." `symm) "▸" [`hd0])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.show', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.show', expected 'Lean.Parser.Term.show.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fromTerm', expected 'Lean.Parser.Term.fromTerm.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.subst
   (Term.proj `hb "." (fieldIdx "2"))
   "▸"
   [(Term.subst (Term.proj (Term.proj `hb "." (fieldIdx "2")) "." `symm) "▸" [`hd0])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.subst', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.subst', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.subst (Term.proj (Term.proj `hb "." (fieldIdx "2")) "." `symm) "▸" [`hd0])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.subst', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hd0
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 75 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 75, term))
  (Term.proj (Term.proj `hb "." (fieldIdx "2")) "." `symm)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.proj `hb "." (fieldIdx "2"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `hb
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 75, term)
[PrettyPrinter.parenthesize] ...precedences are 75 >? 75, (some 75, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 75, term))
  (Term.proj `hb "." (fieldIdx "2"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `hb
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 75, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 75, (some 75, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  («term_<_» (numLit "0") "<" `d)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_<_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `d
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (numLit "0")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.show
   "show"
   («term_<_» (numLit "0") "<" `d)
   (Term.fromTerm
    "from"
    (Term.subst
     (Term.proj `hb "." (fieldIdx "2"))
     "▸"
     [(Term.subst (Term.proj (Term.proj `hb "." (fieldIdx "2")) "." `symm) "▸" [`hd0])])))
  []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `mul_lt_mul_left
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app
   `mul_lt_mul_left
   [(Term.paren
     "("
     [(Term.show
       "show"
       («term_<_» (numLit "0") "<" `d)
       (Term.fromTerm
        "from"
        (Term.subst
         (Term.proj `hb "." (fieldIdx "2"))
         "▸"
         [(Term.subst (Term.proj (Term.proj `hb "." (fieldIdx "2")) "." `symm) "▸" [`hd0])])))
      []]
     ")")])
  []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app
   (Term.proj
    (Term.paren
     "("
     [(Term.app
       `mul_lt_mul_left
       [(Term.paren
         "("
         [(Term.show
           "show"
           («term_<_» (numLit "0") "<" `d)
           (Term.fromTerm
            "from"
            (Term.subst
             (Term.proj `hb "." (fieldIdx "2"))
             "▸"
             [(Term.subst (Term.proj (Term.proj `hb "." (fieldIdx "2")) "." `symm) "▸" [`hd0])])))
          []]
         ")")])
      []]
     ")")
    "."
    (fieldIdx "1"))
   [(Term.paren
     "("
     [(Term.byTactic
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
              [(Tactic.rwRule ["←"] (Term.proj `hb "." (fieldIdx "2")))
               ","
               (Tactic.rwRule
                []
                (Term.app
                 `Nat.mul_div_cancel'ₓ
                 [(Term.paren "(" [(Term.app `gcd_dvd_left [(Term.hole "_") (Term.hole "_")]) []] ")")]))
               ","
               (Tactic.rwRule
                []
                (Term.app
                 `Nat.mul_div_cancel'ₓ
                 [(Term.paren "(" [(Term.app `gcd_dvd_right [(Term.hole "_") (Term.hole "_")]) []] ")")]))]
              "]")
             [])
            "<;>"
            (Tactic.exact "exact" (Term.proj `hb "." (fieldIdx "1"))))
           [])])))
      []]
     ")")])
  []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.proj `mem_range "." (fieldIdx "2"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `mem_range
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.proj `mem_filter "." (fieldIdx "2"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `mem_filter
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_/_»', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_/_» `b "/" `d)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_/_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `d
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
  `b
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveDecl', expected 'Lean.Parser.Term.haveDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveIdDecl.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.simpa "simpa" [] [] [] [] ["using" `hb]) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.simpa "simpa" [] [] [] [] ["using" `hb])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpa', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hb
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_∧_» («term_<_» `b "<" `n) "∧" («term_=_» (Term.app `gcd [`n `b]) "=" `d))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_∧_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_=_» (Term.app `gcd [`n `b]) "=" `d)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `d
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Term.app `gcd [`n `b])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `b
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `gcd
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 35 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 35, term))
  («term_<_» `b "<" `n)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_<_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  `b
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 36 >? 50, (some 51, term) <=? (some 35, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 35, (some 35, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  (Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [`a `b `ha `hb `h] [])]
    "=>"
    (Term.app (Term.proj (Term.app `Nat.mul_right_inj [`hd0]) "." (fieldIdx "1")) [`h])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app (Term.proj (Term.app `Nat.mul_right_inj [`hd0]) "." (fieldIdx "1")) [`h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `h
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.proj (Term.app `Nat.mul_right_inj [`hd0]) "." (fieldIdx "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `Nat.mul_right_inj [`hd0])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hd0
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Nat.mul_right_inj
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `Nat.mul_right_inj [`hd0]) []] ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [`a `b `ha `hb `h] [])]
    "=>"
    (Term.app (Term.proj (Term.paren "(" [(Term.app `Nat.mul_right_inj [`hd0]) []] ")") "." (fieldIdx "1")) [`h])))
  []]
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
    [(Term.simpleBinder [`m `hm] [])]
    "=>"
    (Term.have
     "have"
     (Term.haveDecl
      (Term.haveIdDecl
       [`hm []]
       [(Term.typeSpec
         ":"
         («term_∧_»
          («term_<_» `m "<" («term_/_» `n "/" `d))
          "∧"
          («term_=_» (Term.app `gcd [(«term_/_» `n "/" `d) `m]) "=" (numLit "1"))))]
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.simpa "simpa" [] [] [] [] ["using" `hm]) [])])))))
     []
     (Term.app
      (Term.proj `mem_filter "." (fieldIdx "2"))
      [(Term.anonymousCtor
        "⟨"
        [(«term_$__»
          (Term.proj `mem_range "." (fieldIdx "2"))
          "$"
          (Term.subst
           (Term.app `Nat.mul_div_cancel'ₓ [`hd])
           "▸"
           [(Term.app
             (Term.proj (Term.app `mul_lt_mul_left [`hd0]) "." (fieldIdx "2"))
             [(Term.proj `hm "." (fieldIdx "1"))])]))
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
                [(Tactic.rwRule ["←"] (Term.app `Nat.mul_div_cancel'ₓ [`hd]))
                 ","
                 (Tactic.rwRule [] `gcd_mul_left)
                 ","
                 (Tactic.rwRule [] (Term.proj `hm "." (fieldIdx "2")))
                 ","
                 (Tactic.rwRule [] `mul_oneₓ)]
                "]")
               [])
              [])])))]
        "⟩")]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.have
   "have"
   (Term.haveDecl
    (Term.haveIdDecl
     [`hm []]
     [(Term.typeSpec
       ":"
       («term_∧_»
        («term_<_» `m "<" («term_/_» `n "/" `d))
        "∧"
        («term_=_» (Term.app `gcd [(«term_/_» `n "/" `d) `m]) "=" (numLit "1"))))]
     ":="
     (Term.byTactic
      "by"
      (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.simpa "simpa" [] [] [] [] ["using" `hm]) [])])))))
   []
   (Term.app
    (Term.proj `mem_filter "." (fieldIdx "2"))
    [(Term.anonymousCtor
      "⟨"
      [(«term_$__»
        (Term.proj `mem_range "." (fieldIdx "2"))
        "$"
        (Term.subst
         (Term.app `Nat.mul_div_cancel'ₓ [`hd])
         "▸"
         [(Term.app
           (Term.proj (Term.app `mul_lt_mul_left [`hd0]) "." (fieldIdx "2"))
           [(Term.proj `hm "." (fieldIdx "1"))])]))
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
              [(Tactic.rwRule ["←"] (Term.app `Nat.mul_div_cancel'ₓ [`hd]))
               ","
               (Tactic.rwRule [] `gcd_mul_left)
               ","
               (Tactic.rwRule [] (Term.proj `hm "." (fieldIdx "2")))
               ","
               (Tactic.rwRule [] `mul_oneₓ)]
              "]")
             [])
            [])])))]
      "⟩")]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.have', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.have', expected 'Lean.Parser.Term.have.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   (Term.proj `mem_filter "." (fieldIdx "2"))
   [(Term.anonymousCtor
     "⟨"
     [(«term_$__»
       (Term.proj `mem_range "." (fieldIdx "2"))
       "$"
       (Term.subst
        (Term.app `Nat.mul_div_cancel'ₓ [`hd])
        "▸"
        [(Term.app
          (Term.proj (Term.app `mul_lt_mul_left [`hd0]) "." (fieldIdx "2"))
          [(Term.proj `hm "." (fieldIdx "1"))])]))
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
             [(Tactic.rwRule ["←"] (Term.app `Nat.mul_div_cancel'ₓ [`hd]))
              ","
              (Tactic.rwRule [] `gcd_mul_left)
              ","
              (Tactic.rwRule [] (Term.proj `hm "." (fieldIdx "2")))
              ","
              (Tactic.rwRule [] `mul_oneₓ)]
             "]")
            [])
           [])])))]
     "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor
   "⟨"
   [(«term_$__»
     (Term.proj `mem_range "." (fieldIdx "2"))
     "$"
     (Term.subst
      (Term.app `Nat.mul_div_cancel'ₓ [`hd])
      "▸"
      [(Term.app
        (Term.proj (Term.app `mul_lt_mul_left [`hd0]) "." (fieldIdx "2"))
        [(Term.proj `hm "." (fieldIdx "1"))])]))
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
           [(Tactic.rwRule ["←"] (Term.app `Nat.mul_div_cancel'ₓ [`hd]))
            ","
            (Tactic.rwRule [] `gcd_mul_left)
            ","
            (Tactic.rwRule [] (Term.proj `hm "." (fieldIdx "2")))
            ","
            (Tactic.rwRule [] `mul_oneₓ)]
           "]")
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
         [(Tactic.rwRule ["←"] (Term.app `Nat.mul_div_cancel'ₓ [`hd]))
          ","
          (Tactic.rwRule [] `gcd_mul_left)
          ","
          (Tactic.rwRule [] (Term.proj `hm "." (fieldIdx "2")))
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
    [(Tactic.rwRule ["←"] (Term.app `Nat.mul_div_cancel'ₓ [`hd]))
     ","
     (Tactic.rwRule [] `gcd_mul_left)
     ","
     (Tactic.rwRule [] (Term.proj `hm "." (fieldIdx "2")))
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
  (Term.proj `hm "." (fieldIdx "2"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `hm
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `gcd_mul_left
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Nat.mul_div_cancel'ₓ [`hd])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hd
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Nat.mul_div_cancel'ₓ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«←»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_$__»', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_$__»
   (Term.proj `mem_range "." (fieldIdx "2"))
   "$"
   (Term.subst
    (Term.app `Nat.mul_div_cancel'ₓ [`hd])
    "▸"
    [(Term.app
      (Term.proj (Term.app `mul_lt_mul_left [`hd0]) "." (fieldIdx "2"))
      [(Term.proj `hm "." (fieldIdx "1"))])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_$__»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.subst
   (Term.app `Nat.mul_div_cancel'ₓ [`hd])
   "▸"
   [(Term.app (Term.proj (Term.app `mul_lt_mul_left [`hd0]) "." (fieldIdx "2")) [(Term.proj `hm "." (fieldIdx "1"))])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.subst', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app (Term.proj (Term.app `mul_lt_mul_left [`hd0]) "." (fieldIdx "2")) [(Term.proj `hm "." (fieldIdx "1"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.proj `hm "." (fieldIdx "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `hm
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.proj (Term.app `mul_lt_mul_left [`hd0]) "." (fieldIdx "2"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `mul_lt_mul_left [`hd0])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hd0
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `mul_lt_mul_left
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `mul_lt_mul_left [`hd0]) []] ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 75 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 75, term))
  (Term.app `Nat.mul_div_cancel'ₓ [`hd])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hd
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Nat.mul_div_cancel'ₓ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 75, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 75, (some 75, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
  (Term.proj `mem_range "." (fieldIdx "2"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `mem_range
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 10, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.proj `mem_filter "." (fieldIdx "2"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `mem_filter
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveDecl', expected 'Lean.Parser.Term.haveDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveIdDecl.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.simpa "simpa" [] [] [] [] ["using" `hm]) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.simpa "simpa" [] [] [] [] ["using" `hm])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpa', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hm
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_∧_»
   («term_<_» `m "<" («term_/_» `n "/" `d))
   "∧"
   («term_=_» (Term.app `gcd [(«term_/_» `n "/" `d) `m]) "=" (numLit "1")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_∧_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_=_» (Term.app `gcd [(«term_/_» `n "/" `d) `m]) "=" (numLit "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "1")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Term.app `gcd [(«term_/_» `n "/" `d) `m])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `m
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_/_»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_/_»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_/_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_/_»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_/_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  («term_/_» `n "/" `d)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_/_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `d
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 70, (some 71, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(«term_/_» `n "/" `d) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `gcd
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 35 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 35, term))
  («term_<_» `m "<" («term_/_» `n "/" `d))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_<_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_/_» `n "/" `d)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_/_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `d
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  `m
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 36 >? 50, (some 51, term) <=? (some 35, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 35, (some 35, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
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
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [`m `hm] [])]
    "=>"
    (Term.have
     "have"
     (Term.haveDecl
      (Term.haveIdDecl
       [`hm []]
       [(Term.typeSpec
         ":"
         («term_∧_»
          («term_<_» `m "<" («term_/_» `n "/" `d))
          "∧"
          («term_=_» (Term.app `gcd [(Term.paren "(" [(«term_/_» `n "/" `d) []] ")") `m]) "=" (numLit "1"))))]
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.simpa "simpa" [] [] [] [] ["using" `hm]) [])])))))
     []
     (Term.app
      (Term.proj `mem_filter "." (fieldIdx "2"))
      [(Term.anonymousCtor
        "⟨"
        [(«term_$__»
          (Term.proj `mem_range "." (fieldIdx "2"))
          "$"
          (Term.subst
           (Term.app `Nat.mul_div_cancel'ₓ [`hd])
           "▸"
           [(Term.app
             (Term.proj (Term.paren "(" [(Term.app `mul_lt_mul_left [`hd0]) []] ")") "." (fieldIdx "2"))
             [(Term.proj `hm "." (fieldIdx "1"))])]))
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
                [(Tactic.rwRule ["←"] (Term.app `Nat.mul_div_cancel'ₓ [`hd]))
                 ","
                 (Tactic.rwRule [] `gcd_mul_left)
                 ","
                 (Tactic.rwRule [] (Term.proj `hm "." (fieldIdx "2")))
                 ","
                 (Tactic.rwRule [] `mul_oneₓ)]
                "]")
               [])
              [])])))]
        "⟩")]))))
  []]
 ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`m `hm] [])] "=>" (Finset.Data.Finset.Fold.«term_*_» `d "*" `m)))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Finset.Data.Finset.Fold.«term_*_» `d "*" `m)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `m
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `d
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
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
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`m `hm] [])] "=>" (Finset.Data.Finset.Fold.«term_*_» `d "*" `m)))
  []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `card_congr
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveDecl', expected 'Lean.Parser.Term.haveDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveIdDecl.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
  (Term.app
   `Nat.pos_of_ne_zeroₓ
   [(Term.fun
     "fun"
     (Term.basicFun
      [(Term.simpleBinder [`h] [])]
      "=>"
      (Term.app `hn0 [(«term_$__» `eq_zero_of_zero_dvd "$" (Term.subst `h "▸" [`hd]))])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [`h] [])]
    "=>"
    (Term.app `hn0 [(«term_$__» `eq_zero_of_zero_dvd "$" (Term.subst `h "▸" [`hd]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `hn0 [(«term_$__» `eq_zero_of_zero_dvd "$" (Term.subst `h "▸" [`hd]))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_$__»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_$__»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_$__»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_$__»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_$__»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_$__» `eq_zero_of_zero_dvd "$" (Term.subst `h "▸" [`hd]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_$__»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.subst `h "▸" [`hd])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.subst', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hd
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 75 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 75, term))
  `h
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 75, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 75, (some 75, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
  `eq_zero_of_zero_dvd
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 10, (some 10, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(«term_$__» `eq_zero_of_zero_dvd "$" (Term.subst `h "▸" [`hd])) []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `hn0
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
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
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Nat.pos_of_ne_zeroₓ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_<_» (numLit "0") "<" `d)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_<_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `d
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (numLit "0")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveDecl', expected 'Lean.Parser.Term.haveDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveIdDecl.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
  (Term.proj (Term.app (Term.proj `mem_filter "." (fieldIdx "1")) [`hd]) "." (fieldIdx "2"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app (Term.proj `mem_filter "." (fieldIdx "1")) [`hd])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hd
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.proj `mem_filter "." (fieldIdx "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `mem_filter
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app (Term.proj `mem_filter "." (fieldIdx "1")) [`hd]) []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Core.«term_∣_» `d " ∣ " `n)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Core.«term_∣_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  `d
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 50 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  `rfl
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `sum_congr
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_=_»
   (Term.hole "_")
   "="
   (Algebra.BigOperators.Basic.«term∑_in_,_»
    "∑"
    (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `d)] []))
    " in "
    (Term.app (Term.proj (Term.app `range [`n.succ]) "." `filter) [(Init.Core.«term_∣_» (Term.cdot "·") " ∣ " `n)])
    ", "
    (Term.proj
     (Term.app
      (Term.proj (Term.app `range [`n]) "." `filter)
      [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`m] [])] "=>" («term_=_» (Term.app `gcd [`n `m]) "=" `d)))])
     "."
     `card)))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Algebra.BigOperators.Basic.«term∑_in_,_»
   "∑"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `d)] []))
   " in "
   (Term.app (Term.proj (Term.app `range [`n.succ]) "." `filter) [(Init.Core.«term_∣_» (Term.cdot "·") " ∣ " `n)])
   ", "
   (Term.proj
    (Term.app
     (Term.proj (Term.app `range [`n]) "." `filter)
     [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`m] [])] "=>" («term_=_» (Term.app `gcd [`n `m]) "=" `d)))])
    "."
    `card))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.BigOperators.Basic.«term∑_in_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.proj
   (Term.app
    (Term.proj (Term.app `range [`n]) "." `filter)
    [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`m] [])] "=>" («term_=_» (Term.app `gcd [`n `m]) "=" `d)))])
   "."
   `card)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app
   (Term.proj (Term.app `range [`n]) "." `filter)
   [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`m] [])] "=>" («term_=_» (Term.app `gcd [`n `m]) "=" `d)))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`m] [])] "=>" («term_=_» (Term.app `gcd [`n `m]) "=" `d)))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_=_» (Term.app `gcd [`n `m]) "=" `d)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `d
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Term.app `gcd [`n `m])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `m
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `gcd
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
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
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.proj (Term.app `range [`n]) "." `filter)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `range [`n])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `range
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `range [`n]) []] ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app
   (Term.proj (Term.paren "(" [(Term.app `range [`n]) []] ")") "." `filter)
   [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`m] [])] "=>" («term_=_» (Term.app `gcd [`n `m]) "=" `d)))])
  []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app (Term.proj (Term.app `range [`n.succ]) "." `filter) [(Init.Core.«term_∣_» (Term.cdot "·") " ∣ " `n)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Core.«term_∣_»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Core.«term_∣_»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Core.«term_∣_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Core.«term_∣_»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Core.«term_∣_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Core.«term_∣_» (Term.cdot "·") " ∣ " `n)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Core.«term_∣_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Term.cdot "·")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.cdot', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.cdot', expected 'Lean.Parser.Term.cdot.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 50 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Init.Core.«term_∣_» (Term.cdot "·") " ∣ " `n) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.proj (Term.app `range [`n.succ]) "." `filter)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `range [`n.succ])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `n.succ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `range
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `range [`n.succ]) []] ")")
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
theorem
  sum_totient
  ( n : ℕ ) : ∑ m in range n.succ . filter · ∣ n , φ m = n
  :=
    if
      hn0
      :
      n = 0
      then
      by simp [ hn0 ]
      else
      calc
        ∑ m in range n.succ . filter · ∣ n , φ m
              =
              ∑ d in range n.succ . filter · ∣ n , range n / d . filter fun m => gcd n / d m = 1 . card
            :=
            Eq.symm
              $
              sum_bij
                fun d _ => n / d
                  fun
                    d hd
                      =>
                      mem_filter . 2
                        ⟨
                          mem_range . 2 $ lt_succ_of_le $ Nat.div_le_selfₓ _ _
                            ,
                            by conv => rhs rw [ ← Nat.mul_div_cancel'ₓ mem_filter . 1 hd . 2 ] <;> simp
                          ⟩
                  fun _ _ => rfl
                  fun
                    a b ha hb h
                      =>
                      have
                        ha : a * n / a = n := Nat.mul_div_cancel'ₓ mem_filter . 1 ha . 2
                        have
                          : 0 < n / a := Nat.pos_of_ne_zeroₓ fun h => by simp_all [ lt_irreflₓ ]
                          by rw [ ← Nat.mul_left_inj this , ha , h , Nat.mul_div_cancel'ₓ mem_filter . 1 hb . 2 ]
                  fun
                    b hb
                      =>
                      have
                        hb : b < n.succ ∧ b ∣ n := by simpa [ - range_succ ] using hb
                        have
                          hbn : n / b ∣ n := ⟨ b , by rw [ Nat.div_mul_cancelₓ hb . 2 ] ⟩
                          have
                            hnb0 : n / b ≠ 0 := fun h => by simpa [ h , Ne.symm hn0 ] using Nat.div_mul_cancelₓ hbn
                            ⟨
                              n / b
                                ,
                                mem_filter . 2 ⟨ mem_range . 2 $ lt_succ_of_le $ Nat.div_le_selfₓ _ _ , hbn ⟩
                                ,
                                by
                                  rw
                                    [
                                      ← Nat.mul_left_inj Nat.pos_of_ne_zeroₓ hnb0
                                        ,
                                        Nat.mul_div_cancel'ₓ hb . 2
                                        ,
                                        Nat.div_mul_cancelₓ hbn
                                      ]
                              ⟩
          _ = ∑ d in range n.succ . filter · ∣ n , range n . filter fun m => gcd n m = d . card
            :=
            sum_congr
              rfl
                fun
                  d hd
                    =>
                    have
                      hd : d ∣ n := mem_filter . 1 hd . 2
                      have
                        hd0 : 0 < d := Nat.pos_of_ne_zeroₓ fun h => hn0 eq_zero_of_zero_dvd $ h ▸ hd
                        card_congr
                          fun m hm => d * m
                            fun
                              m hm
                                =>
                                have
                                  hm : m < n / d ∧ gcd n / d m = 1 := by simpa using hm
                                  mem_filter . 2
                                    ⟨
                                      mem_range . 2 $ Nat.mul_div_cancel'ₓ hd ▸ mul_lt_mul_left hd0 . 2 hm . 1
                                        ,
                                        by rw [ ← Nat.mul_div_cancel'ₓ hd , gcd_mul_left , hm . 2 , mul_oneₓ ]
                                      ⟩
                            fun a b ha hb h => Nat.mul_right_inj hd0 . 1 h
                            fun
                              b hb
                                =>
                                have
                                  hb : b < n ∧ gcd n b = d := by simpa using hb
                                  ⟨
                                    b / d
                                      ,
                                      mem_filter . 2
                                        ⟨
                                          mem_range . 2
                                              mul_lt_mul_left show 0 < d from hb . 2 ▸ hb . 2 . symm ▸ hd0 . 1
                                                by
                                                  rw
                                                      [
                                                        ← hb . 2
                                                          ,
                                                          Nat.mul_div_cancel'ₓ gcd_dvd_left _ _
                                                          ,
                                                          Nat.mul_div_cancel'ₓ gcd_dvd_right _ _
                                                        ]
                                                    <;>
                                                    exact hb . 1
                                            ,
                                            hb . 2 ▸ coprime_div_gcd_div_gcd hb . 2 . symm ▸ hd0
                                          ⟩
                                      ,
                                      hb . 2 ▸ Nat.mul_div_cancel'ₓ gcd_dvd_right _ _
                                    ⟩
          _ = filter · ∣ n range n.succ . bUnion fun d => range n . filter fun m => gcd n m = d . card
            :=
            card_bUnion by intros <;> apply disjoint_filter . 2 <;> cc . symm
          _ = range n . card
            :=
            congr_argₓ
              card
                Finset.ext
                  fun
                    m
                      =>
                      ⟨
                        by finish
                          ,
                          fun
                            hm
                              =>
                              have
                                h : m < n := mem_range . 1 hm
                                mem_bUnion . 2
                                  ⟨
                                    gcd n m
                                      ,
                                      mem_filter . 2
                                        ⟨
                                          mem_range . 2
                                              lt_succ_of_le le_of_dvd lt_of_le_of_ltₓ zero_le _ h gcd_dvd_left _ _
                                            ,
                                            gcd_dvd_left _ _
                                          ⟩
                                      ,
                                      mem_filter . 2 ⟨ hm , rfl ⟩
                                    ⟩
                        ⟩
          _ = n := card_range _

/--  When `p` is prime, then the totient of `p ^ (n + 1)` is `p ^ n * (p - 1)` -/
theorem totient_prime_pow_succ {p : ℕ} (hp : p.prime) (n : ℕ) : φ (p ^ n+1) = (p ^ n)*p - 1 :=
  calc φ (p ^ n+1) = ((range (p ^ n+1)).filter (coprime (p ^ n+1))).card := totient_eq_card_coprime _
    _ = (range (p ^ n+1) \ (range (p ^ n)).Image (·*p)).card :=
    congr_argₓ card
      (by
        rw [sdiff_eq_filter]
        apply filter_congr
        simp only [mem_range, mem_filter, coprime_pow_left_iff n.succ_pos, mem_image, not_exists,
          hp.coprime_iff_not_dvd]
        intro a ha
        constructor
        ·
          rintro hap b _ rfl
          exact hap (dvd_mul_left _ _)
        ·
          rintro h ⟨b, rfl⟩
          rw [pow_succₓ] at ha
          exact h b (lt_of_mul_lt_mul_left ha (zero_le _)) (mul_commₓ _ _))
    _ = _ :=
    have h1 : Set.InjOn (·*p) (range (p ^ n)) := fun x _ y _ => (Nat.mul_left_inj hp.pos).1
    have h2 : (range (p ^ n)).Image (·*p) ⊆ range (p ^ n+1) := fun a => by
      simp only [mem_image, mem_range, exists_imp_distrib]
      rintro b h rfl
      rw [pow_succ'ₓ]
      exact (mul_lt_mul_right hp.pos).2 h
    by
    rw [card_sdiff h2, card_image_of_inj_on h1, card_range, card_range, ← one_mulₓ (p ^ n), pow_succₓ, ← tsub_mul,
      one_mulₓ, mul_commₓ]
    

/--  When `p` is prime, then the totient of `p ^ ` is `p ^ (n - 1) * (p - 1)` -/
theorem totient_prime_pow {p : ℕ} (hp : p.prime) {n : ℕ} (hn : 0 < n) : φ (p ^ n) = (p ^ (n - 1))*p - 1 := by
  rcases exists_eq_succ_of_ne_zero (pos_iff_ne_zero.1 hn) with ⟨m, rfl⟩ <;> exact totient_prime_pow_succ hp _

theorem totient_prime {p : ℕ} (hp : p.prime) : φ p = p - 1 := by
  rw [← pow_oneₓ p, totient_prime_pow hp] <;> simp

theorem totient_eq_iff_prime {p : ℕ} (hp : 0 < p) : p.totient = p - 1 ↔ p.prime := by
  refine' ⟨fun h => _, totient_prime⟩
  replace hp : 1 < p
  ·
    apply lt_of_le_of_neₓ
    ·
      rwa [succ_le_iff]
    ·
      rintro rfl
      rw [totient_one, tsub_self] at h
      exact one_ne_zero h
  rw [totient_eq_card_coprime, range_eq_Ico, ← Ico_insert_succ_left hp.le, Finset.filter_insert,
    if_neg (Tactic.NormNum.nat_coprime_helper_zero_right p hp), ← Nat.card_Ico 1 p] at h
  refine' p.prime_of_coprime hp fun n hn hnz => Finset.filter_card_eq h n $ finset.mem_Ico.mpr ⟨_, hn⟩
  rwa [succ_le_iff, pos_iff_ne_zero]

theorem card_units_zmod_lt_sub_one {p : ℕ} (hp : 1 < p) [Fintype (Units (Zmod p))] :
    Fintype.card (Units (Zmod p)) ≤ p - 1 := by
  have : Fact (0 < p) := ⟨zero_lt_one.trans hp⟩
  rw [Zmod.card_units_eq_totient p]
  exact Nat.le_pred_of_lt (Nat.totient_lt p hp)

theorem prime_iff_card_units (p : ℕ) [Fintype (Units (Zmod p))] : p.prime ↔ Fintype.card (Units (Zmod p)) = p - 1 := by
  by_cases' hp : p = 0
  ·
    subst hp
    simp only [Zmod, not_prime_zero, false_iffₓ, zero_tsub]
    suffices Fintype.card (Units ℤ) ≠ 0 by
      convert this
    simp
  have : Fact (0 < p) := ⟨Nat.pos_of_ne_zeroₓ hp⟩
  rw [Zmod.card_units_eq_totient, Nat.totient_eq_iff_prime (Fact.out (0 < p))]

@[simp]
theorem totient_two : φ 2 = 1 :=
  (totient_prime prime_two).trans
    (by
      norm_num)

end Nat

