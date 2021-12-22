import Mathbin.Data.Rat.Basic

/-!
# Order for Rational Numbers

## Summary

We define the order on `ℚ`, prove that `ℚ` is a discrete, linearly ordered field, and define
functions such as `abs` and `sqrt` that depend on this order.

## Notations

- `/.` is infix notation for `rat.mk`.

## Tags

rat, rationals, field, ℚ, numerator, denominator, num, denom, order, ordering, sqrt, abs
-/


namespace Rat

variable (a b c : ℚ)

open_locale Rat

/--  A rational number is called nonnegative if its numerator is nonnegative. -/
protected def nonneg (r : ℚ) : Prop :=
  0 ≤ r.num

@[simp]
theorem mk_nonneg (a : ℤ) {b : ℤ} (h : 0 < b) : (a /. b).Nonneg ↔ 0 ≤ a := by
  generalize ha : a /. b = x
  cases' x with n₁ d₁ h₁ c₁
  rw [num_denom'] at ha
  simp [Rat.Nonneg]
  have d0 := Int.coe_nat_lt.2 h₁
  have := (mk_eq (ne_of_gtₓ h) (ne_of_gtₓ d0)).1 ha
  constructor <;> intro h₂
  ·
    apply nonneg_of_mul_nonneg_right _ d0
    rw [this]
    exact mul_nonneg h₂ (le_of_ltₓ h)
  ·
    apply nonneg_of_mul_nonneg_right _ h
    rw [← this]
    exact mul_nonneg h₂ (Int.coe_zero_le _)

protected theorem nonneg_add {a b} : Rat.Nonneg a → Rat.Nonneg b → Rat.Nonneg (a+b) :=
  num_denom_cases_on' a $ fun n₁ d₁ h₁ =>
    num_denom_cases_on' b $ fun n₂ d₂ h₂ => by
      have d₁0 : 0 < (d₁ : ℤ) := Int.coe_nat_pos.2 (Nat.pos_of_ne_zeroₓ h₁)
      have d₂0 : 0 < (d₂ : ℤ) := Int.coe_nat_pos.2 (Nat.pos_of_ne_zeroₓ h₂)
      simp [d₁0, d₂0, h₁, h₂, mul_pos d₁0 d₂0]
      intro n₁0 n₂0
      apply add_nonneg <;>
        apply mul_nonneg <;>
          ·
            first |
              assumption|
              apply Int.coe_zero_le

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [] [] [(Command.protected "protected")] [] [] [])
 (Command.theorem
  "theorem"
  (Command.declId `nonneg_mul [])
  (Command.declSig
   [(Term.implicitBinder "{" [`a `b] [] "}")]
   (Term.typeSpec
    ":"
    (Term.arrow
     (Term.app `Rat.Nonneg [`a])
     "→"
     (Term.arrow (Term.app `Rat.Nonneg [`b]) "→" (Term.app `Rat.Nonneg [(Init.Logic.«term_*_» `a "*" `b)])))))
  (Command.declValSimple
   ":="
   («term_$__»
    (Term.app `num_denom_cases_on' [`a])
    "$"
    (Term.fun
     "fun"
     (Term.basicFun
      [(Term.simpleBinder [`n₁ `d₁ `h₁] [])]
      "=>"
      («term_$__»
       (Term.app `num_denom_cases_on' [`b])
       "$"
       (Term.fun
        "fun"
        (Term.basicFun
         [(Term.simpleBinder [`n₂ `d₂ `h₂] [])]
         "=>"
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(group
              (Tactic.tacticHave_
               "have"
               (Term.haveDecl
                (Term.haveIdDecl
                 [`d₁0 []]
                 [(Term.typeSpec
                   ":"
                   («term_<_» (numLit "0") "<" (Term.paren "(" [`d₁ [(Term.typeAscription ":" (termℤ "ℤ"))]] ")")))]
                 ":="
                 (Term.app (Term.proj `Int.coe_nat_pos "." (fieldIdx "2")) [(Term.app `Nat.pos_of_ne_zeroₓ [`h₁])]))))
              [])
             (group
              (Tactic.tacticHave_
               "have"
               (Term.haveDecl
                (Term.haveIdDecl
                 [`d₂0 []]
                 [(Term.typeSpec
                   ":"
                   («term_<_» (numLit "0") "<" (Term.paren "(" [`d₂ [(Term.typeAscription ":" (termℤ "ℤ"))]] ")")))]
                 ":="
                 (Term.app (Term.proj `Int.coe_nat_pos "." (fieldIdx "2")) [(Term.app `Nat.pos_of_ne_zeroₓ [`h₂])]))))
              [])
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
                [(Tactic.simpLemma [] [] `d₁0)
                 ","
                 (Tactic.simpLemma [] [] `d₂0)
                 ","
                 (Tactic.simpLemma [] [] `h₁)
                 ","
                 (Tactic.simpLemma [] [] `h₂)
                 ","
                 (Tactic.simpLemma [] [] (Term.app `mul_pos [`d₁0 `d₂0]))
                 ","
                 (Tactic.simpLemma [] [] `mul_nonneg)]
                "]"]
               [])
              [])])))))))))
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
  («term_$__»
   (Term.app `num_denom_cases_on' [`a])
   "$"
   (Term.fun
    "fun"
    (Term.basicFun
     [(Term.simpleBinder [`n₁ `d₁ `h₁] [])]
     "=>"
     («term_$__»
      (Term.app `num_denom_cases_on' [`b])
      "$"
      (Term.fun
       "fun"
       (Term.basicFun
        [(Term.simpleBinder [`n₂ `d₂ `h₂] [])]
        "=>"
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group
             (Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                [`d₁0 []]
                [(Term.typeSpec
                  ":"
                  («term_<_» (numLit "0") "<" (Term.paren "(" [`d₁ [(Term.typeAscription ":" (termℤ "ℤ"))]] ")")))]
                ":="
                (Term.app (Term.proj `Int.coe_nat_pos "." (fieldIdx "2")) [(Term.app `Nat.pos_of_ne_zeroₓ [`h₁])]))))
             [])
            (group
             (Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                [`d₂0 []]
                [(Term.typeSpec
                  ":"
                  («term_<_» (numLit "0") "<" (Term.paren "(" [`d₂ [(Term.typeAscription ":" (termℤ "ℤ"))]] ")")))]
                ":="
                (Term.app (Term.proj `Int.coe_nat_pos "." (fieldIdx "2")) [(Term.app `Nat.pos_of_ne_zeroₓ [`h₂])]))))
             [])
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
               [(Tactic.simpLemma [] [] `d₁0)
                ","
                (Tactic.simpLemma [] [] `d₂0)
                ","
                (Tactic.simpLemma [] [] `h₁)
                ","
                (Tactic.simpLemma [] [] `h₂)
                ","
                (Tactic.simpLemma [] [] (Term.app `mul_pos [`d₁0 `d₂0]))
                ","
                (Tactic.simpLemma [] [] `mul_nonneg)]
               "]"]
              [])
             [])])))))))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_$__»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [`n₁ `d₁ `h₁] [])]
    "=>"
    («term_$__»
     (Term.app `num_denom_cases_on' [`b])
     "$"
     (Term.fun
      "fun"
      (Term.basicFun
       [(Term.simpleBinder [`n₂ `d₂ `h₂] [])]
       "=>"
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group
            (Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               [`d₁0 []]
               [(Term.typeSpec
                 ":"
                 («term_<_» (numLit "0") "<" (Term.paren "(" [`d₁ [(Term.typeAscription ":" (termℤ "ℤ"))]] ")")))]
               ":="
               (Term.app (Term.proj `Int.coe_nat_pos "." (fieldIdx "2")) [(Term.app `Nat.pos_of_ne_zeroₓ [`h₁])]))))
            [])
           (group
            (Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               [`d₂0 []]
               [(Term.typeSpec
                 ":"
                 («term_<_» (numLit "0") "<" (Term.paren "(" [`d₂ [(Term.typeAscription ":" (termℤ "ℤ"))]] ")")))]
               ":="
               (Term.app (Term.proj `Int.coe_nat_pos "." (fieldIdx "2")) [(Term.app `Nat.pos_of_ne_zeroₓ [`h₂])]))))
            [])
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
              [(Tactic.simpLemma [] [] `d₁0)
               ","
               (Tactic.simpLemma [] [] `d₂0)
               ","
               (Tactic.simpLemma [] [] `h₁)
               ","
               (Tactic.simpLemma [] [] `h₂)
               ","
               (Tactic.simpLemma [] [] (Term.app `mul_pos [`d₁0 `d₂0]))
               ","
               (Tactic.simpLemma [] [] `mul_nonneg)]
              "]"]
             [])
            [])]))))))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_$__»
   (Term.app `num_denom_cases_on' [`b])
   "$"
   (Term.fun
    "fun"
    (Term.basicFun
     [(Term.simpleBinder [`n₂ `d₂ `h₂] [])]
     "=>"
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(group
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`d₁0 []]
             [(Term.typeSpec
               ":"
               («term_<_» (numLit "0") "<" (Term.paren "(" [`d₁ [(Term.typeAscription ":" (termℤ "ℤ"))]] ")")))]
             ":="
             (Term.app (Term.proj `Int.coe_nat_pos "." (fieldIdx "2")) [(Term.app `Nat.pos_of_ne_zeroₓ [`h₁])]))))
          [])
         (group
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`d₂0 []]
             [(Term.typeSpec
               ":"
               («term_<_» (numLit "0") "<" (Term.paren "(" [`d₂ [(Term.typeAscription ":" (termℤ "ℤ"))]] ")")))]
             ":="
             (Term.app (Term.proj `Int.coe_nat_pos "." (fieldIdx "2")) [(Term.app `Nat.pos_of_ne_zeroₓ [`h₂])]))))
          [])
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
            [(Tactic.simpLemma [] [] `d₁0)
             ","
             (Tactic.simpLemma [] [] `d₂0)
             ","
             (Tactic.simpLemma [] [] `h₁)
             ","
             (Tactic.simpLemma [] [] `h₂)
             ","
             (Tactic.simpLemma [] [] (Term.app `mul_pos [`d₁0 `d₂0]))
             ","
             (Tactic.simpLemma [] [] `mul_nonneg)]
            "]"]
           [])
          [])]))))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_$__»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [`n₂ `d₂ `h₂] [])]
    "=>"
    (Term.byTactic
     "by"
     (Tactic.tacticSeq
      (Tactic.tacticSeq1Indented
       [(group
         (Tactic.tacticHave_
          "have"
          (Term.haveDecl
           (Term.haveIdDecl
            [`d₁0 []]
            [(Term.typeSpec
              ":"
              («term_<_» (numLit "0") "<" (Term.paren "(" [`d₁ [(Term.typeAscription ":" (termℤ "ℤ"))]] ")")))]
            ":="
            (Term.app (Term.proj `Int.coe_nat_pos "." (fieldIdx "2")) [(Term.app `Nat.pos_of_ne_zeroₓ [`h₁])]))))
         [])
        (group
         (Tactic.tacticHave_
          "have"
          (Term.haveDecl
           (Term.haveIdDecl
            [`d₂0 []]
            [(Term.typeSpec
              ":"
              («term_<_» (numLit "0") "<" (Term.paren "(" [`d₂ [(Term.typeAscription ":" (termℤ "ℤ"))]] ")")))]
            ":="
            (Term.app (Term.proj `Int.coe_nat_pos "." (fieldIdx "2")) [(Term.app `Nat.pos_of_ne_zeroₓ [`h₂])]))))
         [])
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
           [(Tactic.simpLemma [] [] `d₁0)
            ","
            (Tactic.simpLemma [] [] `d₂0)
            ","
            (Tactic.simpLemma [] [] `h₁)
            ","
            (Tactic.simpLemma [] [] `h₂)
            ","
            (Tactic.simpLemma [] [] (Term.app `mul_pos [`d₁0 `d₂0]))
            ","
            (Tactic.simpLemma [] [] `mul_nonneg)]
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
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`d₁0 []]
          [(Term.typeSpec
            ":"
            («term_<_» (numLit "0") "<" (Term.paren "(" [`d₁ [(Term.typeAscription ":" (termℤ "ℤ"))]] ")")))]
          ":="
          (Term.app (Term.proj `Int.coe_nat_pos "." (fieldIdx "2")) [(Term.app `Nat.pos_of_ne_zeroₓ [`h₁])]))))
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`d₂0 []]
          [(Term.typeSpec
            ":"
            («term_<_» (numLit "0") "<" (Term.paren "(" [`d₂ [(Term.typeAscription ":" (termℤ "ℤ"))]] ")")))]
          ":="
          (Term.app (Term.proj `Int.coe_nat_pos "." (fieldIdx "2")) [(Term.app `Nat.pos_of_ne_zeroₓ [`h₂])]))))
       [])
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
         [(Tactic.simpLemma [] [] `d₁0)
          ","
          (Tactic.simpLemma [] [] `d₂0)
          ","
          (Tactic.simpLemma [] [] `h₁)
          ","
          (Tactic.simpLemma [] [] `h₂)
          ","
          (Tactic.simpLemma [] [] (Term.app `mul_pos [`d₁0 `d₂0]))
          ","
          (Tactic.simpLemma [] [] `mul_nonneg)]
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
    [(Tactic.simpLemma [] [] `d₁0)
     ","
     (Tactic.simpLemma [] [] `d₂0)
     ","
     (Tactic.simpLemma [] [] `h₁)
     ","
     (Tactic.simpLemma [] [] `h₂)
     ","
     (Tactic.simpLemma [] [] (Term.app `mul_pos [`d₁0 `d₂0]))
     ","
     (Tactic.simpLemma [] [] `mul_nonneg)]
    "]"]
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `mul_nonneg
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `mul_pos [`d₁0 `d₂0])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `d₂0
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `d₁0
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `mul_pos
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `h₂
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `h₁
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `d₂0
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `d₁0
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«)»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«)»', expected 'Lean.Parser.Tactic.discharger'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts'
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
protected
  theorem
    nonneg_mul
    { a b } : Rat.Nonneg a → Rat.Nonneg b → Rat.Nonneg a * b
    :=
      num_denom_cases_on' a
        $
        fun
          n₁ d₁ h₁
            =>
            num_denom_cases_on' b
              $
              fun
                n₂ d₂ h₂
                  =>
                  by
                    have d₁0 : 0 < ( d₁ : ℤ ) := Int.coe_nat_pos . 2 Nat.pos_of_ne_zeroₓ h₁
                      have d₂0 : 0 < ( d₂ : ℤ ) := Int.coe_nat_pos . 2 Nat.pos_of_ne_zeroₓ h₂
                      simp
                        ( config := { contextual := Bool.true._@._internal._hyg.0 } )
                        [ d₁0 , d₂0 , h₁ , h₂ , mul_pos d₁0 d₂0 , mul_nonneg ]

protected theorem nonneg_antisymm {a} : Rat.Nonneg a → Rat.Nonneg (-a) → a = 0 :=
  num_denom_cases_on' a $ fun n d h => by
    have d0 : 0 < (d : ℤ) := Int.coe_nat_pos.2 (Nat.pos_of_ne_zeroₓ h)
    simp [d0, h]
    exact fun h₁ h₂ => le_antisymmₓ h₂ h₁

protected theorem nonneg_total : Rat.Nonneg a ∨ Rat.Nonneg (-a) := by
  cases' a with n <;> exact Or.imp_rightₓ neg_nonneg_of_nonpos (le_totalₓ 0 n)

instance decidable_nonneg : Decidable (Rat.Nonneg a) := by
  cases a <;> unfold Rat.Nonneg <;> infer_instance

/--  Relation `a ≤ b` on `ℚ` defined as `a ≤ b ↔ rat.nonneg (b - a)`. Use `a ≤ b` instead of
`rat.le a b`. -/
protected def le (a b : ℚ) :=
  Rat.Nonneg (b - a)

instance : LE ℚ :=
  ⟨Rat.Le⟩

instance decidable_le : DecidableRel (· ≤ · : ℚ → ℚ → Prop)
  | a, b =>
    show Decidable (Rat.Nonneg (b - a))by
      infer_instance

protected theorem le_def {a b c d : ℤ} (b0 : 0 < b) (d0 : 0 < d) : a /. b ≤ c /. d ↔ (a*d) ≤ c*b := by
  show Rat.Nonneg _ ↔ _
  rw [← sub_nonneg]
  simp [sub_eq_add_neg, ne_of_gtₓ b0, ne_of_gtₓ d0, mul_pos d0 b0]

protected theorem le_reflₓ : a ≤ a :=
  show Rat.Nonneg (a - a)by
    rw [sub_self] <;> exact le_reflₓ (0 : ℤ)

protected theorem le_totalₓ : a ≤ b ∨ b ≤ a := by
  have := Rat.nonneg_total (b - a) <;> rwa [neg_sub] at this

protected theorem le_antisymmₓ {a b : ℚ} (hab : a ≤ b) (hba : b ≤ a) : a = b := by
  have :=
    eq_neg_of_add_eq_zero
      (Rat.nonneg_antisymm hba $ by
        rwa [← sub_eq_add_neg, neg_sub])
  rwa [neg_negₓ] at this

protected theorem le_transₓ {a b c : ℚ} (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c :=
  have : Rat.Nonneg ((b - a)+c - b) := Rat.nonneg_add hab hbc
  by
  simpa [sub_eq_add_neg, add_commₓ, add_left_commₓ]

-- failed to format: format: uncaught backtrack exception
instance
  : LinearOrderₓ ℚ
  where
    le := Rat.Le
      le_refl := Rat.le_refl
      le_trans := @ Rat.le_trans
      le_antisymm := @ Rat.le_antisymm
      le_total := Rat.le_total
      DecidableEq := by infer_instance
      decidableLe a b := Rat.decidableNonneg ( b - a )

instance : LT ℚ := by
  infer_instance

instance : DistribLattice ℚ := by
  infer_instance

instance : Lattice ℚ := by
  infer_instance

instance : SemilatticeInf ℚ := by
  infer_instance

instance : SemilatticeSup ℚ := by
  infer_instance

instance : HasInf ℚ := by
  infer_instance

instance : HasSup ℚ := by
  infer_instance

instance : PartialOrderₓ ℚ := by
  infer_instance

instance : Preorderₓ ℚ := by
  infer_instance

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [] [] [(Command.protected "protected")] [] [] [])
 (Command.theorem
  "theorem"
  (Command.declId `le_def' [])
  (Command.declSig
   [(Term.implicitBinder "{" [`p `q] [":" (Data.Rat.Basic.termℚ "ℚ")] "}")]
   (Term.typeSpec
    ":"
    («term_↔_»
     («term_≤_» `p "≤" `q)
     "↔"
     («term_≤_» (Init.Logic.«term_*_» `p.num "*" `q.denom) "≤" (Init.Logic.«term_*_» `q.num "*" `p.denom)))))
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
          [(Tactic.rwRule ["←"] (Term.app (Term.explicit "@" `num_denom) [`q]))
           ","
           (Tactic.rwRule ["←"] (Term.app (Term.explicit "@" `num_denom) [`p]))]
          "]")
         [])
        [])
       (group
        (Mathlib.Tactic.Conv.convRHS
         "conv_rhs"
         []
         []
         "=>"
         (Tactic.Conv.convSeq
          (Tactic.Conv.convSeq1Indented
           [(group (Tactic.Conv.simp "simp" [] ["only"] ["[" [(Tactic.simpLemma [] [] `num_denom)] "]"] []) [])])))
        [])
       (group
        (Tactic.exact
         "exact"
         (Term.app
          `Rat.le_def
          [(Term.byTactic
            "by"
            (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.exactModCast "exact_mod_cast" `p.pos) [])])))
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented [(group (Tactic.exactModCast "exact_mod_cast" `q.pos) [])])))]))
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
         [(Tactic.rwRule ["←"] (Term.app (Term.explicit "@" `num_denom) [`q]))
          ","
          (Tactic.rwRule ["←"] (Term.app (Term.explicit "@" `num_denom) [`p]))]
         "]")
        [])
       [])
      (group
       (Mathlib.Tactic.Conv.convRHS
        "conv_rhs"
        []
        []
        "=>"
        (Tactic.Conv.convSeq
         (Tactic.Conv.convSeq1Indented
          [(group (Tactic.Conv.simp "simp" [] ["only"] ["[" [(Tactic.simpLemma [] [] `num_denom)] "]"] []) [])])))
       [])
      (group
       (Tactic.exact
        "exact"
        (Term.app
         `Rat.le_def
         [(Term.byTactic
           "by"
           (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.exactModCast "exact_mod_cast" `p.pos) [])])))
          (Term.byTactic
           "by"
           (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.exactModCast "exact_mod_cast" `q.pos) [])])))]))
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.exact
   "exact"
   (Term.app
    `Rat.le_def
    [(Term.byTactic
      "by"
      (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.exactModCast "exact_mod_cast" `p.pos) [])])))
     (Term.byTactic
      "by"
      (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.exactModCast "exact_mod_cast" `q.pos) [])])))]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.exact', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `Rat.le_def
   [(Term.byTactic
     "by"
     (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.exactModCast "exact_mod_cast" `p.pos) [])])))
    (Term.byTactic
     "by"
     (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.exactModCast "exact_mod_cast" `q.pos) [])])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.exactModCast "exact_mod_cast" `q.pos) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.exactModCast "exact_mod_cast" `q.pos)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.exactModCast', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `q.pos
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.byTactic
   "by"
   (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.exactModCast "exact_mod_cast" `q.pos) [])])))
  []]
 ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.exactModCast "exact_mod_cast" `p.pos) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.exactModCast "exact_mod_cast" `p.pos)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.exactModCast', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `p.pos
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, tactic) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.byTactic
   "by"
   (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.exactModCast "exact_mod_cast" `p.pos) [])])))
  []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Rat.le_def
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Mathlib.Tactic.Conv.convRHS
   "conv_rhs"
   []
   []
   "=>"
   (Tactic.Conv.convSeq
    (Tactic.Conv.convSeq1Indented
     [(group (Tactic.Conv.simp "simp" [] ["only"] ["[" [(Tactic.simpLemma [] [] `num_denom)] "]"] []) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Mathlib.Tactic.Conv.convRHS', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.Conv.simp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'only', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'only', expected 'Lean.Parser.Tactic.discharger'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.Conv.convSeq1Indented', expected 'Lean.Parser.Tactic.Conv.convSeqBracketed'
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
protected
  theorem
    le_def'
    { p q : ℚ } : p ≤ q ↔ p.num * q.denom ≤ q.num * p.denom
    :=
      by
        rw [ ← @ num_denom q , ← @ num_denom p ]
          conv_rhs => simp only [ num_denom ]
          exact Rat.le_def by exact_mod_cast p.pos by exact_mod_cast q.pos

protected theorem lt_def {p q : ℚ} : p < q ↔ (p.num*q.denom) < q.num*p.denom := by
  rw [lt_iff_le_and_ne, Rat.le_def']
  suffices p ≠ q ↔ (p.num*q.denom) ≠ q.num*p.denom by
    ·
      constructor <;> intro h
      ·
        exact lt_iff_le_and_ne.elim_right ⟨h.left, this.elim_left h.right⟩
      ·
        have tmp := lt_iff_le_and_ne.elim_left h
        exact ⟨tmp.left, this.elim_right tmp.right⟩
  exact not_iff_not.elim_right eq_iff_mul_eq_mul

theorem nonneg_iff_zero_le {a} : Rat.Nonneg a ↔ 0 ≤ a :=
  show Rat.Nonneg a ↔ Rat.Nonneg (a - 0)by
    simp

theorem num_nonneg_iff_zero_le : ∀ {a : ℚ}, 0 ≤ a.num ↔ 0 ≤ a
  | ⟨n, d, h, c⟩ => @nonneg_iff_zero_le ⟨n, d, h, c⟩

protected theorem add_le_add_left {a b c : ℚ} : ((c+a) ≤ c+b) ↔ a ≤ b := by
  unfold LE.le Rat.Le <;> rw [add_sub_add_left_eq_sub]

protected theorem mul_nonneg {a b : ℚ} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a*b := by
  rw [← nonneg_iff_zero_le] at ha hb⊢ <;> exact Rat.nonneg_mul ha hb

instance : LinearOrderedField ℚ :=
  { Rat.field, Rat.linearOrder, Rat.semiring with
    zero_le_one := by
      decide,
    add_le_add_left := fun a b ab c => Rat.add_le_add_left.2 ab,
    mul_pos := fun a b ha hb =>
      lt_of_le_of_neₓ (Rat.mul_nonneg (le_of_ltₓ ha) (le_of_ltₓ hb))
        (mul_ne_zero (ne_of_ltₓ ha).symm (ne_of_ltₓ hb).symm).symm }

instance : LinearOrderedCommRing ℚ := by
  infer_instance

instance : LinearOrderedRing ℚ := by
  infer_instance

instance : OrderedRing ℚ := by
  infer_instance

instance : LinearOrderedSemiring ℚ := by
  infer_instance

instance : OrderedSemiring ℚ := by
  infer_instance

instance : LinearOrderedAddCommGroup ℚ := by
  infer_instance

instance : OrderedAddCommGroup ℚ := by
  infer_instance

instance : OrderedCancelAddCommMonoid ℚ := by
  infer_instance

instance : OrderedAddCommMonoid ℚ := by
  infer_instance

theorem num_pos_iff_pos {a : ℚ} : 0 < a.num ↔ 0 < a :=
  lt_iff_lt_of_le_iff_le $ by
    simpa [(by
        cases a <;> rfl : (-a).num = -a.num)] using
      @num_nonneg_iff_zero_le (-a)

theorem div_lt_div_iff_mul_lt_mul {a b c d : ℤ} (b_pos : 0 < b) (d_pos : 0 < d) : (a : ℚ) / b < c / d ↔ (a*d) < c*b :=
  by
  simp only [lt_iff_le_not_leₓ]
  apply and_congr
  ·
    simp [div_num_denom, Rat.le_def b_pos d_pos]
  ·
    apply not_iff_not_of_iff
    simp [div_num_denom, Rat.le_def d_pos b_pos]

theorem lt_one_iff_num_lt_denom {q : ℚ} : q < 1 ↔ q.num < q.denom := by
  simp [Rat.lt_def]

theorem abs_def (q : ℚ) : |q| = q.num.nat_abs /. q.denom := by
  cases' le_totalₓ q 0 with hq hq
  ·
    rw [abs_of_nonpos hq]
    rw [← @num_denom q, ← mk_zero_one, Rat.le_def (Int.coe_nat_pos.2 q.pos) zero_lt_one, mul_oneₓ, zero_mul] at hq
    rw [Int.of_nat_nat_abs_of_nonpos hq, ← neg_def, num_denom]
  ·
    rw [abs_of_nonneg hq]
    rw [← @num_denom q, ← mk_zero_one, Rat.le_def zero_lt_one (Int.coe_nat_pos.2 q.pos), mul_oneₓ, zero_mul] at hq
    rw [Int.nat_abs_of_nonneg hq, num_denom]

end Rat

