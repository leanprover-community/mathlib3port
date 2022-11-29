/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathbin.Data.Int.LeastGreatest
import Mathbin.Data.Rat.Floor

/-!
# Archimedean groups and fields.

This file defines the archimedean property for ordered groups and proves several results connected
to this notion. Being archimedean means that for all elements `x` and `y>0` there exists a natural
number `n` such that `x ≤ n • y`.

## Main definitions

* `archimedean` is a typeclass for an ordered additive commutative monoid to have the archimedean
  property.
* `archimedean.floor_ring` defines a floor function on an archimedean linearly ordered ring making
  it into a `floor_ring`.

## Main statements

* `ℕ`, `ℤ`, and `ℚ` are archimedean.
-/


open Int Set

variable {α : Type _}

/-- An ordered additive commutative monoid is called `archimedean` if for any two elements `x`, `y`
such that `0 < y` there exists a natural number `n` such that `x ≤ n • y`. -/
class Archimedean (α) [OrderedAddCommMonoid α] : Prop where
  arch : ∀ (x : α) {y}, 0 < y → ∃ n : ℕ, x ≤ n • y
#align archimedean Archimedean

instance OrderDual.archimedean [OrderedAddCommGroup α] [Archimedean α] : Archimedean αᵒᵈ :=
  ⟨fun x y hy =>
    let ⟨n, hn⟩ := Archimedean.arch (-x : α) (neg_pos.2 hy)
    ⟨n, by rwa [neg_nsmul, neg_le_neg_iff] at hn⟩⟩
#align order_dual.archimedean OrderDual.archimedean

section LinearOrderedAddCommGroup

variable [LinearOrderedAddCommGroup α] [Archimedean α]

/-- An archimedean decidable linearly ordered `add_comm_group` has a version of the floor: for
`a > 0`, any `g` in the group lies between some two consecutive multiples of `a`. -/
theorem exists_unique_zsmul_near_of_pos {a : α} (ha : 0 < a) (g : α) :
    ∃! k : ℤ, k • a ≤ g ∧ g < (k + 1) • a := by
  let s : Set ℤ := { n : ℤ | n • a ≤ g }
  obtain ⟨k, hk : -g ≤ k • a⟩ := Archimedean.arch (-g) ha
  have h_ne : s.nonempty := ⟨-k, by simpa using neg_le_neg hk⟩
  obtain ⟨k, hk⟩ := Archimedean.arch g ha
  have h_bdd : ∀ n ∈ s, n ≤ (k : ℤ) := by
    intro n hn
    apply (zsmul_le_zsmul_iff ha).mp
    rw [← coe_nat_zsmul] at hk
    exact le_trans hn hk
  obtain ⟨m, hm, hm'⟩ := Int.exists_greatest_of_bdd ⟨k, h_bdd⟩ h_ne
  have hm'' : g < (m + 1) • a := by
    contrapose! hm'
    exact ⟨m + 1, hm', lt_add_one _⟩
  refine' ⟨m, ⟨hm, hm''⟩, fun n hn => (hm' n hn.1).antisymm <| Int.le_of_lt_add_one _⟩
  rw [← zsmul_lt_zsmul_iff ha]
  exact lt_of_le_of_lt hm hn.2
#align exists_unique_zsmul_near_of_pos exists_unique_zsmul_near_of_pos

theorem exists_unique_zsmul_near_of_pos' {a : α} (ha : 0 < a) (g : α) :
    ∃! k : ℤ, 0 ≤ g - k • a ∧ g - k • a < a := by
  simpa only [sub_nonneg, add_zsmul, one_zsmul, sub_lt_iff_lt_add'] using
    exists_unique_zsmul_near_of_pos ha g
#align exists_unique_zsmul_near_of_pos' exists_unique_zsmul_near_of_pos'

theorem exists_unique_add_zsmul_mem_Ico {a : α} (ha : 0 < a) (b c : α) :
    ∃! m : ℤ, b + m • a ∈ Set.ico c (c + a) :=
  (Equiv.neg ℤ).Bijective.exists_unique_iff.2 <| by
    simpa only [Equiv.neg_apply, mem_Ico, neg_zsmul, ← sub_eq_add_neg, le_sub_iff_add_le, zero_add,
      add_comm c, sub_lt_iff_lt_add', add_assoc] using exists_unique_zsmul_near_of_pos' ha (b - c)
#align exists_unique_add_zsmul_mem_Ico exists_unique_add_zsmul_mem_Ico

theorem exists_unique_add_zsmul_mem_Ioc {a : α} (ha : 0 < a) (b c : α) :
    ∃! m : ℤ, b + m • a ∈ Set.ioc c (c + a) :=
  (Equiv.addRight (1 : ℤ)).Bijective.exists_unique_iff.2 <| by
    simpa only [add_zsmul, sub_lt_iff_lt_add', le_sub_iff_add_le', ← add_assoc, and_comm, mem_Ioc,
      Equiv.coe_add_right, one_zsmul, add_le_add_iff_right] using
      exists_unique_zsmul_near_of_pos ha (c - b)
#align exists_unique_add_zsmul_mem_Ioc exists_unique_add_zsmul_mem_Ioc

end LinearOrderedAddCommGroup

theorem exists_nat_gt [StrictOrderedSemiring α] [Archimedean α] (x : α) : ∃ n : ℕ, x < n :=
  let ⟨n, h⟩ := Archimedean.arch x zero_lt_one
  ⟨n + 1, lt_of_le_of_lt (by rwa [← nsmul_one]) (Nat.cast_lt.2 (Nat.lt_succ_self _))⟩
#align exists_nat_gt exists_nat_gt

theorem exists_nat_ge [StrictOrderedSemiring α] [Archimedean α] (x : α) : ∃ n : ℕ, x ≤ n := by
  nontriviality α
  exact (exists_nat_gt x).imp fun n => le_of_lt
#align exists_nat_ge exists_nat_ge

theorem add_one_pow_unbounded_of_pos [StrictOrderedSemiring α] [Archimedean α] (x : α) {y : α}
    (hy : 0 < y) : ∃ n : ℕ, x < (y + 1) ^ n :=
  have : 0 ≤ 1 + y := add_nonneg zero_le_one hy.le
  let ⟨n, h⟩ := Archimedean.arch x hy
  ⟨n,
    calc
      x ≤ n • y := h
      _ = n * y := nsmul_eq_mul _ _
      _ < 1 + n * y := lt_one_add _
      _ ≤ (1 + y) ^ n :=
        one_add_mul_le_pow' (mul_nonneg hy.le hy.le) (mul_nonneg this this)
          (add_nonneg zero_le_two hy.le) _
      _ = (y + 1) ^ n := by rw [add_comm]
      ⟩
#align add_one_pow_unbounded_of_pos add_one_pow_unbounded_of_pos

section StrictOrderedRing

variable [StrictOrderedRing α] [Archimedean α]

theorem pow_unbounded_of_one_lt (x : α) {y : α} (hy1 : 1 < y) : ∃ n : ℕ, x < y ^ n :=
  sub_add_cancel y 1 ▸ add_one_pow_unbounded_of_pos _ (sub_pos.2 hy1)
#align pow_unbounded_of_one_lt pow_unbounded_of_one_lt

theorem exists_int_gt (x : α) : ∃ n : ℤ, x < n :=
  let ⟨n, h⟩ := exists_nat_gt x
  ⟨n, by rwa [Int.cast_ofNat]⟩
#align exists_int_gt exists_int_gt

theorem exists_int_lt (x : α) : ∃ n : ℤ, (n : α) < x :=
  let ⟨n, h⟩ := exists_int_gt (-x)
  ⟨-n, by rw [Int.cast_neg] <;> exact neg_lt.1 h⟩
#align exists_int_lt exists_int_lt

theorem exists_floor (x : α) : ∃ fl : ℤ, ∀ z : ℤ, z ≤ fl ↔ (z : α) ≤ x := by
  haveI := Classical.propDecidable
  have : ∃ ub : ℤ, (ub : α) ≤ x ∧ ∀ z : ℤ, (z : α) ≤ x → z ≤ ub :=
    Int.exists_greatest_of_bdd
      (let ⟨n, hn⟩ := exists_int_gt x
      ⟨n, fun z h' => Int.cast_le.1 <| le_trans h' <| le_of_lt hn⟩)
      (let ⟨n, hn⟩ := exists_int_lt x
      ⟨n, le_of_lt hn⟩)
  refine' this.imp fun fl h z => _
  cases' h with h₁ h₂
  exact ⟨fun h => le_trans (Int.cast_le.2 h) h₁, h₂ z⟩
#align exists_floor exists_floor

end StrictOrderedRing

section LinearOrderedRing

variable [LinearOrderedRing α] [Archimedean α]

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "Every x greater than or equal to 1 is between two successive\nnatural-number powers of every y greater than one. -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `exists_nat_pow_near [])
      (Command.declSig
       [(Term.implicitBinder "{" [`x] [":" `α] "}")
        (Term.implicitBinder "{" [`y] [":" `α] "}")
        (Term.explicitBinder "(" [`hx] [":" («term_≤_» (num "1") "≤" `x)] [] ")")
        (Term.explicitBinder "(" [`hy] [":" («term_<_» (num "1") "<" `y)] [] ")")]
       (Term.typeSpec
        ":"
        («term∃_,_»
         "∃"
         (Lean.explicitBinders
          (Lean.unbracketedExplicitBinders [(Lean.binderIdent `n)] [":" (termℕ "ℕ")]))
         ","
         («term_∧_»
          («term_≤_» («term_^_» `y "^" `n) "≤" `x)
          "∧"
          («term_<_» `x "<" («term_^_» `y "^" («term_+_» `n "+" (num "1"))))))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`h []]
              [(Term.typeSpec
                ":"
                («term∃_,_»
                 "∃"
                 (Lean.explicitBinders
                  (Lean.unbracketedExplicitBinders [(Lean.binderIdent `n)] [":" (termℕ "ℕ")]))
                 ","
                 («term_<_» `x "<" («term_^_» `y "^" `n))))]
              ":="
              (Term.app `pow_unbounded_of_one_lt [(Term.hole "_") `hy]))))
           []
           (Tactic.«tactic_<;>_»
            (Mathlib.Tactic.tacticClassical_ (Tactic.skip "skip"))
            "<;>"
            (Tactic.exact
             "exact"
             (Term.let
              "let"
              (Term.letDecl (Term.letIdDecl `n [] [] ":=" (Term.app `Nat.find [`h])))
              []
              (Term.have
               "have"
               (Term.haveDecl
                (Term.haveIdDecl
                 [`hn []]
                 [(Term.typeSpec ":" («term_<_» `x "<" («term_^_» `y "^" `n)))]
                 ":="
                 (Term.app `Nat.find_spec [`h])))
               []
               (Term.have
                "have"
                (Term.haveDecl
                 (Term.haveIdDecl
                  [`hnp []]
                  [(Term.typeSpec ":" («term_<_» (num "0") "<" `n))]
                  ":="
                  (Term.app
                   (Term.proj `pos_iff_ne_zero "." (fieldIdx "2"))
                   [(Term.fun
                     "fun"
                     (Term.basicFun
                      [`hn0]
                      []
                      "=>"
                      (Term.byTactic
                       "by"
                       (Tactic.tacticSeq
                        (Tactic.tacticSeq1Indented
                         [(Tactic.«tactic_<;>_»
                           (Tactic.rwSeq
                            "rw"
                            []
                            (Tactic.rwRuleSeq
                             "["
                             [(Tactic.rwRule [] `hn0) "," (Tactic.rwRule [] `pow_zero)]
                             "]")
                            [(Tactic.location "at" (Tactic.locationHyp [`hn] []))])
                           "<;>"
                           (Tactic.exact "exact" (Term.app `not_le_of_gt [`hn `hx])))])))))])))
                []
                (Term.have
                 "have"
                 (Term.haveDecl
                  (Term.haveIdDecl
                   [`hnsp []]
                   [(Term.typeSpec
                     ":"
                     («term_=_» («term_+_» (Term.app `Nat.pred [`n]) "+" (num "1")) "=" `n))]
                   ":="
                   (Term.app `Nat.succ_pred_eq_of_pos [`hnp])))
                 []
                 (Term.have
                  "have"
                  (Term.haveDecl
                   (Term.haveIdDecl
                    [`hltn []]
                    [(Term.typeSpec ":" («term_<_» (Term.app `Nat.pred [`n]) "<" `n))]
                    ":="
                    (Term.app `Nat.pred_lt [(Term.app `ne_of_gt [`hnp])])))
                  []
                  (Term.anonymousCtor
                   "⟨"
                   [(Term.app `Nat.pred [`n])
                    ","
                    (Term.app `le_of_not_lt [(Term.app `Nat.find_min [`h `hltn])])
                    ","
                    (Term.byTactic
                     "by"
                     (Tactic.tacticSeq
                      (Tactic.tacticSeq1Indented
                       [(Std.Tactic.tacticRwa__
                         "rwa"
                         (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `hnsp)] "]")
                         [])])))]
                   "⟩"))))))))])))
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
         [(Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`h []]
             [(Term.typeSpec
               ":"
               («term∃_,_»
                "∃"
                (Lean.explicitBinders
                 (Lean.unbracketedExplicitBinders [(Lean.binderIdent `n)] [":" (termℕ "ℕ")]))
                ","
                («term_<_» `x "<" («term_^_» `y "^" `n))))]
             ":="
             (Term.app `pow_unbounded_of_one_lt [(Term.hole "_") `hy]))))
          []
          (Tactic.«tactic_<;>_»
           (Mathlib.Tactic.tacticClassical_ (Tactic.skip "skip"))
           "<;>"
           (Tactic.exact
            "exact"
            (Term.let
             "let"
             (Term.letDecl (Term.letIdDecl `n [] [] ":=" (Term.app `Nat.find [`h])))
             []
             (Term.have
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                [`hn []]
                [(Term.typeSpec ":" («term_<_» `x "<" («term_^_» `y "^" `n)))]
                ":="
                (Term.app `Nat.find_spec [`h])))
              []
              (Term.have
               "have"
               (Term.haveDecl
                (Term.haveIdDecl
                 [`hnp []]
                 [(Term.typeSpec ":" («term_<_» (num "0") "<" `n))]
                 ":="
                 (Term.app
                  (Term.proj `pos_iff_ne_zero "." (fieldIdx "2"))
                  [(Term.fun
                    "fun"
                    (Term.basicFun
                     [`hn0]
                     []
                     "=>"
                     (Term.byTactic
                      "by"
                      (Tactic.tacticSeq
                       (Tactic.tacticSeq1Indented
                        [(Tactic.«tactic_<;>_»
                          (Tactic.rwSeq
                           "rw"
                           []
                           (Tactic.rwRuleSeq
                            "["
                            [(Tactic.rwRule [] `hn0) "," (Tactic.rwRule [] `pow_zero)]
                            "]")
                           [(Tactic.location "at" (Tactic.locationHyp [`hn] []))])
                          "<;>"
                          (Tactic.exact "exact" (Term.app `not_le_of_gt [`hn `hx])))])))))])))
               []
               (Term.have
                "have"
                (Term.haveDecl
                 (Term.haveIdDecl
                  [`hnsp []]
                  [(Term.typeSpec
                    ":"
                    («term_=_» («term_+_» (Term.app `Nat.pred [`n]) "+" (num "1")) "=" `n))]
                  ":="
                  (Term.app `Nat.succ_pred_eq_of_pos [`hnp])))
                []
                (Term.have
                 "have"
                 (Term.haveDecl
                  (Term.haveIdDecl
                   [`hltn []]
                   [(Term.typeSpec ":" («term_<_» (Term.app `Nat.pred [`n]) "<" `n))]
                   ":="
                   (Term.app `Nat.pred_lt [(Term.app `ne_of_gt [`hnp])])))
                 []
                 (Term.anonymousCtor
                  "⟨"
                  [(Term.app `Nat.pred [`n])
                   ","
                   (Term.app `le_of_not_lt [(Term.app `Nat.find_min [`h `hltn])])
                   ","
                   (Term.byTactic
                    "by"
                    (Tactic.tacticSeq
                     (Tactic.tacticSeq1Indented
                      [(Std.Tactic.tacticRwa__
                        "rwa"
                        (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `hnsp)] "]")
                        [])])))]
                  "⟩"))))))))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.«tactic_<;>_»
       (Mathlib.Tactic.tacticClassical_ (Tactic.skip "skip"))
       "<;>"
       (Tactic.exact
        "exact"
        (Term.let
         "let"
         (Term.letDecl (Term.letIdDecl `n [] [] ":=" (Term.app `Nat.find [`h])))
         []
         (Term.have
          "have"
          (Term.haveDecl
           (Term.haveIdDecl
            [`hn []]
            [(Term.typeSpec ":" («term_<_» `x "<" («term_^_» `y "^" `n)))]
            ":="
            (Term.app `Nat.find_spec [`h])))
          []
          (Term.have
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`hnp []]
             [(Term.typeSpec ":" («term_<_» (num "0") "<" `n))]
             ":="
             (Term.app
              (Term.proj `pos_iff_ne_zero "." (fieldIdx "2"))
              [(Term.fun
                "fun"
                (Term.basicFun
                 [`hn0]
                 []
                 "=>"
                 (Term.byTactic
                  "by"
                  (Tactic.tacticSeq
                   (Tactic.tacticSeq1Indented
                    [(Tactic.«tactic_<;>_»
                      (Tactic.rwSeq
                       "rw"
                       []
                       (Tactic.rwRuleSeq
                        "["
                        [(Tactic.rwRule [] `hn0) "," (Tactic.rwRule [] `pow_zero)]
                        "]")
                       [(Tactic.location "at" (Tactic.locationHyp [`hn] []))])
                      "<;>"
                      (Tactic.exact "exact" (Term.app `not_le_of_gt [`hn `hx])))])))))])))
           []
           (Term.have
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`hnsp []]
              [(Term.typeSpec
                ":"
                («term_=_» («term_+_» (Term.app `Nat.pred [`n]) "+" (num "1")) "=" `n))]
              ":="
              (Term.app `Nat.succ_pred_eq_of_pos [`hnp])))
            []
            (Term.have
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               [`hltn []]
               [(Term.typeSpec ":" («term_<_» (Term.app `Nat.pred [`n]) "<" `n))]
               ":="
               (Term.app `Nat.pred_lt [(Term.app `ne_of_gt [`hnp])])))
             []
             (Term.anonymousCtor
              "⟨"
              [(Term.app `Nat.pred [`n])
               ","
               (Term.app `le_of_not_lt [(Term.app `Nat.find_min [`h `hltn])])
               ","
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(Std.Tactic.tacticRwa__
                    "rwa"
                    (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `hnsp)] "]")
                    [])])))]
              "⟩"))))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.let
        "let"
        (Term.letDecl (Term.letIdDecl `n [] [] ":=" (Term.app `Nat.find [`h])))
        []
        (Term.have
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`hn []]
           [(Term.typeSpec ":" («term_<_» `x "<" («term_^_» `y "^" `n)))]
           ":="
           (Term.app `Nat.find_spec [`h])))
         []
         (Term.have
          "have"
          (Term.haveDecl
           (Term.haveIdDecl
            [`hnp []]
            [(Term.typeSpec ":" («term_<_» (num "0") "<" `n))]
            ":="
            (Term.app
             (Term.proj `pos_iff_ne_zero "." (fieldIdx "2"))
             [(Term.fun
               "fun"
               (Term.basicFun
                [`hn0]
                []
                "=>"
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(Tactic.«tactic_<;>_»
                     (Tactic.rwSeq
                      "rw"
                      []
                      (Tactic.rwRuleSeq
                       "["
                       [(Tactic.rwRule [] `hn0) "," (Tactic.rwRule [] `pow_zero)]
                       "]")
                      [(Tactic.location "at" (Tactic.locationHyp [`hn] []))])
                     "<;>"
                     (Tactic.exact "exact" (Term.app `not_le_of_gt [`hn `hx])))])))))])))
          []
          (Term.have
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`hnsp []]
             [(Term.typeSpec
               ":"
               («term_=_» («term_+_» (Term.app `Nat.pred [`n]) "+" (num "1")) "=" `n))]
             ":="
             (Term.app `Nat.succ_pred_eq_of_pos [`hnp])))
           []
           (Term.have
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`hltn []]
              [(Term.typeSpec ":" («term_<_» (Term.app `Nat.pred [`n]) "<" `n))]
              ":="
              (Term.app `Nat.pred_lt [(Term.app `ne_of_gt [`hnp])])))
            []
            (Term.anonymousCtor
             "⟨"
             [(Term.app `Nat.pred [`n])
              ","
              (Term.app `le_of_not_lt [(Term.app `Nat.find_min [`h `hltn])])
              ","
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Std.Tactic.tacticRwa__
                   "rwa"
                   (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `hnsp)] "]")
                   [])])))]
             "⟩")))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.let
       "let"
       (Term.letDecl (Term.letIdDecl `n [] [] ":=" (Term.app `Nat.find [`h])))
       []
       (Term.have
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`hn []]
          [(Term.typeSpec ":" («term_<_» `x "<" («term_^_» `y "^" `n)))]
          ":="
          (Term.app `Nat.find_spec [`h])))
        []
        (Term.have
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`hnp []]
           [(Term.typeSpec ":" («term_<_» (num "0") "<" `n))]
           ":="
           (Term.app
            (Term.proj `pos_iff_ne_zero "." (fieldIdx "2"))
            [(Term.fun
              "fun"
              (Term.basicFun
               [`hn0]
               []
               "=>"
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(Tactic.«tactic_<;>_»
                    (Tactic.rwSeq
                     "rw"
                     []
                     (Tactic.rwRuleSeq
                      "["
                      [(Tactic.rwRule [] `hn0) "," (Tactic.rwRule [] `pow_zero)]
                      "]")
                     [(Tactic.location "at" (Tactic.locationHyp [`hn] []))])
                    "<;>"
                    (Tactic.exact "exact" (Term.app `not_le_of_gt [`hn `hx])))])))))])))
         []
         (Term.have
          "have"
          (Term.haveDecl
           (Term.haveIdDecl
            [`hnsp []]
            [(Term.typeSpec
              ":"
              («term_=_» («term_+_» (Term.app `Nat.pred [`n]) "+" (num "1")) "=" `n))]
            ":="
            (Term.app `Nat.succ_pred_eq_of_pos [`hnp])))
          []
          (Term.have
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`hltn []]
             [(Term.typeSpec ":" («term_<_» (Term.app `Nat.pred [`n]) "<" `n))]
             ":="
             (Term.app `Nat.pred_lt [(Term.app `ne_of_gt [`hnp])])))
           []
           (Term.anonymousCtor
            "⟨"
            [(Term.app `Nat.pred [`n])
             ","
             (Term.app `le_of_not_lt [(Term.app `Nat.find_min [`h `hltn])])
             ","
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Std.Tactic.tacticRwa__
                  "rwa"
                  (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `hnsp)] "]")
                  [])])))]
            "⟩"))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.have
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`hn []]
         [(Term.typeSpec ":" («term_<_» `x "<" («term_^_» `y "^" `n)))]
         ":="
         (Term.app `Nat.find_spec [`h])))
       []
       (Term.have
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`hnp []]
          [(Term.typeSpec ":" («term_<_» (num "0") "<" `n))]
          ":="
          (Term.app
           (Term.proj `pos_iff_ne_zero "." (fieldIdx "2"))
           [(Term.fun
             "fun"
             (Term.basicFun
              [`hn0]
              []
              "=>"
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Tactic.«tactic_<;>_»
                   (Tactic.rwSeq
                    "rw"
                    []
                    (Tactic.rwRuleSeq
                     "["
                     [(Tactic.rwRule [] `hn0) "," (Tactic.rwRule [] `pow_zero)]
                     "]")
                    [(Tactic.location "at" (Tactic.locationHyp [`hn] []))])
                   "<;>"
                   (Tactic.exact "exact" (Term.app `not_le_of_gt [`hn `hx])))])))))])))
        []
        (Term.have
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`hnsp []]
           [(Term.typeSpec
             ":"
             («term_=_» («term_+_» (Term.app `Nat.pred [`n]) "+" (num "1")) "=" `n))]
           ":="
           (Term.app `Nat.succ_pred_eq_of_pos [`hnp])))
         []
         (Term.have
          "have"
          (Term.haveDecl
           (Term.haveIdDecl
            [`hltn []]
            [(Term.typeSpec ":" («term_<_» (Term.app `Nat.pred [`n]) "<" `n))]
            ":="
            (Term.app `Nat.pred_lt [(Term.app `ne_of_gt [`hnp])])))
          []
          (Term.anonymousCtor
           "⟨"
           [(Term.app `Nat.pred [`n])
            ","
            (Term.app `le_of_not_lt [(Term.app `Nat.find_min [`h `hltn])])
            ","
            (Term.byTactic
             "by"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(Std.Tactic.tacticRwa__
                 "rwa"
                 (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `hnsp)] "]")
                 [])])))]
           "⟩")))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.have
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`hnp []]
         [(Term.typeSpec ":" («term_<_» (num "0") "<" `n))]
         ":="
         (Term.app
          (Term.proj `pos_iff_ne_zero "." (fieldIdx "2"))
          [(Term.fun
            "fun"
            (Term.basicFun
             [`hn0]
             []
             "=>"
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.«tactic_<;>_»
                  (Tactic.rwSeq
                   "rw"
                   []
                   (Tactic.rwRuleSeq
                    "["
                    [(Tactic.rwRule [] `hn0) "," (Tactic.rwRule [] `pow_zero)]
                    "]")
                   [(Tactic.location "at" (Tactic.locationHyp [`hn] []))])
                  "<;>"
                  (Tactic.exact "exact" (Term.app `not_le_of_gt [`hn `hx])))])))))])))
       []
       (Term.have
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`hnsp []]
          [(Term.typeSpec
            ":"
            («term_=_» («term_+_» (Term.app `Nat.pred [`n]) "+" (num "1")) "=" `n))]
          ":="
          (Term.app `Nat.succ_pred_eq_of_pos [`hnp])))
        []
        (Term.have
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`hltn []]
           [(Term.typeSpec ":" («term_<_» (Term.app `Nat.pred [`n]) "<" `n))]
           ":="
           (Term.app `Nat.pred_lt [(Term.app `ne_of_gt [`hnp])])))
         []
         (Term.anonymousCtor
          "⟨"
          [(Term.app `Nat.pred [`n])
           ","
           (Term.app `le_of_not_lt [(Term.app `Nat.find_min [`h `hltn])])
           ","
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Std.Tactic.tacticRwa__
                "rwa"
                (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `hnsp)] "]")
                [])])))]
          "⟩"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.have
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`hnsp []]
         [(Term.typeSpec
           ":"
           («term_=_» («term_+_» (Term.app `Nat.pred [`n]) "+" (num "1")) "=" `n))]
         ":="
         (Term.app `Nat.succ_pred_eq_of_pos [`hnp])))
       []
       (Term.have
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`hltn []]
          [(Term.typeSpec ":" («term_<_» (Term.app `Nat.pred [`n]) "<" `n))]
          ":="
          (Term.app `Nat.pred_lt [(Term.app `ne_of_gt [`hnp])])))
        []
        (Term.anonymousCtor
         "⟨"
         [(Term.app `Nat.pred [`n])
          ","
          (Term.app `le_of_not_lt [(Term.app `Nat.find_min [`h `hltn])])
          ","
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(Std.Tactic.tacticRwa__
               "rwa"
               (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `hnsp)] "]")
               [])])))]
         "⟩")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.have
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`hltn []]
         [(Term.typeSpec ":" («term_<_» (Term.app `Nat.pred [`n]) "<" `n))]
         ":="
         (Term.app `Nat.pred_lt [(Term.app `ne_of_gt [`hnp])])))
       []
       (Term.anonymousCtor
        "⟨"
        [(Term.app `Nat.pred [`n])
         ","
         (Term.app `le_of_not_lt [(Term.app `Nat.find_min [`h `hltn])])
         ","
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Std.Tactic.tacticRwa__
              "rwa"
              (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `hnsp)] "]")
              [])])))]
        "⟩"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.app `Nat.pred [`n])
        ","
        (Term.app `le_of_not_lt [(Term.app `Nat.find_min [`h `hltn])])
        ","
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Std.Tactic.tacticRwa__
             "rwa"
             (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `hnsp)] "]")
             [])])))]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Std.Tactic.tacticRwa__
           "rwa"
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `hnsp)] "]")
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.tacticRwa__ "rwa" (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `hnsp)] "]") [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hnsp
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `le_of_not_lt [(Term.app `Nat.find_min [`h `hltn])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Nat.find_min [`h `hltn])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hltn
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Nat.find_min
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `Nat.find_min [`h `hltn]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `le_of_not_lt
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Nat.pred [`n])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Nat.pred
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Nat.pred_lt [(Term.app `ne_of_gt [`hnp])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `ne_of_gt [`hnp])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hnp
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `ne_of_gt
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `ne_of_gt [`hnp]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Nat.pred_lt
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<_» (Term.app `Nat.pred [`n]) "<" `n)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app `Nat.pred [`n])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Nat.pred
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Nat.succ_pred_eq_of_pos [`hnp])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hnp
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Nat.succ_pred_eq_of_pos
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_» («term_+_» (Term.app `Nat.pred [`n]) "+" (num "1")) "=" `n)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      («term_+_» (Term.app `Nat.pred [`n]) "+" (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      (Term.app `Nat.pred [`n])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Nat.pred
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1022, (some 1023, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 65, (some 66, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj `pos_iff_ne_zero "." (fieldIdx "2"))
       [(Term.fun
         "fun"
         (Term.basicFun
          [`hn0]
          []
          "=>"
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(Tactic.«tactic_<;>_»
               (Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule [] `hn0) "," (Tactic.rwRule [] `pow_zero)]
                 "]")
                [(Tactic.location "at" (Tactic.locationHyp [`hn] []))])
               "<;>"
               (Tactic.exact "exact" (Term.app `not_le_of_gt [`hn `hx])))])))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`hn0]
        []
        "=>"
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Tactic.«tactic_<;>_»
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `hn0) "," (Tactic.rwRule [] `pow_zero)] "]")
              [(Tactic.location "at" (Tactic.locationHyp [`hn] []))])
             "<;>"
             (Tactic.exact "exact" (Term.app `not_le_of_gt [`hn `hx])))])))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.«tactic_<;>_»
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `hn0) "," (Tactic.rwRule [] `pow_zero)] "]")
            [(Tactic.location "at" (Tactic.locationHyp [`hn] []))])
           "<;>"
           (Tactic.exact "exact" (Term.app `not_le_of_gt [`hn `hx])))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.«tactic_<;>_»
       (Tactic.rwSeq
        "rw"
        []
        (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `hn0) "," (Tactic.rwRule [] `pow_zero)] "]")
        [(Tactic.location "at" (Tactic.locationHyp [`hn] []))])
       "<;>"
       (Tactic.exact "exact" (Term.app `not_le_of_gt [`hn `hx])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" (Term.app `not_le_of_gt [`hn `hx]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `not_le_of_gt [`hn `hx])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hx
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hn
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `not_le_of_gt
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 2 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `hn0) "," (Tactic.rwRule [] `pow_zero)] "]")
       [(Tactic.location "at" (Tactic.locationHyp [`hn] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hn
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `pow_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hn0
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hn0
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `pos_iff_ne_zero "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `pos_iff_ne_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<_» (num "0") "<" `n)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Nat.find_spec [`h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Nat.find_spec
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<_» `x "<" («term_^_» `y "^" `n))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_» `y "^" `n)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      `y
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Nat.find [`h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Nat.find
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 2 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
      (Mathlib.Tactic.tacticClassical_ (Tactic.skip "skip"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.skip', expected 'Lean.Parser.Tactic.tacticSeq'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    Every x greater than or equal to 1 is between two successive
    natural-number powers of every y greater than one. -/
  theorem
    exists_nat_pow_near
    { x : α } { y : α } ( hx : 1 ≤ x ) ( hy : 1 < y ) : ∃ n : ℕ , y ^ n ≤ x ∧ x < y ^ n + 1
    :=
      by
        have h : ∃ n : ℕ , x < y ^ n := pow_unbounded_of_one_lt _ hy
          skip
            <;>
            exact
              let
                n := Nat.find h
                have
                  hn : x < y ^ n := Nat.find_spec h
                  have
                    hnp
                      : 0 < n
                      :=
                      pos_iff_ne_zero . 2
                        fun hn0 => by rw [ hn0 , pow_zero ] at hn <;> exact not_le_of_gt hn hx
                    have
                      hnsp : Nat.pred n + 1 = n := Nat.succ_pred_eq_of_pos hnp
                      have
                        hltn : Nat.pred n < n := Nat.pred_lt ne_of_gt hnp
                        ⟨ Nat.pred n , le_of_not_lt Nat.find_min h hltn , by rwa [ hnsp ] ⟩
#align exists_nat_pow_near exists_nat_pow_near

end LinearOrderedRing

section LinearOrderedField

variable [LinearOrderedField α] [Archimedean α] {x y ε : α}

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "Every positive `x` is between two successive integer powers of\nanother `y` greater than one. This is the same as `exists_mem_Ioc_zpow`,\nbut with ≤ and < the other way around. -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `exists_mem_Ico_zpow [])
      (Command.declSig
       [(Term.explicitBinder "(" [`hx] [":" («term_<_» (num "0") "<" `x)] [] ")")
        (Term.explicitBinder "(" [`hy] [":" («term_<_» (num "1") "<" `y)] [] ")")]
       (Term.typeSpec
        ":"
        («term∃_,_»
         "∃"
         (Lean.explicitBinders
          (Lean.unbracketedExplicitBinders [(Lean.binderIdent `n)] [":" (termℤ "ℤ")]))
         ","
         («term_∈_»
          `x
          "∈"
          (Term.app
           `ico
           [(«term_^_» `y "^" `n) («term_^_» `y "^" («term_+_» `n "+" (num "1")))])))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.«tactic_<;>_»
            (Mathlib.Tactic.tacticClassical_ (Tactic.skip "skip"))
            "<;>"
            (Tactic.exact
             "exact"
             (Term.let
              "let"
              (Term.letDecl
               (Term.letPatDecl
                (Term.anonymousCtor "⟨" [`N "," `hN] "⟩")
                []
                []
                ":="
                (Term.app `pow_unbounded_of_one_lt [(«term_⁻¹_1» `x "⁻¹") `hy])))
              []
              (Term.have
               "have"
               (Term.haveDecl
                (Term.haveIdDecl
                 [`he []]
                 [(Term.typeSpec
                   ":"
                   («term∃_,_»
                    "∃"
                    (Lean.explicitBinders
                     (Lean.unbracketedExplicitBinders [(Lean.binderIdent `m)] [":" (termℤ "ℤ")]))
                    ","
                    («term_≤_» («term_^_» `y "^" `m) "≤" `x)))]
                 ":="
                 (Term.anonymousCtor
                  "⟨"
                  [(«term-_» "-" `N)
                   ","
                   (Term.app
                    `le_of_lt
                    [(Term.byTactic
                      "by"
                      (Tactic.tacticSeq
                       (Tactic.tacticSeq1Indented
                        [(Tactic.rwSeq
                          "rw"
                          []
                          (Tactic.rwRuleSeq
                           "["
                           [(Tactic.rwRule [] (Term.app `zpow_neg [`y (coeNotation "↑" `N)]))
                            ","
                            (Tactic.rwRule [] `zpow_coe_nat)]
                           "]")
                          [])
                         []
                         (Tactic.exact
                          "exact"
                          (Term.app
                           (Term.proj
                            (Term.app
                             `inv_lt
                             [`hx
                              (Term.app
                               `lt_trans
                               [(Term.app (Term.proj `inv_pos "." (fieldIdx "2")) [`hx]) `hN])])
                            "."
                            (fieldIdx "1"))
                           [`hN]))])))])]
                  "⟩")))
               []
               (Term.let
                "let"
                (Term.letDecl
                 (Term.letPatDecl
                  (Term.anonymousCtor "⟨" [`M "," `hM] "⟩")
                  []
                  []
                  ":="
                  (Term.app `pow_unbounded_of_one_lt [`x `hy])))
                []
                (Term.have
                 "have"
                 (Term.haveDecl
                  (Term.haveIdDecl
                   [`hb []]
                   [(Term.typeSpec
                     ":"
                     («term∃_,_»
                      "∃"
                      (Lean.explicitBinders
                       (Lean.unbracketedExplicitBinders [(Lean.binderIdent `b)] [":" (termℤ "ℤ")]))
                      ","
                      (Term.forall
                       "∀"
                       [`m]
                       []
                       ","
                       (Term.arrow
                        («term_≤_» («term_^_» `y "^" `m) "≤" `x)
                        "→"
                        («term_≤_» `m "≤" `b)))))]
                   ":="
                   (Term.anonymousCtor
                    "⟨"
                    [`M
                     ","
                     (Term.fun
                      "fun"
                      (Term.basicFun
                       [`m `hm]
                       []
                       "=>"
                       (Term.app
                        `le_of_not_lt
                        [(Term.fun
                          "fun"
                          (Term.basicFun
                           [`hlt]
                           []
                           "=>"
                           (Term.app
                            `not_lt_of_ge
                            [(Term.app `zpow_le_of_le [`hy.le (Term.proj `hlt "." `le)])
                             (Term.app
                              `lt_of_le_of_lt
                              [`hm
                               (Term.byTactic
                                "by"
                                (Tactic.tacticSeq
                                 (Tactic.tacticSeq1Indented
                                  [(Std.Tactic.tacticRwa__
                                    "rwa"
                                    (Tactic.rwRuleSeq
                                     "["
                                     [(Tactic.rwRule
                                       [(patternIgnore (token.«← » "←"))]
                                       `zpow_coe_nat)]
                                     "]")
                                    [(Tactic.location
                                      "at"
                                      (Tactic.locationHyp [`hM] []))])])))])])))])))]
                    "⟩")))
                 []
                 (Term.let
                  "let"
                  (Term.letDecl
                   (Term.letPatDecl
                    (Term.anonymousCtor "⟨" [`n "," `hn₁ "," `hn₂] "⟩")
                    []
                    []
                    ":="
                    (Term.app `Int.exists_greatest_of_bdd [`hb `he])))
                  []
                  (Term.anonymousCtor
                   "⟨"
                   [`n
                    ","
                    `hn₁
                    ","
                    (Term.app
                     `lt_of_not_ge
                     [(Term.fun
                       "fun"
                       (Term.basicFun
                        [`hge]
                        []
                        "=>"
                        (Term.app
                         `not_le_of_gt
                         [(Term.app `Int.lt_succ [(Term.hole "_")])
                          (Term.app `hn₂ [(Term.hole "_") `hge])])))])]
                   "⟩"))))))))])))
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
         [(Tactic.«tactic_<;>_»
           (Mathlib.Tactic.tacticClassical_ (Tactic.skip "skip"))
           "<;>"
           (Tactic.exact
            "exact"
            (Term.let
             "let"
             (Term.letDecl
              (Term.letPatDecl
               (Term.anonymousCtor "⟨" [`N "," `hN] "⟩")
               []
               []
               ":="
               (Term.app `pow_unbounded_of_one_lt [(«term_⁻¹_1» `x "⁻¹") `hy])))
             []
             (Term.have
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                [`he []]
                [(Term.typeSpec
                  ":"
                  («term∃_,_»
                   "∃"
                   (Lean.explicitBinders
                    (Lean.unbracketedExplicitBinders [(Lean.binderIdent `m)] [":" (termℤ "ℤ")]))
                   ","
                   («term_≤_» («term_^_» `y "^" `m) "≤" `x)))]
                ":="
                (Term.anonymousCtor
                 "⟨"
                 [(«term-_» "-" `N)
                  ","
                  (Term.app
                   `le_of_lt
                   [(Term.byTactic
                     "by"
                     (Tactic.tacticSeq
                      (Tactic.tacticSeq1Indented
                       [(Tactic.rwSeq
                         "rw"
                         []
                         (Tactic.rwRuleSeq
                          "["
                          [(Tactic.rwRule [] (Term.app `zpow_neg [`y (coeNotation "↑" `N)]))
                           ","
                           (Tactic.rwRule [] `zpow_coe_nat)]
                          "]")
                         [])
                        []
                        (Tactic.exact
                         "exact"
                         (Term.app
                          (Term.proj
                           (Term.app
                            `inv_lt
                            [`hx
                             (Term.app
                              `lt_trans
                              [(Term.app (Term.proj `inv_pos "." (fieldIdx "2")) [`hx]) `hN])])
                           "."
                           (fieldIdx "1"))
                          [`hN]))])))])]
                 "⟩")))
              []
              (Term.let
               "let"
               (Term.letDecl
                (Term.letPatDecl
                 (Term.anonymousCtor "⟨" [`M "," `hM] "⟩")
                 []
                 []
                 ":="
                 (Term.app `pow_unbounded_of_one_lt [`x `hy])))
               []
               (Term.have
                "have"
                (Term.haveDecl
                 (Term.haveIdDecl
                  [`hb []]
                  [(Term.typeSpec
                    ":"
                    («term∃_,_»
                     "∃"
                     (Lean.explicitBinders
                      (Lean.unbracketedExplicitBinders [(Lean.binderIdent `b)] [":" (termℤ "ℤ")]))
                     ","
                     (Term.forall
                      "∀"
                      [`m]
                      []
                      ","
                      (Term.arrow
                       («term_≤_» («term_^_» `y "^" `m) "≤" `x)
                       "→"
                       («term_≤_» `m "≤" `b)))))]
                  ":="
                  (Term.anonymousCtor
                   "⟨"
                   [`M
                    ","
                    (Term.fun
                     "fun"
                     (Term.basicFun
                      [`m `hm]
                      []
                      "=>"
                      (Term.app
                       `le_of_not_lt
                       [(Term.fun
                         "fun"
                         (Term.basicFun
                          [`hlt]
                          []
                          "=>"
                          (Term.app
                           `not_lt_of_ge
                           [(Term.app `zpow_le_of_le [`hy.le (Term.proj `hlt "." `le)])
                            (Term.app
                             `lt_of_le_of_lt
                             [`hm
                              (Term.byTactic
                               "by"
                               (Tactic.tacticSeq
                                (Tactic.tacticSeq1Indented
                                 [(Std.Tactic.tacticRwa__
                                   "rwa"
                                   (Tactic.rwRuleSeq
                                    "["
                                    [(Tactic.rwRule
                                      [(patternIgnore (token.«← » "←"))]
                                      `zpow_coe_nat)]
                                    "]")
                                   [(Tactic.location
                                     "at"
                                     (Tactic.locationHyp [`hM] []))])])))])])))])))]
                   "⟩")))
                []
                (Term.let
                 "let"
                 (Term.letDecl
                  (Term.letPatDecl
                   (Term.anonymousCtor "⟨" [`n "," `hn₁ "," `hn₂] "⟩")
                   []
                   []
                   ":="
                   (Term.app `Int.exists_greatest_of_bdd [`hb `he])))
                 []
                 (Term.anonymousCtor
                  "⟨"
                  [`n
                   ","
                   `hn₁
                   ","
                   (Term.app
                    `lt_of_not_ge
                    [(Term.fun
                      "fun"
                      (Term.basicFun
                       [`hge]
                       []
                       "=>"
                       (Term.app
                        `not_le_of_gt
                        [(Term.app `Int.lt_succ [(Term.hole "_")])
                         (Term.app `hn₂ [(Term.hole "_") `hge])])))])]
                  "⟩"))))))))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.«tactic_<;>_»
       (Mathlib.Tactic.tacticClassical_ (Tactic.skip "skip"))
       "<;>"
       (Tactic.exact
        "exact"
        (Term.let
         "let"
         (Term.letDecl
          (Term.letPatDecl
           (Term.anonymousCtor "⟨" [`N "," `hN] "⟩")
           []
           []
           ":="
           (Term.app `pow_unbounded_of_one_lt [(«term_⁻¹_1» `x "⁻¹") `hy])))
         []
         (Term.have
          "have"
          (Term.haveDecl
           (Term.haveIdDecl
            [`he []]
            [(Term.typeSpec
              ":"
              («term∃_,_»
               "∃"
               (Lean.explicitBinders
                (Lean.unbracketedExplicitBinders [(Lean.binderIdent `m)] [":" (termℤ "ℤ")]))
               ","
               («term_≤_» («term_^_» `y "^" `m) "≤" `x)))]
            ":="
            (Term.anonymousCtor
             "⟨"
             [(«term-_» "-" `N)
              ","
              (Term.app
               `le_of_lt
               [(Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(Tactic.rwSeq
                     "rw"
                     []
                     (Tactic.rwRuleSeq
                      "["
                      [(Tactic.rwRule [] (Term.app `zpow_neg [`y (coeNotation "↑" `N)]))
                       ","
                       (Tactic.rwRule [] `zpow_coe_nat)]
                      "]")
                     [])
                    []
                    (Tactic.exact
                     "exact"
                     (Term.app
                      (Term.proj
                       (Term.app
                        `inv_lt
                        [`hx
                         (Term.app
                          `lt_trans
                          [(Term.app (Term.proj `inv_pos "." (fieldIdx "2")) [`hx]) `hN])])
                       "."
                       (fieldIdx "1"))
                      [`hN]))])))])]
             "⟩")))
          []
          (Term.let
           "let"
           (Term.letDecl
            (Term.letPatDecl
             (Term.anonymousCtor "⟨" [`M "," `hM] "⟩")
             []
             []
             ":="
             (Term.app `pow_unbounded_of_one_lt [`x `hy])))
           []
           (Term.have
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`hb []]
              [(Term.typeSpec
                ":"
                («term∃_,_»
                 "∃"
                 (Lean.explicitBinders
                  (Lean.unbracketedExplicitBinders [(Lean.binderIdent `b)] [":" (termℤ "ℤ")]))
                 ","
                 (Term.forall
                  "∀"
                  [`m]
                  []
                  ","
                  (Term.arrow
                   («term_≤_» («term_^_» `y "^" `m) "≤" `x)
                   "→"
                   («term_≤_» `m "≤" `b)))))]
              ":="
              (Term.anonymousCtor
               "⟨"
               [`M
                ","
                (Term.fun
                 "fun"
                 (Term.basicFun
                  [`m `hm]
                  []
                  "=>"
                  (Term.app
                   `le_of_not_lt
                   [(Term.fun
                     "fun"
                     (Term.basicFun
                      [`hlt]
                      []
                      "=>"
                      (Term.app
                       `not_lt_of_ge
                       [(Term.app `zpow_le_of_le [`hy.le (Term.proj `hlt "." `le)])
                        (Term.app
                         `lt_of_le_of_lt
                         [`hm
                          (Term.byTactic
                           "by"
                           (Tactic.tacticSeq
                            (Tactic.tacticSeq1Indented
                             [(Std.Tactic.tacticRwa__
                               "rwa"
                               (Tactic.rwRuleSeq
                                "["
                                [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `zpow_coe_nat)]
                                "]")
                               [(Tactic.location
                                 "at"
                                 (Tactic.locationHyp [`hM] []))])])))])])))])))]
               "⟩")))
            []
            (Term.let
             "let"
             (Term.letDecl
              (Term.letPatDecl
               (Term.anonymousCtor "⟨" [`n "," `hn₁ "," `hn₂] "⟩")
               []
               []
               ":="
               (Term.app `Int.exists_greatest_of_bdd [`hb `he])))
             []
             (Term.anonymousCtor
              "⟨"
              [`n
               ","
               `hn₁
               ","
               (Term.app
                `lt_of_not_ge
                [(Term.fun
                  "fun"
                  (Term.basicFun
                   [`hge]
                   []
                   "=>"
                   (Term.app
                    `not_le_of_gt
                    [(Term.app `Int.lt_succ [(Term.hole "_")])
                     (Term.app `hn₂ [(Term.hole "_") `hge])])))])]
              "⟩"))))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.let
        "let"
        (Term.letDecl
         (Term.letPatDecl
          (Term.anonymousCtor "⟨" [`N "," `hN] "⟩")
          []
          []
          ":="
          (Term.app `pow_unbounded_of_one_lt [(«term_⁻¹_1» `x "⁻¹") `hy])))
        []
        (Term.have
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`he []]
           [(Term.typeSpec
             ":"
             («term∃_,_»
              "∃"
              (Lean.explicitBinders
               (Lean.unbracketedExplicitBinders [(Lean.binderIdent `m)] [":" (termℤ "ℤ")]))
              ","
              («term_≤_» («term_^_» `y "^" `m) "≤" `x)))]
           ":="
           (Term.anonymousCtor
            "⟨"
            [(«term-_» "-" `N)
             ","
             (Term.app
              `le_of_lt
              [(Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(Tactic.rwSeq
                    "rw"
                    []
                    (Tactic.rwRuleSeq
                     "["
                     [(Tactic.rwRule [] (Term.app `zpow_neg [`y (coeNotation "↑" `N)]))
                      ","
                      (Tactic.rwRule [] `zpow_coe_nat)]
                     "]")
                    [])
                   []
                   (Tactic.exact
                    "exact"
                    (Term.app
                     (Term.proj
                      (Term.app
                       `inv_lt
                       [`hx
                        (Term.app
                         `lt_trans
                         [(Term.app (Term.proj `inv_pos "." (fieldIdx "2")) [`hx]) `hN])])
                      "."
                      (fieldIdx "1"))
                     [`hN]))])))])]
            "⟩")))
         []
         (Term.let
          "let"
          (Term.letDecl
           (Term.letPatDecl
            (Term.anonymousCtor "⟨" [`M "," `hM] "⟩")
            []
            []
            ":="
            (Term.app `pow_unbounded_of_one_lt [`x `hy])))
          []
          (Term.have
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`hb []]
             [(Term.typeSpec
               ":"
               («term∃_,_»
                "∃"
                (Lean.explicitBinders
                 (Lean.unbracketedExplicitBinders [(Lean.binderIdent `b)] [":" (termℤ "ℤ")]))
                ","
                (Term.forall
                 "∀"
                 [`m]
                 []
                 ","
                 (Term.arrow («term_≤_» («term_^_» `y "^" `m) "≤" `x) "→" («term_≤_» `m "≤" `b)))))]
             ":="
             (Term.anonymousCtor
              "⟨"
              [`M
               ","
               (Term.fun
                "fun"
                (Term.basicFun
                 [`m `hm]
                 []
                 "=>"
                 (Term.app
                  `le_of_not_lt
                  [(Term.fun
                    "fun"
                    (Term.basicFun
                     [`hlt]
                     []
                     "=>"
                     (Term.app
                      `not_lt_of_ge
                      [(Term.app `zpow_le_of_le [`hy.le (Term.proj `hlt "." `le)])
                       (Term.app
                        `lt_of_le_of_lt
                        [`hm
                         (Term.byTactic
                          "by"
                          (Tactic.tacticSeq
                           (Tactic.tacticSeq1Indented
                            [(Std.Tactic.tacticRwa__
                              "rwa"
                              (Tactic.rwRuleSeq
                               "["
                               [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `zpow_coe_nat)]
                               "]")
                              [(Tactic.location "at" (Tactic.locationHyp [`hM] []))])])))])])))])))]
              "⟩")))
           []
           (Term.let
            "let"
            (Term.letDecl
             (Term.letPatDecl
              (Term.anonymousCtor "⟨" [`n "," `hn₁ "," `hn₂] "⟩")
              []
              []
              ":="
              (Term.app `Int.exists_greatest_of_bdd [`hb `he])))
            []
            (Term.anonymousCtor
             "⟨"
             [`n
              ","
              `hn₁
              ","
              (Term.app
               `lt_of_not_ge
               [(Term.fun
                 "fun"
                 (Term.basicFun
                  [`hge]
                  []
                  "=>"
                  (Term.app
                   `not_le_of_gt
                   [(Term.app `Int.lt_succ [(Term.hole "_")])
                    (Term.app `hn₂ [(Term.hole "_") `hge])])))])]
             "⟩")))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.let
       "let"
       (Term.letDecl
        (Term.letPatDecl
         (Term.anonymousCtor "⟨" [`N "," `hN] "⟩")
         []
         []
         ":="
         (Term.app `pow_unbounded_of_one_lt [(«term_⁻¹_1» `x "⁻¹") `hy])))
       []
       (Term.have
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`he []]
          [(Term.typeSpec
            ":"
            («term∃_,_»
             "∃"
             (Lean.explicitBinders
              (Lean.unbracketedExplicitBinders [(Lean.binderIdent `m)] [":" (termℤ "ℤ")]))
             ","
             («term_≤_» («term_^_» `y "^" `m) "≤" `x)))]
          ":="
          (Term.anonymousCtor
           "⟨"
           [(«term-_» "-" `N)
            ","
            (Term.app
             `le_of_lt
             [(Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Tactic.rwSeq
                   "rw"
                   []
                   (Tactic.rwRuleSeq
                    "["
                    [(Tactic.rwRule [] (Term.app `zpow_neg [`y (coeNotation "↑" `N)]))
                     ","
                     (Tactic.rwRule [] `zpow_coe_nat)]
                    "]")
                   [])
                  []
                  (Tactic.exact
                   "exact"
                   (Term.app
                    (Term.proj
                     (Term.app
                      `inv_lt
                      [`hx
                       (Term.app
                        `lt_trans
                        [(Term.app (Term.proj `inv_pos "." (fieldIdx "2")) [`hx]) `hN])])
                     "."
                     (fieldIdx "1"))
                    [`hN]))])))])]
           "⟩")))
        []
        (Term.let
         "let"
         (Term.letDecl
          (Term.letPatDecl
           (Term.anonymousCtor "⟨" [`M "," `hM] "⟩")
           []
           []
           ":="
           (Term.app `pow_unbounded_of_one_lt [`x `hy])))
         []
         (Term.have
          "have"
          (Term.haveDecl
           (Term.haveIdDecl
            [`hb []]
            [(Term.typeSpec
              ":"
              («term∃_,_»
               "∃"
               (Lean.explicitBinders
                (Lean.unbracketedExplicitBinders [(Lean.binderIdent `b)] [":" (termℤ "ℤ")]))
               ","
               (Term.forall
                "∀"
                [`m]
                []
                ","
                (Term.arrow («term_≤_» («term_^_» `y "^" `m) "≤" `x) "→" («term_≤_» `m "≤" `b)))))]
            ":="
            (Term.anonymousCtor
             "⟨"
             [`M
              ","
              (Term.fun
               "fun"
               (Term.basicFun
                [`m `hm]
                []
                "=>"
                (Term.app
                 `le_of_not_lt
                 [(Term.fun
                   "fun"
                   (Term.basicFun
                    [`hlt]
                    []
                    "=>"
                    (Term.app
                     `not_lt_of_ge
                     [(Term.app `zpow_le_of_le [`hy.le (Term.proj `hlt "." `le)])
                      (Term.app
                       `lt_of_le_of_lt
                       [`hm
                        (Term.byTactic
                         "by"
                         (Tactic.tacticSeq
                          (Tactic.tacticSeq1Indented
                           [(Std.Tactic.tacticRwa__
                             "rwa"
                             (Tactic.rwRuleSeq
                              "["
                              [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `zpow_coe_nat)]
                              "]")
                             [(Tactic.location "at" (Tactic.locationHyp [`hM] []))])])))])])))])))]
             "⟩")))
          []
          (Term.let
           "let"
           (Term.letDecl
            (Term.letPatDecl
             (Term.anonymousCtor "⟨" [`n "," `hn₁ "," `hn₂] "⟩")
             []
             []
             ":="
             (Term.app `Int.exists_greatest_of_bdd [`hb `he])))
           []
           (Term.anonymousCtor
            "⟨"
            [`n
             ","
             `hn₁
             ","
             (Term.app
              `lt_of_not_ge
              [(Term.fun
                "fun"
                (Term.basicFun
                 [`hge]
                 []
                 "=>"
                 (Term.app
                  `not_le_of_gt
                  [(Term.app `Int.lt_succ [(Term.hole "_")])
                   (Term.app `hn₂ [(Term.hole "_") `hge])])))])]
            "⟩"))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.have
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`he []]
         [(Term.typeSpec
           ":"
           («term∃_,_»
            "∃"
            (Lean.explicitBinders
             (Lean.unbracketedExplicitBinders [(Lean.binderIdent `m)] [":" (termℤ "ℤ")]))
            ","
            («term_≤_» («term_^_» `y "^" `m) "≤" `x)))]
         ":="
         (Term.anonymousCtor
          "⟨"
          [(«term-_» "-" `N)
           ","
           (Term.app
            `le_of_lt
            [(Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule [] (Term.app `zpow_neg [`y (coeNotation "↑" `N)]))
                    ","
                    (Tactic.rwRule [] `zpow_coe_nat)]
                   "]")
                  [])
                 []
                 (Tactic.exact
                  "exact"
                  (Term.app
                   (Term.proj
                    (Term.app
                     `inv_lt
                     [`hx
                      (Term.app
                       `lt_trans
                       [(Term.app (Term.proj `inv_pos "." (fieldIdx "2")) [`hx]) `hN])])
                    "."
                    (fieldIdx "1"))
                   [`hN]))])))])]
          "⟩")))
       []
       (Term.let
        "let"
        (Term.letDecl
         (Term.letPatDecl
          (Term.anonymousCtor "⟨" [`M "," `hM] "⟩")
          []
          []
          ":="
          (Term.app `pow_unbounded_of_one_lt [`x `hy])))
        []
        (Term.have
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`hb []]
           [(Term.typeSpec
             ":"
             («term∃_,_»
              "∃"
              (Lean.explicitBinders
               (Lean.unbracketedExplicitBinders [(Lean.binderIdent `b)] [":" (termℤ "ℤ")]))
              ","
              (Term.forall
               "∀"
               [`m]
               []
               ","
               (Term.arrow («term_≤_» («term_^_» `y "^" `m) "≤" `x) "→" («term_≤_» `m "≤" `b)))))]
           ":="
           (Term.anonymousCtor
            "⟨"
            [`M
             ","
             (Term.fun
              "fun"
              (Term.basicFun
               [`m `hm]
               []
               "=>"
               (Term.app
                `le_of_not_lt
                [(Term.fun
                  "fun"
                  (Term.basicFun
                   [`hlt]
                   []
                   "=>"
                   (Term.app
                    `not_lt_of_ge
                    [(Term.app `zpow_le_of_le [`hy.le (Term.proj `hlt "." `le)])
                     (Term.app
                      `lt_of_le_of_lt
                      [`hm
                       (Term.byTactic
                        "by"
                        (Tactic.tacticSeq
                         (Tactic.tacticSeq1Indented
                          [(Std.Tactic.tacticRwa__
                            "rwa"
                            (Tactic.rwRuleSeq
                             "["
                             [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `zpow_coe_nat)]
                             "]")
                            [(Tactic.location "at" (Tactic.locationHyp [`hM] []))])])))])])))])))]
            "⟩")))
         []
         (Term.let
          "let"
          (Term.letDecl
           (Term.letPatDecl
            (Term.anonymousCtor "⟨" [`n "," `hn₁ "," `hn₂] "⟩")
            []
            []
            ":="
            (Term.app `Int.exists_greatest_of_bdd [`hb `he])))
          []
          (Term.anonymousCtor
           "⟨"
           [`n
            ","
            `hn₁
            ","
            (Term.app
             `lt_of_not_ge
             [(Term.fun
               "fun"
               (Term.basicFun
                [`hge]
                []
                "=>"
                (Term.app
                 `not_le_of_gt
                 [(Term.app `Int.lt_succ [(Term.hole "_")])
                  (Term.app `hn₂ [(Term.hole "_") `hge])])))])]
           "⟩")))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.let
       "let"
       (Term.letDecl
        (Term.letPatDecl
         (Term.anonymousCtor "⟨" [`M "," `hM] "⟩")
         []
         []
         ":="
         (Term.app `pow_unbounded_of_one_lt [`x `hy])))
       []
       (Term.have
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`hb []]
          [(Term.typeSpec
            ":"
            («term∃_,_»
             "∃"
             (Lean.explicitBinders
              (Lean.unbracketedExplicitBinders [(Lean.binderIdent `b)] [":" (termℤ "ℤ")]))
             ","
             (Term.forall
              "∀"
              [`m]
              []
              ","
              (Term.arrow («term_≤_» («term_^_» `y "^" `m) "≤" `x) "→" («term_≤_» `m "≤" `b)))))]
          ":="
          (Term.anonymousCtor
           "⟨"
           [`M
            ","
            (Term.fun
             "fun"
             (Term.basicFun
              [`m `hm]
              []
              "=>"
              (Term.app
               `le_of_not_lt
               [(Term.fun
                 "fun"
                 (Term.basicFun
                  [`hlt]
                  []
                  "=>"
                  (Term.app
                   `not_lt_of_ge
                   [(Term.app `zpow_le_of_le [`hy.le (Term.proj `hlt "." `le)])
                    (Term.app
                     `lt_of_le_of_lt
                     [`hm
                      (Term.byTactic
                       "by"
                       (Tactic.tacticSeq
                        (Tactic.tacticSeq1Indented
                         [(Std.Tactic.tacticRwa__
                           "rwa"
                           (Tactic.rwRuleSeq
                            "["
                            [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `zpow_coe_nat)]
                            "]")
                           [(Tactic.location "at" (Tactic.locationHyp [`hM] []))])])))])])))])))]
           "⟩")))
        []
        (Term.let
         "let"
         (Term.letDecl
          (Term.letPatDecl
           (Term.anonymousCtor "⟨" [`n "," `hn₁ "," `hn₂] "⟩")
           []
           []
           ":="
           (Term.app `Int.exists_greatest_of_bdd [`hb `he])))
         []
         (Term.anonymousCtor
          "⟨"
          [`n
           ","
           `hn₁
           ","
           (Term.app
            `lt_of_not_ge
            [(Term.fun
              "fun"
              (Term.basicFun
               [`hge]
               []
               "=>"
               (Term.app
                `not_le_of_gt
                [(Term.app `Int.lt_succ [(Term.hole "_")])
                 (Term.app `hn₂ [(Term.hole "_") `hge])])))])]
          "⟩"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.have
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`hb []]
         [(Term.typeSpec
           ":"
           («term∃_,_»
            "∃"
            (Lean.explicitBinders
             (Lean.unbracketedExplicitBinders [(Lean.binderIdent `b)] [":" (termℤ "ℤ")]))
            ","
            (Term.forall
             "∀"
             [`m]
             []
             ","
             (Term.arrow («term_≤_» («term_^_» `y "^" `m) "≤" `x) "→" («term_≤_» `m "≤" `b)))))]
         ":="
         (Term.anonymousCtor
          "⟨"
          [`M
           ","
           (Term.fun
            "fun"
            (Term.basicFun
             [`m `hm]
             []
             "=>"
             (Term.app
              `le_of_not_lt
              [(Term.fun
                "fun"
                (Term.basicFun
                 [`hlt]
                 []
                 "=>"
                 (Term.app
                  `not_lt_of_ge
                  [(Term.app `zpow_le_of_le [`hy.le (Term.proj `hlt "." `le)])
                   (Term.app
                    `lt_of_le_of_lt
                    [`hm
                     (Term.byTactic
                      "by"
                      (Tactic.tacticSeq
                       (Tactic.tacticSeq1Indented
                        [(Std.Tactic.tacticRwa__
                          "rwa"
                          (Tactic.rwRuleSeq
                           "["
                           [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `zpow_coe_nat)]
                           "]")
                          [(Tactic.location "at" (Tactic.locationHyp [`hM] []))])])))])])))])))]
          "⟩")))
       []
       (Term.let
        "let"
        (Term.letDecl
         (Term.letPatDecl
          (Term.anonymousCtor "⟨" [`n "," `hn₁ "," `hn₂] "⟩")
          []
          []
          ":="
          (Term.app `Int.exists_greatest_of_bdd [`hb `he])))
        []
        (Term.anonymousCtor
         "⟨"
         [`n
          ","
          `hn₁
          ","
          (Term.app
           `lt_of_not_ge
           [(Term.fun
             "fun"
             (Term.basicFun
              [`hge]
              []
              "=>"
              (Term.app
               `not_le_of_gt
               [(Term.app `Int.lt_succ [(Term.hole "_")])
                (Term.app `hn₂ [(Term.hole "_") `hge])])))])]
         "⟩")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.let
       "let"
       (Term.letDecl
        (Term.letPatDecl
         (Term.anonymousCtor "⟨" [`n "," `hn₁ "," `hn₂] "⟩")
         []
         []
         ":="
         (Term.app `Int.exists_greatest_of_bdd [`hb `he])))
       []
       (Term.anonymousCtor
        "⟨"
        [`n
         ","
         `hn₁
         ","
         (Term.app
          `lt_of_not_ge
          [(Term.fun
            "fun"
            (Term.basicFun
             [`hge]
             []
             "=>"
             (Term.app
              `not_le_of_gt
              [(Term.app `Int.lt_succ [(Term.hole "_")])
               (Term.app `hn₂ [(Term.hole "_") `hge])])))])]
        "⟩"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [`n
        ","
        `hn₁
        ","
        (Term.app
         `lt_of_not_ge
         [(Term.fun
           "fun"
           (Term.basicFun
            [`hge]
            []
            "=>"
            (Term.app
             `not_le_of_gt
             [(Term.app `Int.lt_succ [(Term.hole "_")])
              (Term.app `hn₂ [(Term.hole "_") `hge])])))])]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `lt_of_not_ge
       [(Term.fun
         "fun"
         (Term.basicFun
          [`hge]
          []
          "=>"
          (Term.app
           `not_le_of_gt
           [(Term.app `Int.lt_succ [(Term.hole "_")]) (Term.app `hn₂ [(Term.hole "_") `hge])])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`hge]
        []
        "=>"
        (Term.app
         `not_le_of_gt
         [(Term.app `Int.lt_succ [(Term.hole "_")]) (Term.app `hn₂ [(Term.hole "_") `hge])])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `not_le_of_gt
       [(Term.app `Int.lt_succ [(Term.hole "_")]) (Term.app `hn₂ [(Term.hole "_") `hge])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `hn₂ [(Term.hole "_") `hge])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hge
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `hn₂
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `hn₂ [(Term.hole "_") `hge])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `Int.lt_succ [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Int.lt_succ
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `Int.lt_succ [(Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `not_le_of_gt
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hge
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `lt_of_not_ge
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hn₁
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letPatDecl', expected 'Lean.Parser.Term.letIdDecl'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Int.exists_greatest_of_bdd [`hb `he])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `he
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hb
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Int.exists_greatest_of_bdd
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [`n "," `hn₁ "," `hn₂] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hn₂
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hn₁
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [`M
        ","
        (Term.fun
         "fun"
         (Term.basicFun
          [`m `hm]
          []
          "=>"
          (Term.app
           `le_of_not_lt
           [(Term.fun
             "fun"
             (Term.basicFun
              [`hlt]
              []
              "=>"
              (Term.app
               `not_lt_of_ge
               [(Term.app `zpow_le_of_le [`hy.le (Term.proj `hlt "." `le)])
                (Term.app
                 `lt_of_le_of_lt
                 [`hm
                  (Term.byTactic
                   "by"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented
                     [(Std.Tactic.tacticRwa__
                       "rwa"
                       (Tactic.rwRuleSeq
                        "["
                        [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `zpow_coe_nat)]
                        "]")
                       [(Tactic.location "at" (Tactic.locationHyp [`hM] []))])])))])])))])))]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`m `hm]
        []
        "=>"
        (Term.app
         `le_of_not_lt
         [(Term.fun
           "fun"
           (Term.basicFun
            [`hlt]
            []
            "=>"
            (Term.app
             `not_lt_of_ge
             [(Term.app `zpow_le_of_le [`hy.le (Term.proj `hlt "." `le)])
              (Term.app
               `lt_of_le_of_lt
               [`hm
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(Std.Tactic.tacticRwa__
                     "rwa"
                     (Tactic.rwRuleSeq
                      "["
                      [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `zpow_coe_nat)]
                      "]")
                     [(Tactic.location "at" (Tactic.locationHyp [`hM] []))])])))])])))])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `le_of_not_lt
       [(Term.fun
         "fun"
         (Term.basicFun
          [`hlt]
          []
          "=>"
          (Term.app
           `not_lt_of_ge
           [(Term.app `zpow_le_of_le [`hy.le (Term.proj `hlt "." `le)])
            (Term.app
             `lt_of_le_of_lt
             [`hm
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Std.Tactic.tacticRwa__
                   "rwa"
                   (Tactic.rwRuleSeq
                    "["
                    [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `zpow_coe_nat)]
                    "]")
                   [(Tactic.location "at" (Tactic.locationHyp [`hM] []))])])))])])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`hlt]
        []
        "=>"
        (Term.app
         `not_lt_of_ge
         [(Term.app `zpow_le_of_le [`hy.le (Term.proj `hlt "." `le)])
          (Term.app
           `lt_of_le_of_lt
           [`hm
            (Term.byTactic
             "by"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(Std.Tactic.tacticRwa__
                 "rwa"
                 (Tactic.rwRuleSeq
                  "["
                  [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `zpow_coe_nat)]
                  "]")
                 [(Tactic.location "at" (Tactic.locationHyp [`hM] []))])])))])])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `not_lt_of_ge
       [(Term.app `zpow_le_of_le [`hy.le (Term.proj `hlt "." `le)])
        (Term.app
         `lt_of_le_of_lt
         [`hm
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(Std.Tactic.tacticRwa__
               "rwa"
               (Tactic.rwRuleSeq
                "["
                [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `zpow_coe_nat)]
                "]")
               [(Tactic.location "at" (Tactic.locationHyp [`hM] []))])])))])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `lt_of_le_of_lt
       [`hm
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Std.Tactic.tacticRwa__
             "rwa"
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `zpow_coe_nat)]
              "]")
             [(Tactic.location "at" (Tactic.locationHyp [`hM] []))])])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Std.Tactic.tacticRwa__
           "rwa"
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `zpow_coe_nat)]
            "]")
           [(Tactic.location "at" (Tactic.locationHyp [`hM] []))])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.tacticRwa__
       "rwa"
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `zpow_coe_nat)] "]")
       [(Tactic.location "at" (Tactic.locationHyp [`hM] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hM
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `zpow_coe_nat
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0,
     tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(Std.Tactic.tacticRwa__
          "rwa"
          (Tactic.rwRuleSeq
           "["
           [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `zpow_coe_nat)]
           "]")
          [(Tactic.location "at" (Tactic.locationHyp [`hM] []))])])))
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hm
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `lt_of_le_of_lt
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `lt_of_le_of_lt
      [`hm
       (Term.paren
        "("
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Std.Tactic.tacticRwa__
             "rwa"
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `zpow_coe_nat)]
              "]")
             [(Tactic.location "at" (Tactic.locationHyp [`hM] []))])])))
        ")")])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `zpow_le_of_le [`hy.le (Term.proj `hlt "." `le)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `hlt "." `le)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hlt
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hy.le
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `zpow_le_of_le
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `zpow_le_of_le [`hy.le (Term.proj `hlt "." `le)])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `not_lt_of_ge
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hlt
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `le_of_not_lt
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hm
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `m
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `M
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term∃_,_»
       "∃"
       (Lean.explicitBinders
        (Lean.unbracketedExplicitBinders [(Lean.binderIdent `b)] [":" (termℤ "ℤ")]))
       ","
       (Term.forall
        "∀"
        [`m]
        []
        ","
        (Term.arrow («term_≤_» («term_^_» `y "^" `m) "≤" `x) "→" («term_≤_» `m "≤" `b))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.forall
       "∀"
       [`m]
       []
       ","
       (Term.arrow («term_≤_» («term_^_» `y "^" `m) "≤" `x) "→" («term_≤_» `m "≤" `b)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.arrow («term_≤_» («term_^_» `y "^" `m) "≤" `x) "→" («term_≤_» `m "≤" `b))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≤_» `m "≤" `b)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `b
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `m
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 25 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
      («term_≤_» («term_^_» `y "^" `m) "≤" `x)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      («term_^_» `y "^" `m)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `m
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      `y
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 80, (some 80, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (some 25, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 25, (some 25, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'Lean.bracketedExplicitBinders'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (termℤ "ℤ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letPatDecl', expected 'Lean.Parser.Term.letIdDecl'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `pow_unbounded_of_one_lt [`x `hy])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hy
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `pow_unbounded_of_one_lt
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [`M "," `hM] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hM
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `M
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(«term-_» "-" `N)
        ","
        (Term.app
         `le_of_lt
         [(Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(Tactic.rwSeq
               "rw"
               []
               (Tactic.rwRuleSeq
                "["
                [(Tactic.rwRule [] (Term.app `zpow_neg [`y (coeNotation "↑" `N)]))
                 ","
                 (Tactic.rwRule [] `zpow_coe_nat)]
                "]")
               [])
              []
              (Tactic.exact
               "exact"
               (Term.app
                (Term.proj
                 (Term.app
                  `inv_lt
                  [`hx
                   (Term.app
                    `lt_trans
                    [(Term.app (Term.proj `inv_pos "." (fieldIdx "2")) [`hx]) `hN])])
                 "."
                 (fieldIdx "1"))
                [`hN]))])))])]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `le_of_lt
       [(Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] (Term.app `zpow_neg [`y (coeNotation "↑" `N)]))
               ","
               (Tactic.rwRule [] `zpow_coe_nat)]
              "]")
             [])
            []
            (Tactic.exact
             "exact"
             (Term.app
              (Term.proj
               (Term.app
                `inv_lt
                [`hx
                 (Term.app
                  `lt_trans
                  [(Term.app (Term.proj `inv_pos "." (fieldIdx "2")) [`hx]) `hN])])
               "."
               (fieldIdx "1"))
              [`hN]))])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.ellipsis'
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
            [(Tactic.rwRule [] (Term.app `zpow_neg [`y (coeNotation "↑" `N)]))
             ","
             (Tactic.rwRule [] `zpow_coe_nat)]
            "]")
           [])
          []
          (Tactic.exact
           "exact"
           (Term.app
            (Term.proj
             (Term.app
              `inv_lt
              [`hx
               (Term.app `lt_trans [(Term.app (Term.proj `inv_pos "." (fieldIdx "2")) [`hx]) `hN])])
             "."
             (fieldIdx "1"))
            [`hN]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.app
        (Term.proj
         (Term.app
          `inv_lt
          [`hx (Term.app `lt_trans [(Term.app (Term.proj `inv_pos "." (fieldIdx "2")) [`hx]) `hN])])
         "."
         (fieldIdx "1"))
        [`hN]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (Term.app
         `inv_lt
         [`hx (Term.app `lt_trans [(Term.app (Term.proj `inv_pos "." (fieldIdx "2")) [`hx]) `hN])])
        "."
        (fieldIdx "1"))
       [`hN])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hN
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (Term.app
        `inv_lt
        [`hx (Term.app `lt_trans [(Term.app (Term.proj `inv_pos "." (fieldIdx "2")) [`hx]) `hN])])
       "."
       (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       `inv_lt
       [`hx (Term.app `lt_trans [(Term.app (Term.proj `inv_pos "." (fieldIdx "2")) [`hx]) `hN])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `lt_trans [(Term.app (Term.proj `inv_pos "." (fieldIdx "2")) [`hx]) `hN])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hN
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app (Term.proj `inv_pos "." (fieldIdx "2")) [`hx])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hx
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `inv_pos "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `inv_pos
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.proj `inv_pos "." (fieldIdx "2")) [`hx])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `lt_trans
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `lt_trans
      [(Term.paren "(" (Term.app (Term.proj `inv_pos "." (fieldIdx "2")) [`hx]) ")") `hN])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hx
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `inv_lt
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `inv_lt
      [`hx
       (Term.paren
        "("
        (Term.app
         `lt_trans
         [(Term.paren "(" (Term.app (Term.proj `inv_pos "." (fieldIdx "2")) [`hx]) ")") `hN])
        ")")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] (Term.app `zpow_neg [`y (coeNotation "↑" `N)]))
         ","
         (Tactic.rwRule [] `zpow_coe_nat)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `zpow_coe_nat
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `zpow_neg [`y (coeNotation "↑" `N)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'coeNotation', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'coeNotation', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (coeNotation "↑" `N)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `N
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 1024,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `zpow_neg
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0,
     tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(Tactic.rwSeq
          "rw"
          []
          (Tactic.rwRuleSeq
           "["
           [(Tactic.rwRule [] (Term.app `zpow_neg [`y (coeNotation "↑" `N)]))
            ","
            (Tactic.rwRule [] `zpow_coe_nat)]
           "]")
          [])
         []
         (Tactic.exact
          "exact"
          (Term.app
           (Term.proj
            (Term.paren
             "("
             (Term.app
              `inv_lt
              [`hx
               (Term.paren
                "("
                (Term.app
                 `lt_trans
                 [(Term.paren "(" (Term.app (Term.proj `inv_pos "." (fieldIdx "2")) [`hx]) ")")
                  `hN])
                ")")])
             ")")
            "."
            (fieldIdx "1"))
           [`hN]))])))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `le_of_lt
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term-_» "-" `N)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `N
[PrettyPrinter.parenthesize] ...precedences are 75 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 75, (some 75, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term∃_,_»
       "∃"
       (Lean.explicitBinders
        (Lean.unbracketedExplicitBinders [(Lean.binderIdent `m)] [":" (termℤ "ℤ")]))
       ","
       («term_≤_» («term_^_» `y "^" `m) "≤" `x))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≤_» («term_^_» `y "^" `m) "≤" `x)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      («term_^_» `y "^" `m)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `m
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      `y
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 80, (some 80, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'Lean.bracketedExplicitBinders'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (termℤ "ℤ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letPatDecl', expected 'Lean.Parser.Term.letIdDecl'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `pow_unbounded_of_one_lt [(«term_⁻¹_1» `x "⁻¹") `hy])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hy
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_⁻¹_1»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_⁻¹_1»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      («term_⁻¹_1» `x "⁻¹")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `pow_unbounded_of_one_lt
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [`N "," `hN] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hN
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `N
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 2 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
      (Mathlib.Tactic.tacticClassical_ (Tactic.skip "skip"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.skip', expected 'Lean.Parser.Tactic.tacticSeq'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    Every positive `x` is between two successive integer powers of
    another `y` greater than one. This is the same as `exists_mem_Ioc_zpow`,
    but with ≤ and < the other way around. -/
  theorem
    exists_mem_Ico_zpow
    ( hx : 0 < x ) ( hy : 1 < y ) : ∃ n : ℤ , x ∈ ico y ^ n y ^ n + 1
    :=
      by
        skip
          <;>
          exact
            let
              ⟨ N , hN ⟩ := pow_unbounded_of_one_lt x ⁻¹ hy
              have
                he
                  : ∃ m : ℤ , y ^ m ≤ x
                  :=
                  ⟨
                    - N
                      ,
                      le_of_lt
                        by
                          rw [ zpow_neg y ↑ N , zpow_coe_nat ]
                            exact inv_lt hx lt_trans inv_pos . 2 hx hN . 1 hN
                    ⟩
                let
                  ⟨ M , hM ⟩ := pow_unbounded_of_one_lt x hy
                  have
                    hb
                      : ∃ b : ℤ , ∀ m , y ^ m ≤ x → m ≤ b
                      :=
                      ⟨
                        M
                          ,
                          fun
                            m hm
                              =>
                              le_of_not_lt
                                fun
                                  hlt
                                    =>
                                    not_lt_of_ge
                                      zpow_le_of_le hy.le hlt . le
                                        lt_of_le_of_lt hm by rwa [ ← zpow_coe_nat ] at hM
                        ⟩
                    let
                      ⟨ n , hn₁ , hn₂ ⟩ := Int.exists_greatest_of_bdd hb he
                      ⟨ n , hn₁ , lt_of_not_ge fun hge => not_le_of_gt Int.lt_succ _ hn₂ _ hge ⟩
#align exists_mem_Ico_zpow exists_mem_Ico_zpow

/-- Every positive `x` is between two successive integer powers of
another `y` greater than one. This is the same as `exists_mem_Ico_zpow`,
but with ≤ and < the other way around. -/
theorem exists_mem_Ioc_zpow (hx : 0 < x) (hy : 1 < y) : ∃ n : ℤ, x ∈ ioc (y ^ n) (y ^ (n + 1)) :=
  let ⟨m, hle, hlt⟩ := exists_mem_Ico_zpow (inv_pos.2 hx) hy
  have hyp : 0 < y := lt_trans zero_lt_one hy
  ⟨-(m + 1), by rwa [zpow_neg, inv_lt (zpow_pos_of_pos hyp _) hx], by
    rwa [neg_add, neg_add_cancel_right, zpow_neg, le_inv hx (zpow_pos_of_pos hyp _)]⟩
#align exists_mem_Ioc_zpow exists_mem_Ioc_zpow

/-- For any `y < 1` and any positive `x`, there exists `n : ℕ` with `y ^ n < x`. -/
theorem exists_pow_lt_of_lt_one (hx : 0 < x) (hy : y < 1) : ∃ n : ℕ, y ^ n < x := by
  by_cases y_pos : y ≤ 0
  · use 1
    simp only [pow_one]
    linarith
    
  rw [not_le] at y_pos
  rcases pow_unbounded_of_one_lt x⁻¹ (one_lt_inv y_pos hy) with ⟨q, hq⟩
  exact ⟨q, by rwa [inv_pow, inv_lt_inv hx (pow_pos y_pos _)] at hq⟩
#align exists_pow_lt_of_lt_one exists_pow_lt_of_lt_one

/-- Given `x` and `y` between `0` and `1`, `x` is between two successive powers of `y`.
This is the same as `exists_nat_pow_near`, but for elements between `0` and `1` -/
theorem exists_nat_pow_near_of_lt_one (xpos : 0 < x) (hx : x ≤ 1) (ypos : 0 < y) (hy : y < 1) :
    ∃ n : ℕ, y ^ (n + 1) < x ∧ x ≤ y ^ n := by
  rcases exists_nat_pow_near (one_le_inv_iff.2 ⟨xpos, hx⟩) (one_lt_inv_iff.2 ⟨ypos, hy⟩) with
    ⟨n, hn, h'n⟩
  refine' ⟨n, _, _⟩
  · rwa [inv_pow, inv_lt_inv xpos (pow_pos ypos _)] at h'n
    
  · rwa [inv_pow, inv_le_inv (pow_pos ypos _) xpos] at hn
    
#align exists_nat_pow_near_of_lt_one exists_nat_pow_near_of_lt_one

theorem exists_rat_gt (x : α) : ∃ q : ℚ, x < q :=
  let ⟨n, h⟩ := exists_nat_gt x
  ⟨n, by rwa [Rat.cast_coe_nat]⟩
#align exists_rat_gt exists_rat_gt

theorem exists_rat_lt (x : α) : ∃ q : ℚ, (q : α) < x :=
  let ⟨n, h⟩ := exists_int_lt x
  ⟨n, by rwa [Rat.cast_coe_int]⟩
#align exists_rat_lt exists_rat_lt

theorem exists_rat_btwn {x y : α} (h : x < y) : ∃ q : ℚ, x < q ∧ (q : α) < y := by
  cases' exists_nat_gt (y - x)⁻¹ with n nh
  cases' exists_floor (x * n) with z zh
  refine' ⟨(z + 1 : ℤ) / n, _⟩
  have n0' := (inv_pos.2 (sub_pos.2 h)).trans nh
  have n0 := Nat.cast_pos.1 n0'
  rw [Rat.cast_div_of_ne_zero, Rat.cast_coe_nat, Rat.cast_coe_int, div_lt_iff n0']
  refine' ⟨(lt_div_iff n0').2 <| (lt_iff_lt_of_le_iff_le (zh _)).1 (lt_add_one _), _⟩
  rw [Int.cast_add, Int.cast_one]
  refine' lt_of_le_of_lt (add_le_add_right ((zh _).1 le_rfl) _) _
  rwa [← lt_sub_iff_add_lt', ← sub_mul, ← div_lt_iff' (sub_pos.2 h), one_div]
  · rw [Rat.coe_int_denom, Nat.cast_one]
    exact one_ne_zero
    
  · intro H
    rw [Rat.coe_nat_num, Int.cast_ofNat, Nat.cast_eq_zero] at H
    subst H
    cases n0
    
  · rw [Rat.coe_nat_denom, Nat.cast_one]
    exact one_ne_zero
    
#align exists_rat_btwn exists_rat_btwn

theorem le_of_forall_rat_lt_imp_le (h : ∀ q : ℚ, (q : α) < x → (q : α) ≤ y) : x ≤ y :=
  le_of_not_lt fun hyx =>
    let ⟨q, hy, hx⟩ := exists_rat_btwn hyx
    hy.not_le <| h _ hx
#align le_of_forall_rat_lt_imp_le le_of_forall_rat_lt_imp_le

theorem le_of_forall_lt_rat_imp_le (h : ∀ q : ℚ, y < q → x ≤ q) : x ≤ y :=
  le_of_not_lt fun hyx =>
    let ⟨q, hy, hx⟩ := exists_rat_btwn hyx
    hx.not_le <| h _ hy
#align le_of_forall_lt_rat_imp_le le_of_forall_lt_rat_imp_le

theorem eq_of_forall_rat_lt_iff_lt (h : ∀ q : ℚ, (q : α) < x ↔ (q : α) < y) : x = y :=
  (le_of_forall_rat_lt_imp_le fun q hq => ((h q).1 hq).le).antisymm <|
    le_of_forall_rat_lt_imp_le fun q hq => ((h q).2 hq).le
#align eq_of_forall_rat_lt_iff_lt eq_of_forall_rat_lt_iff_lt

theorem eq_of_forall_lt_rat_iff_lt (h : ∀ q : ℚ, x < q ↔ y < q) : x = y :=
  (le_of_forall_lt_rat_imp_le fun q hq => ((h q).2 hq).le).antisymm <|
    le_of_forall_lt_rat_imp_le fun q hq => ((h q).1 hq).le
#align eq_of_forall_lt_rat_iff_lt eq_of_forall_lt_rat_iff_lt

theorem exists_nat_one_div_lt {ε : α} (hε : 0 < ε) : ∃ n : ℕ, 1 / (n + 1 : α) < ε := by
  cases' exists_nat_gt (1 / ε) with n hn
  use n
  rw [div_lt_iff, ← div_lt_iff' hε]
  · apply hn.trans
    simp [zero_lt_one]
    
  · exact n.cast_add_one_pos
    
#align exists_nat_one_div_lt exists_nat_one_div_lt

theorem exists_pos_rat_lt {x : α} (x0 : 0 < x) : ∃ q : ℚ, 0 < q ∧ (q : α) < x := by
  simpa only [Rat.cast_pos] using exists_rat_btwn x0
#align exists_pos_rat_lt exists_pos_rat_lt

theorem exists_rat_near (x : α) (ε0 : 0 < ε) : ∃ q : ℚ, |x - q| < ε :=
  let ⟨q, h₁, h₂⟩ :=
    exists_rat_btwn <| ((sub_lt_self_iff x).2 ε0).trans ((lt_add_iff_pos_left x).2 ε0)
  ⟨q, abs_sub_lt_iff.2 ⟨sub_lt_comm.1 h₁, sub_lt_iff_lt_add.2 h₂⟩⟩
#align exists_rat_near exists_rat_near

end LinearOrderedField

section LinearOrderedField

variable [LinearOrderedField α]

theorem archimedean_iff_nat_lt : Archimedean α ↔ ∀ x : α, ∃ n : ℕ, x < n :=
  ⟨@exists_nat_gt α _, fun H =>
    ⟨fun x y y0 =>
      (H (x / y)).imp fun n h => le_of_lt <| by rwa [div_lt_iff y0, ← nsmul_eq_mul] at h⟩⟩
#align archimedean_iff_nat_lt archimedean_iff_nat_lt

theorem archimedean_iff_nat_le : Archimedean α ↔ ∀ x : α, ∃ n : ℕ, x ≤ n :=
  archimedean_iff_nat_lt.trans
    ⟨fun H x => (H x).imp fun _ => le_of_lt, fun H x =>
      let ⟨n, h⟩ := H x
      ⟨n + 1, lt_of_le_of_lt h (Nat.cast_lt.2 (lt_add_one _))⟩⟩
#align archimedean_iff_nat_le archimedean_iff_nat_le

theorem archimedean_iff_int_lt : Archimedean α ↔ ∀ x : α, ∃ n : ℤ, x < n :=
  ⟨@exists_int_gt α _, by
    rw [archimedean_iff_nat_lt]
    intro h x
    obtain ⟨n, h⟩ := h x
    refine' ⟨n.to_nat, h.trans_le _⟩
    exact_mod_cast Int.self_le_toNat _⟩
#align archimedean_iff_int_lt archimedean_iff_int_lt

theorem archimedean_iff_int_le : Archimedean α ↔ ∀ x : α, ∃ n : ℤ, x ≤ n :=
  archimedean_iff_int_lt.trans
    ⟨fun H x => (H x).imp fun _ => le_of_lt, fun H x =>
      let ⟨n, h⟩ := H x
      ⟨n + 1, lt_of_le_of_lt h (Int.cast_lt.2 (lt_add_one _))⟩⟩
#align archimedean_iff_int_le archimedean_iff_int_le

theorem archimedean_iff_rat_lt : Archimedean α ↔ ∀ x : α, ∃ q : ℚ, x < q :=
  ⟨@exists_rat_gt α _, fun H =>
    archimedean_iff_nat_lt.2 fun x =>
      let ⟨q, h⟩ := H x
      ⟨⌈q⌉₊,
        lt_of_lt_of_le h <| by
          simpa only [Rat.cast_coe_nat] using (@Rat.cast_le α _ _ _).2 (Nat.le_ceil _)⟩⟩
#align archimedean_iff_rat_lt archimedean_iff_rat_lt

theorem archimedean_iff_rat_le : Archimedean α ↔ ∀ x : α, ∃ q : ℚ, x ≤ q :=
  archimedean_iff_rat_lt.trans
    ⟨fun H x => (H x).imp fun _ => le_of_lt, fun H x =>
      let ⟨n, h⟩ := H x
      ⟨n + 1, lt_of_le_of_lt h (Rat.cast_lt.2 (lt_add_one _))⟩⟩
#align archimedean_iff_rat_le archimedean_iff_rat_le

end LinearOrderedField

instance : Archimedean ℕ :=
  ⟨fun n m m0 => ⟨n, by simpa only [mul_one, Nat.nsmul_eq_mul] using Nat.mul_le_mul_left n m0⟩⟩

instance : Archimedean ℤ :=
  ⟨fun n m m0 =>
    ⟨n.toNat,
      le_trans (Int.self_le_toNat _) <| by
        simpa only [nsmul_eq_mul, zero_add, mul_one] using
          mul_le_mul_of_nonneg_left (Int.add_one_le_iff.2 m0) (Int.ofNat_zero_le n.to_nat)⟩⟩

instance : Archimedean ℚ :=
  archimedean_iff_rat_le.2 fun q => ⟨q, by rw [Rat.cast_id]⟩

/-- A linear ordered archimedean ring is a floor ring. This is not an `instance` because in some
cases we have a computable `floor` function. -/
noncomputable def Archimedean.floorRing (α) [LinearOrderedRing α] [Archimedean α] : FloorRing α :=
  FloorRing.ofFloor α (fun a => Classical.choose (exists_floor a)) fun z a =>
    (Classical.choose_spec (exists_floor a) z).symm
#align archimedean.floor_ring Archimedean.floorRing

-- see Note [lower instance priority]
/-- A linear ordered field that is a floor ring is archimedean. -/
instance (priority := 100) FloorRing.archimedean (α) [LinearOrderedField α] [FloorRing α] :
    Archimedean α := by
  rw [archimedean_iff_int_le]
  exact fun x => ⟨⌈x⌉, Int.le_ceil x⟩
#align floor_ring.archimedean FloorRing.archimedean

