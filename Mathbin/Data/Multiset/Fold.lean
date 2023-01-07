/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

! This file was ported from Lean 3 source module data.multiset.fold
! leanprover-community/mathlib commit 6afc9b06856ad973f6a2619e3e8a0a8d537a58f2
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Multiset.Dedup
import Mathbin.Data.List.MinMax

/-!
# The fold operation for a commutative associative operation over a multiset.
-/


namespace Multiset

variable {α β : Type _}

/-! ### fold -/


section Fold

variable (op : α → α → α) [hc : IsCommutative α op] [ha : IsAssociative α op]

-- mathport name: op
local notation a " * " b => op a b

include hc ha

/-- `fold op b s` folds a commutative associative operation `op` over
  the multiset `s`. -/
def fold : α → Multiset α → α :=
  foldr op (left_comm _ hc.comm ha.assoc)
#align multiset.fold Multiset.fold

theorem fold_eq_foldr (b : α) (s : Multiset α) :
    fold op b s = foldr op (left_comm _ hc.comm ha.assoc) b s :=
  rfl
#align multiset.fold_eq_foldr Multiset.fold_eq_foldr

@[simp]
theorem coe_fold_r (b : α) (l : List α) : fold op b l = l.foldr op b :=
  rfl
#align multiset.coe_fold_r Multiset.coe_fold_r

theorem coe_fold_l (b : α) (l : List α) : fold op b l = l.foldl op b :=
  (coe_foldr_swap op _ b l).trans <| by simp [hc.comm]
#align multiset.coe_fold_l Multiset.coe_fold_l

theorem fold_eq_foldl (b : α) (s : Multiset α) :
    fold op b s = foldl op (right_comm _ hc.comm ha.assoc) b s :=
  (Quot.induction_on s) fun l => coe_fold_l _ _ _
#align multiset.fold_eq_foldl Multiset.fold_eq_foldl

@[simp]
theorem fold_zero (b : α) : (0 : Multiset α).fold op b = b :=
  rfl
#align multiset.fold_zero Multiset.fold_zero

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
      (Command.declId `fold_cons_left [])
      (Command.declSig
       []
       (Term.typeSpec
        ":"
        (Term.forall
         "∀"
         [(Term.explicitBinder "(" [`b `a] [":" `α] [] ")")
          (Term.explicitBinder "(" [`s] [":" (Term.app `Multiset [`α])] [] ")")]
         []
         ","
         («term_=_»
          (Term.app
           (Term.proj (Multiset.Data.Multiset.Basic.«term_::ₘ_» `a " ::ₘ " `s) "." `fold)
           [`op `b])
          "="
          (Multiset.Data.Multiset.Fold.op `a " * " (Term.app (Term.proj `s "." `fold) [`op `b]))))))
      (Command.declValSimple ":=" (Term.app `foldr_cons [(Term.hole "_") (Term.hole "_")]) [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `foldr_cons [(Term.hole "_") (Term.hole "_")])
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
      `foldr_cons
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.forall
       "∀"
       [(Term.explicitBinder "(" [`b `a] [":" `α] [] ")")
        (Term.explicitBinder "(" [`s] [":" (Term.app `Multiset [`α])] [] ")")]
       []
       ","
       («term_=_»
        (Term.app
         (Term.proj (Multiset.Data.Multiset.Basic.«term_::ₘ_» `a " ::ₘ " `s) "." `fold)
         [`op `b])
        "="
        (Multiset.Data.Multiset.Fold.op `a " * " (Term.app (Term.proj `s "." `fold) [`op `b]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Term.app
        (Term.proj (Multiset.Data.Multiset.Basic.«term_::ₘ_» `a " ::ₘ " `s) "." `fold)
        [`op `b])
       "="
       (Multiset.Data.Multiset.Fold.op `a " * " (Term.app (Term.proj `s "." `fold) [`op `b])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Multiset.Data.Multiset.Fold.op `a " * " (Term.app (Term.proj `s "." `fold) [`op `b]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Multiset.Data.Multiset.Fold.op', expected 'Multiset.Data.Multiset.Fold.op._@.Data.Multiset.Fold._hyg.7'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ simp ]
  theorem
    fold_cons_left
    : ∀ ( b a : α ) ( s : Multiset α ) , a ::ₘ s . fold op b = a * s . fold op b
    := foldr_cons _ _
#align multiset.fold_cons_left Multiset.fold_cons_left

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `fold_cons_right [])
      (Command.declSig
       [(Term.explicitBinder "(" [`b `a] [":" `α] [] ")")
        (Term.explicitBinder "(" [`s] [":" (Term.app `Multiset [`α])] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app
          (Term.proj (Multiset.Data.Multiset.Basic.«term_::ₘ_» `a " ::ₘ " `s) "." `fold)
          [`op `b])
         "="
         (Multiset.Data.Multiset.Fold.op (Term.app (Term.proj `s "." `fold) [`op `b]) " * " `a))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `hc.comm)] "]"] [])])))
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
         [(Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `hc.comm)] "]"] [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `hc.comm)] "]"] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hc.comm
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app
        (Term.proj (Multiset.Data.Multiset.Basic.«term_::ₘ_» `a " ::ₘ " `s) "." `fold)
        [`op `b])
       "="
       (Multiset.Data.Multiset.Fold.op (Term.app (Term.proj `s "." `fold) [`op `b]) " * " `a))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Multiset.Data.Multiset.Fold.op (Term.app (Term.proj `s "." `fold) [`op `b]) " * " `a)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Multiset.Data.Multiset.Fold.op', expected 'Multiset.Data.Multiset.Fold.op._@.Data.Multiset.Fold._hyg.7'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  fold_cons_right
  ( b a : α ) ( s : Multiset α ) : a ::ₘ s . fold op b = s . fold op b * a
  := by simp [ hc.comm ]
#align multiset.fold_cons_right Multiset.fold_cons_right

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `fold_cons'_right [])
      (Command.declSig
       [(Term.explicitBinder "(" [`b `a] [":" `α] [] ")")
        (Term.explicitBinder "(" [`s] [":" (Term.app `Multiset [`α])] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app
          (Term.proj (Multiset.Data.Multiset.Basic.«term_::ₘ_» `a " ::ₘ " `s) "." `fold)
          [`op `b])
         "="
         (Term.app (Term.proj `s "." `fold) [`op (Multiset.Data.Multiset.Fold.op `b " * " `a)]))))
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
             [(Tactic.rwRule [] `fold_eq_foldl)
              ","
              (Tactic.rwRule [] `foldl_cons)
              ","
              (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `fold_eq_foldl)]
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
            [(Tactic.rwRule [] `fold_eq_foldl)
             ","
             (Tactic.rwRule [] `foldl_cons)
             ","
             (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `fold_eq_foldl)]
            "]")
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `fold_eq_foldl)
         ","
         (Tactic.rwRule [] `foldl_cons)
         ","
         (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `fold_eq_foldl)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `fold_eq_foldl
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `foldl_cons
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `fold_eq_foldl
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app
        (Term.proj (Multiset.Data.Multiset.Basic.«term_::ₘ_» `a " ::ₘ " `s) "." `fold)
        [`op `b])
       "="
       (Term.app (Term.proj `s "." `fold) [`op (Multiset.Data.Multiset.Fold.op `b " * " `a)]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj `s "." `fold) [`op (Multiset.Data.Multiset.Fold.op `b " * " `a)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Multiset.Data.Multiset.Fold.op', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Multiset.Data.Multiset.Fold.op', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Multiset.Data.Multiset.Fold.op `b " * " `a)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Multiset.Data.Multiset.Fold.op', expected 'Multiset.Data.Multiset.Fold.op._@.Data.Multiset.Fold._hyg.7'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  fold_cons'_right
  ( b a : α ) ( s : Multiset α ) : a ::ₘ s . fold op b = s . fold op b * a
  := by rw [ fold_eq_foldl , foldl_cons , ← fold_eq_foldl ]
#align multiset.fold_cons'_right Multiset.fold_cons'_right

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `fold_cons'_left [])
      (Command.declSig
       [(Term.explicitBinder "(" [`b `a] [":" `α] [] ")")
        (Term.explicitBinder "(" [`s] [":" (Term.app `Multiset [`α])] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app
          (Term.proj (Multiset.Data.Multiset.Basic.«term_::ₘ_» `a " ::ₘ " `s) "." `fold)
          [`op `b])
         "="
         (Term.app (Term.proj `s "." `fold) [`op (Multiset.Data.Multiset.Fold.op `a " * " `b)]))))
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
             [(Tactic.rwRule [] `fold_cons'_right) "," (Tactic.rwRule [] `hc.comm)]
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
            [(Tactic.rwRule [] `fold_cons'_right) "," (Tactic.rwRule [] `hc.comm)]
            "]")
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `fold_cons'_right) "," (Tactic.rwRule [] `hc.comm)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hc.comm
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `fold_cons'_right
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app
        (Term.proj (Multiset.Data.Multiset.Basic.«term_::ₘ_» `a " ::ₘ " `s) "." `fold)
        [`op `b])
       "="
       (Term.app (Term.proj `s "." `fold) [`op (Multiset.Data.Multiset.Fold.op `a " * " `b)]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj `s "." `fold) [`op (Multiset.Data.Multiset.Fold.op `a " * " `b)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Multiset.Data.Multiset.Fold.op', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Multiset.Data.Multiset.Fold.op', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Multiset.Data.Multiset.Fold.op `a " * " `b)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Multiset.Data.Multiset.Fold.op', expected 'Multiset.Data.Multiset.Fold.op._@.Data.Multiset.Fold._hyg.7'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  fold_cons'_left
  ( b a : α ) ( s : Multiset α ) : a ::ₘ s . fold op b = s . fold op a * b
  := by rw [ fold_cons'_right , hc.comm ]
#align multiset.fold_cons'_left Multiset.fold_cons'_left

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `fold_add [])
      (Command.declSig
       [(Term.explicitBinder "(" [`b₁ `b₂] [":" `α] [] ")")
        (Term.explicitBinder "(" [`s₁ `s₂] [":" (Term.app `Multiset [`α])] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app
          (Term.proj («term_+_» `s₁ "+" `s₂) "." `fold)
          [`op (Multiset.Data.Multiset.Fold.op `b₁ " * " `b₂)])
         "="
         (Multiset.Data.Multiset.Fold.op
          (Term.app (Term.proj `s₁ "." `fold) [`op `b₁])
          " * "
          (Term.app (Term.proj `s₂ "." `fold) [`op `b₂])))))
      (Command.declValSimple
       ":="
       (Term.app
        `Multiset.induction_on
        [`s₂
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [] `add_zero)
                ","
                (Tactic.rwRule [] `fold_zero)
                ","
                (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `fold_cons'_right)
                ","
                (Tactic.rwRule
                 [(patternIgnore (token.«← » "←"))]
                 (Term.app `fold_cons_right [`op]))]
               "]")
              [])])))
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.«tactic_<;>_»
              (Tactic.simp
               "simp"
               [(Tactic.config
                 "("
                 "config"
                 ":="
                 (Term.structInst
                  "{"
                  []
                  [(Term.structInstField (Term.structInstLVal `contextual []) ":=" `true)]
                  (Term.optEllipsis [])
                  []
                  "}")
                 ")")]
               []
               []
               []
               [])
              "<;>"
              (Tactic.cc "cc"))])))])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Multiset.induction_on
       [`s₂
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] `add_zero)
               ","
               (Tactic.rwRule [] `fold_zero)
               ","
               (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `fold_cons'_right)
               ","
               (Tactic.rwRule [(patternIgnore (token.«← » "←"))] (Term.app `fold_cons_right [`op]))]
              "]")
             [])])))
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Tactic.«tactic_<;>_»
             (Tactic.simp
              "simp"
              [(Tactic.config
                "("
                "config"
                ":="
                (Term.structInst
                 "{"
                 []
                 [(Term.structInstField (Term.structInstLVal `contextual []) ":=" `true)]
                 (Term.optEllipsis [])
                 []
                 "}")
                ")")]
              []
              []
              []
              [])
             "<;>"
             (Tactic.cc "cc"))])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.«tactic_<;>_»
           (Tactic.simp
            "simp"
            [(Tactic.config
              "("
              "config"
              ":="
              (Term.structInst
               "{"
               []
               [(Term.structInstField (Term.structInstLVal `contextual []) ":=" `true)]
               (Term.optEllipsis [])
               []
               "}")
              ")")]
            []
            []
            []
            [])
           "<;>"
           (Tactic.cc "cc"))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.«tactic_<;>_»
       (Tactic.simp
        "simp"
        [(Tactic.config
          "("
          "config"
          ":="
          (Term.structInst
           "{"
           []
           [(Term.structInstField (Term.structInstLVal `contextual []) ":=" `true)]
           (Term.optEllipsis [])
           []
           "}")
          ")")]
        []
        []
        []
        [])
       "<;>"
       (Tactic.cc "cc"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.cc "cc")
[PrettyPrinter.parenthesize] ...precedences are 2 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
      (Tactic.simp
       "simp"
       [(Tactic.config
         "("
         "config"
         ":="
         (Term.structInst
          "{"
          []
          [(Term.structInstField (Term.structInstLVal `contextual []) ":=" `true)]
          (Term.optEllipsis [])
          []
          "}")
         ")")]
       []
       []
       []
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.structInst
       "{"
       []
       [(Term.structInstField (Term.structInstLVal `contextual []) ":=" `true)]
       (Term.optEllipsis [])
       []
       "}")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `true
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0,
     tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(Tactic.«tactic_<;>_»
          (Tactic.simp
           "simp"
           [(Tactic.config
             "("
             "config"
             ":="
             (Term.structInst
              "{"
              []
              [(Term.structInstField (Term.structInstLVal `contextual []) ":=" `true)]
              (Term.optEllipsis [])
              []
              "}")
             ")")]
           []
           []
           []
           [])
          "<;>"
          (Tactic.cc "cc"))])))
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `add_zero)
             ","
             (Tactic.rwRule [] `fold_zero)
             ","
             (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `fold_cons'_right)
             ","
             (Tactic.rwRule [(patternIgnore (token.«← » "←"))] (Term.app `fold_cons_right [`op]))]
            "]")
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `add_zero)
         ","
         (Tactic.rwRule [] `fold_zero)
         ","
         (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `fold_cons'_right)
         ","
         (Tactic.rwRule [(patternIgnore (token.«← » "←"))] (Term.app `fold_cons_right [`op]))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `fold_cons_right [`op])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `op
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `fold_cons_right
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `fold_cons'_right
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `fold_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `add_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, tactic) <=? (some 1024, term)
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
           [(Tactic.rwRule [] `add_zero)
            ","
            (Tactic.rwRule [] `fold_zero)
            ","
            (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `fold_cons'_right)
            ","
            (Tactic.rwRule [(patternIgnore (token.«← » "←"))] (Term.app `fold_cons_right [`op]))]
           "]")
          [])])))
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `s₂
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Multiset.induction_on
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app
        (Term.proj («term_+_» `s₁ "+" `s₂) "." `fold)
        [`op (Multiset.Data.Multiset.Fold.op `b₁ " * " `b₂)])
       "="
       (Multiset.Data.Multiset.Fold.op
        (Term.app (Term.proj `s₁ "." `fold) [`op `b₁])
        " * "
        (Term.app (Term.proj `s₂ "." `fold) [`op `b₂])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Multiset.Data.Multiset.Fold.op
       (Term.app (Term.proj `s₁ "." `fold) [`op `b₁])
       " * "
       (Term.app (Term.proj `s₂ "." `fold) [`op `b₂]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Multiset.Data.Multiset.Fold.op', expected 'Multiset.Data.Multiset.Fold.op._@.Data.Multiset.Fold._hyg.7'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  fold_add
  ( b₁ b₂ : α ) ( s₁ s₂ : Multiset α )
    : s₁ + s₂ . fold op b₁ * b₂ = s₁ . fold op b₁ * s₂ . fold op b₂
  :=
    Multiset.induction_on
      s₂
        by rw [ add_zero , fold_zero , ← fold_cons'_right , ← fold_cons_right op ]
        by simp ( config := { contextual := true } ) <;> cc
#align multiset.fold_add Multiset.fold_add

theorem fold_bind {ι : Type _} (s : Multiset ι) (t : ι → Multiset α) (b : ι → α) (b₀ : α) :
    (s.bind t).fold op ((s.map b).fold op b₀) = (s.map fun i => (t i).fold op (b i)).fold op b₀ :=
  by
  induction' s using Multiset.induction_on with a ha ih
  · rw [zero_bind, map_zero, map_zero, fold_zero]
  · rw [cons_bind, map_cons, map_cons, fold_cons_left, fold_cons_left, fold_add, ih]
#align multiset.fold_bind Multiset.fold_bind

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `fold_singleton [])
      (Command.declSig
       [(Term.explicitBinder "(" [`b `a] [":" `α] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app
          (Term.proj
           (Term.typeAscription "(" («term{_}» "{" [`a] "}") ":" [(Term.app `Multiset [`α])] ")")
           "."
           `fold)
          [`op `b])
         "="
         (Multiset.Data.Multiset.Fold.op `a " * " `b))))
      (Command.declValSimple
       ":="
       (Term.app `foldr_singleton [(Term.hole "_") (Term.hole "_") (Term.hole "_") (Term.hole "_")])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `foldr_singleton [(Term.hole "_") (Term.hole "_") (Term.hole "_") (Term.hole "_")])
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `foldr_singleton
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app
        (Term.proj
         (Term.typeAscription "(" («term{_}» "{" [`a] "}") ":" [(Term.app `Multiset [`α])] ")")
         "."
         `fold)
        [`op `b])
       "="
       (Multiset.Data.Multiset.Fold.op `a " * " `b))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Multiset.Data.Multiset.Fold.op `a " * " `b)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Multiset.Data.Multiset.Fold.op', expected 'Multiset.Data.Multiset.Fold.op._@.Data.Multiset.Fold._hyg.7'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  fold_singleton
  ( b a : α ) : ( { a } : Multiset α ) . fold op b = a * b
  := foldr_singleton _ _ _ _
#align multiset.fold_singleton Multiset.fold_singleton

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `fold_distrib [])
      (Command.declSig
       [(Term.implicitBinder "{" [`f `g] [":" (Term.arrow `β "→" `α)] "}")
        (Term.explicitBinder "(" [`u₁ `u₂] [":" `α] [] ")")
        (Term.explicitBinder "(" [`s] [":" (Term.app `Multiset [`β])] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app
          (Term.proj
           (Term.app
            (Term.proj `s "." `map)
            [(Term.fun
              "fun"
              (Term.basicFun
               [`x]
               []
               "=>"
               (Multiset.Data.Multiset.Fold.op (Term.app `f [`x]) " * " (Term.app `g [`x]))))])
           "."
           `fold)
          [`op (Multiset.Data.Multiset.Fold.op `u₁ " * " `u₂)])
         "="
         (Multiset.Data.Multiset.Fold.op
          (Term.app (Term.proj (Term.app (Term.proj `s "." `map) [`f]) "." `fold) [`op `u₁])
          " * "
          (Term.app (Term.proj (Term.app (Term.proj `s "." `map) [`g]) "." `fold) [`op `u₂])))))
      (Command.declValSimple
       ":="
       (Term.app
        `Multiset.induction_on
        [`s
         (Term.byTactic
          "by"
          (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])])))
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.«tactic_<;>_»
              (Tactic.simp
               "simp"
               [(Tactic.config
                 "("
                 "config"
                 ":="
                 (Term.structInst
                  "{"
                  []
                  [(Term.structInstField (Term.structInstLVal `contextual []) ":=" `true)]
                  (Term.optEllipsis [])
                  []
                  "}")
                 ")")]
               []
               []
               []
               [])
              "<;>"
              (Tactic.cc "cc"))])))])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Multiset.induction_on
       [`s
        (Term.byTactic
         "by"
         (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])])))
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Tactic.«tactic_<;>_»
             (Tactic.simp
              "simp"
              [(Tactic.config
                "("
                "config"
                ":="
                (Term.structInst
                 "{"
                 []
                 [(Term.structInstField (Term.structInstLVal `contextual []) ":=" `true)]
                 (Term.optEllipsis [])
                 []
                 "}")
                ")")]
              []
              []
              []
              [])
             "<;>"
             (Tactic.cc "cc"))])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.«tactic_<;>_»
           (Tactic.simp
            "simp"
            [(Tactic.config
              "("
              "config"
              ":="
              (Term.structInst
               "{"
               []
               [(Term.structInstField (Term.structInstLVal `contextual []) ":=" `true)]
               (Term.optEllipsis [])
               []
               "}")
              ")")]
            []
            []
            []
            [])
           "<;>"
           (Tactic.cc "cc"))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.«tactic_<;>_»
       (Tactic.simp
        "simp"
        [(Tactic.config
          "("
          "config"
          ":="
          (Term.structInst
           "{"
           []
           [(Term.structInstField (Term.structInstLVal `contextual []) ":=" `true)]
           (Term.optEllipsis [])
           []
           "}")
          ")")]
        []
        []
        []
        [])
       "<;>"
       (Tactic.cc "cc"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.cc "cc")
[PrettyPrinter.parenthesize] ...precedences are 2 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
      (Tactic.simp
       "simp"
       [(Tactic.config
         "("
         "config"
         ":="
         (Term.structInst
          "{"
          []
          [(Term.structInstField (Term.structInstLVal `contextual []) ":=" `true)]
          (Term.optEllipsis [])
          []
          "}")
         ")")]
       []
       []
       []
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.structInst
       "{"
       []
       [(Term.structInstField (Term.structInstLVal `contextual []) ":=" `true)]
       (Term.optEllipsis [])
       []
       "}")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `true
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0,
     tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(Tactic.«tactic_<;>_»
          (Tactic.simp
           "simp"
           [(Tactic.config
             "("
             "config"
             ":="
             (Term.structInst
              "{"
              []
              [(Term.structInstField (Term.structInstLVal `contextual []) ":=" `true)]
              (Term.optEllipsis [])
              []
              "}")
             ")")]
           []
           []
           []
           [])
          "<;>"
          (Tactic.cc "cc"))])))
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] [] [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, tactic) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.byTactic
      "by"
      (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])])))
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `s
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Multiset.induction_on
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app
        (Term.proj
         (Term.app
          (Term.proj `s "." `map)
          [(Term.fun
            "fun"
            (Term.basicFun
             [`x]
             []
             "=>"
             (Multiset.Data.Multiset.Fold.op (Term.app `f [`x]) " * " (Term.app `g [`x]))))])
         "."
         `fold)
        [`op (Multiset.Data.Multiset.Fold.op `u₁ " * " `u₂)])
       "="
       (Multiset.Data.Multiset.Fold.op
        (Term.app (Term.proj (Term.app (Term.proj `s "." `map) [`f]) "." `fold) [`op `u₁])
        " * "
        (Term.app (Term.proj (Term.app (Term.proj `s "." `map) [`g]) "." `fold) [`op `u₂])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Multiset.Data.Multiset.Fold.op
       (Term.app (Term.proj (Term.app (Term.proj `s "." `map) [`f]) "." `fold) [`op `u₁])
       " * "
       (Term.app (Term.proj (Term.app (Term.proj `s "." `map) [`g]) "." `fold) [`op `u₂]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Multiset.Data.Multiset.Fold.op', expected 'Multiset.Data.Multiset.Fold.op._@.Data.Multiset.Fold._hyg.7'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  fold_distrib
  { f g : β → α } ( u₁ u₂ : α ) ( s : Multiset β )
    : s . map fun x => f x * g x . fold op u₁ * u₂ = s . map f . fold op u₁ * s . map g . fold op u₂
  := Multiset.induction_on s by simp by simp ( config := { contextual := true } ) <;> cc
#align multiset.fold_distrib Multiset.fold_distrib

theorem fold_hom {op' : β → β → β} [IsCommutative β op'] [IsAssociative β op'] {m : α → β}
    (hm : ∀ x y, m (op x y) = op' (m x) (m y)) (b : α) (s : Multiset α) :
    (s.map m).fold op' (m b) = m (s.fold op b) :=
  Multiset.induction_on s (by simp) (by simp (config := { contextual := true }) [hm])
#align multiset.fold_hom Multiset.fold_hom

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `fold_union_inter [])
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `DecidableEq [`α]) "]")
        (Term.explicitBinder "(" [`s₁ `s₂] [":" (Term.app `Multiset [`α])] [] ")")
        (Term.explicitBinder "(" [`b₁ `b₂] [":" `α] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Multiset.Data.Multiset.Fold.op
          (Term.app (Term.proj («term_∪_» `s₁ "∪" `s₂) "." `fold) [`op `b₁])
          " * "
          (Term.app (Term.proj («term_∩_» `s₁ "∩" `s₂) "." `fold) [`op `b₂]))
         "="
         (Multiset.Data.Multiset.Fold.op
          (Term.app (Term.proj `s₁ "." `fold) [`op `b₁])
          " * "
          (Term.app (Term.proj `s₂ "." `fold) [`op `b₂])))))
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
             [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] (Term.app `fold_add [`op]))
              ","
              (Tactic.rwRule [] `union_add_inter)
              ","
              (Tactic.rwRule [] (Term.app `fold_add [`op]))]
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
            [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] (Term.app `fold_add [`op]))
             ","
             (Tactic.rwRule [] `union_add_inter)
             ","
             (Tactic.rwRule [] (Term.app `fold_add [`op]))]
            "]")
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] (Term.app `fold_add [`op]))
         ","
         (Tactic.rwRule [] `union_add_inter)
         ","
         (Tactic.rwRule [] (Term.app `fold_add [`op]))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `fold_add [`op])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `op
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `fold_add
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `union_add_inter
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `fold_add [`op])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `op
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `fold_add
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Multiset.Data.Multiset.Fold.op
        (Term.app (Term.proj («term_∪_» `s₁ "∪" `s₂) "." `fold) [`op `b₁])
        " * "
        (Term.app (Term.proj («term_∩_» `s₁ "∩" `s₂) "." `fold) [`op `b₂]))
       "="
       (Multiset.Data.Multiset.Fold.op
        (Term.app (Term.proj `s₁ "." `fold) [`op `b₁])
        " * "
        (Term.app (Term.proj `s₂ "." `fold) [`op `b₂])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Multiset.Data.Multiset.Fold.op
       (Term.app (Term.proj `s₁ "." `fold) [`op `b₁])
       " * "
       (Term.app (Term.proj `s₂ "." `fold) [`op `b₂]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Multiset.Data.Multiset.Fold.op', expected 'Multiset.Data.Multiset.Fold.op._@.Data.Multiset.Fold._hyg.7'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  fold_union_inter
  [ DecidableEq α ] ( s₁ s₂ : Multiset α ) ( b₁ b₂ : α )
    : s₁ ∪ s₂ . fold op b₁ * s₁ ∩ s₂ . fold op b₂ = s₁ . fold op b₁ * s₂ . fold op b₂
  := by rw [ ← fold_add op , union_add_inter , fold_add op ]
#align multiset.fold_union_inter Multiset.fold_union_inter

@[simp]
theorem fold_dedup_idem [DecidableEq α] [hi : IsIdempotent α op] (s : Multiset α) (b : α) :
    (dedup s).fold op b = s.fold op b :=
  (Multiset.induction_on s (by simp)) fun a s IH =>
    by
    by_cases a ∈ s <;> simp [IH, h]
    show fold op b s = op a (fold op b s)
    rw [← cons_erase h, fold_cons_left, ← ha.assoc, hi.idempotent]
#align multiset.fold_dedup_idem Multiset.fold_dedup_idem

end Fold

section Order

theorem max_le_of_forall_le {α : Type _} [CanonicallyLinearOrderedAddMonoid α] (l : Multiset α)
    (n : α) (h : ∀ x ∈ l, x ≤ n) : l.fold max ⊥ ≤ n :=
  by
  induction l using Quotient.induction_on
  simpa using List.max_le_of_forall_le _ _ h
#align multiset.max_le_of_forall_le Multiset.max_le_of_forall_le

theorem max_nat_le_of_forall_le (l : Multiset ℕ) (n : ℕ) (h : ∀ x ∈ l, x ≤ n) : l.fold max 0 ≤ n :=
  max_le_of_forall_le l n h
#align multiset.max_nat_le_of_forall_le Multiset.max_nat_le_of_forall_le

end Order

open Nat

theorem le_smul_dedup [DecidableEq α] (s : Multiset α) : ∃ n : ℕ, s ≤ n • dedup s :=
  ⟨(s.map fun a => count a s).fold max 0,
    le_iff_count.2 fun a => by
      rw [count_nsmul]; by_cases a ∈ s
      · refine' le_trans _ (Nat.mul_le_mul_left _ <| count_pos.2 <| mem_dedup.2 h)
        have : count a s ≤ fold max 0 (map (fun a => count a s) (a ::ₘ erase s a)) <;>
          [simp [le_max_left], simpa [cons_erase h] ]
      · simp [count_eq_zero.2 h, Nat.zero_le]⟩
#align multiset.le_smul_dedup Multiset.le_smul_dedup

end Multiset

