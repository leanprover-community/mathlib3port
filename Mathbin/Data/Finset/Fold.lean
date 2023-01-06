/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

! This file was ported from Lean 3 source module data.finset.fold
! leanprover-community/mathlib commit 26f081a2fb920140ed5bc5cc5344e84bcc7cb2b2
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Order.Monoid.WithTop
import Mathbin.Data.Finset.Image
import Mathbin.Data.Multiset.Fold

/-!
# The fold operation for a commutative associative operation over a finset.
-/


namespace Finset

open Multiset

variable {α β γ : Type _}

/-! ### fold -/


section Fold

variable (op : β → β → β) [hc : IsCommutative β op] [ha : IsAssociative β op]

-- mathport name: op
local notation a " * " b => op a b

include hc ha

/-- `fold op b f s` folds the commutative associative operation `op` over the
  `f`-image of `s`, i.e. `fold (+) b f {1,2,3} = f 1 + f 2 + f 3 + b`. -/
def fold (b : β) (f : α → β) (s : Finset α) : β :=
  (s.1.map f).fold op b
#align finset.fold Finset.fold

variable {op} {f : α → β} {b : β} {s : Finset α} {a : α}

@[simp]
theorem fold_empty : (∅ : Finset α).fold op b f = b :=
  rfl
#align finset.fold_empty Finset.fold_empty

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
      (Command.declId `fold_cons [])
      (Command.declSig
       [(Term.explicitBinder "(" [`h] [":" («term_∉_» `a "∉" `s)] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app (Term.proj (Term.app `cons [`a `s `h]) "." `fold) [`op `b `f])
         "="
         (Finset.Data.Finset.Fold.op
          (Term.app `f [`a])
          " * "
          (Term.app (Term.proj `s "." `fold) [`op `b `f])))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.dsimp "dsimp" [] [] ["only"] ["[" [(Tactic.simpLemma [] [] `fold)] "]"] [])
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [] `cons_val)
              ","
              (Tactic.rwRule [] `Multiset.map_cons)
              ","
              (Tactic.rwRule [] `fold_cons_left)]
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
         [(Tactic.dsimp "dsimp" [] [] ["only"] ["[" [(Tactic.simpLemma [] [] `fold)] "]"] [])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `cons_val)
             ","
             (Tactic.rwRule [] `Multiset.map_cons)
             ","
             (Tactic.rwRule [] `fold_cons_left)]
            "]")
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `cons_val)
         ","
         (Tactic.rwRule [] `Multiset.map_cons)
         ","
         (Tactic.rwRule [] `fold_cons_left)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `fold_cons_left
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Multiset.map_cons
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `cons_val
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.dsimp "dsimp" [] [] ["only"] ["[" [(Tactic.simpLemma [] [] `fold)] "]"] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `fold
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app (Term.proj (Term.app `cons [`a `s `h]) "." `fold) [`op `b `f])
       "="
       (Finset.Data.Finset.Fold.op
        (Term.app `f [`a])
        " * "
        (Term.app (Term.proj `s "." `fold) [`op `b `f])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Finset.Data.Finset.Fold.op
       (Term.app `f [`a])
       " * "
       (Term.app (Term.proj `s "." `fold) [`op `b `f]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.op', expected 'Finset.Data.Finset.Fold.op._@.Data.Finset.Fold._hyg.8'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ simp ]
  theorem
    fold_cons
    ( h : a ∉ s ) : cons a s h . fold op b f = f a * s . fold op b f
    := by dsimp only [ fold ] rw [ cons_val , Multiset.map_cons , fold_cons_left ]
#align finset.fold_cons Finset.fold_cons

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
      (Command.declId `fold_insert [])
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `DecidableEq [`α]) "]")
        (Term.explicitBinder "(" [`h] [":" («term_∉_» `a "∉" `s)] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app (Term.proj (Term.app `insert [`a `s]) "." `fold) [`op `b `f])
         "="
         (Finset.Data.Finset.Fold.op
          (Term.app `f [`a])
          " * "
          (Term.app (Term.proj `s "." `fold) [`op `b `f])))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.«tactic_<;>_»
            (Tactic.unfold "unfold" [`fold] [])
            "<;>"
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] `insert_val)
               ","
               (Tactic.rwRule [] (Term.app `ndinsert_of_not_mem [`h]))
               ","
               (Tactic.rwRule [] `Multiset.map_cons)
               ","
               (Tactic.rwRule [] `fold_cons_left)]
              "]")
             []))])))
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
           (Tactic.unfold "unfold" [`fold] [])
           "<;>"
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [] `insert_val)
              ","
              (Tactic.rwRule [] (Term.app `ndinsert_of_not_mem [`h]))
              ","
              (Tactic.rwRule [] `Multiset.map_cons)
              ","
              (Tactic.rwRule [] `fold_cons_left)]
             "]")
            []))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.«tactic_<;>_»
       (Tactic.unfold "unfold" [`fold] [])
       "<;>"
       (Tactic.rwSeq
        "rw"
        []
        (Tactic.rwRuleSeq
         "["
         [(Tactic.rwRule [] `insert_val)
          ","
          (Tactic.rwRule [] (Term.app `ndinsert_of_not_mem [`h]))
          ","
          (Tactic.rwRule [] `Multiset.map_cons)
          ","
          (Tactic.rwRule [] `fold_cons_left)]
         "]")
        []))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `insert_val)
         ","
         (Tactic.rwRule [] (Term.app `ndinsert_of_not_mem [`h]))
         ","
         (Tactic.rwRule [] `Multiset.map_cons)
         ","
         (Tactic.rwRule [] `fold_cons_left)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `fold_cons_left
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Multiset.map_cons
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `ndinsert_of_not_mem [`h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `ndinsert_of_not_mem
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `insert_val
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 2 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
      (Tactic.unfold "unfold" [`fold] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app (Term.proj (Term.app `insert [`a `s]) "." `fold) [`op `b `f])
       "="
       (Finset.Data.Finset.Fold.op
        (Term.app `f [`a])
        " * "
        (Term.app (Term.proj `s "." `fold) [`op `b `f])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Finset.Data.Finset.Fold.op
       (Term.app `f [`a])
       " * "
       (Term.app (Term.proj `s "." `fold) [`op `b `f]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.op', expected 'Finset.Data.Finset.Fold.op._@.Data.Finset.Fold._hyg.8'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ simp ]
  theorem
    fold_insert
    [ DecidableEq α ] ( h : a ∉ s ) : insert a s . fold op b f = f a * s . fold op b f
    :=
      by
        unfold fold
          <;>
          rw [ insert_val , ndinsert_of_not_mem h , Multiset.map_cons , fold_cons_left ]
#align finset.fold_insert Finset.fold_insert

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
      (Command.declId `fold_singleton [])
      (Command.declSig
       []
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app
          (Term.proj
           (Term.typeAscription "(" («term{_}» "{" [`a] "}") ":" [(Term.app `Finset [`α])] ")")
           "."
           `fold)
          [`op `b `f])
         "="
         (Finset.Data.Finset.Fold.op (Term.app `f [`a]) " * " `b))))
      (Command.declValSimple ":=" `rfl [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rfl
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app
        (Term.proj
         (Term.typeAscription "(" («term{_}» "{" [`a] "}") ":" [(Term.app `Finset [`α])] ")")
         "."
         `fold)
        [`op `b `f])
       "="
       (Finset.Data.Finset.Fold.op (Term.app `f [`a]) " * " `b))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Finset.Data.Finset.Fold.op (Term.app `f [`a]) " * " `b)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.op', expected 'Finset.Data.Finset.Fold.op._@.Data.Finset.Fold._hyg.8'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ simp ] theorem fold_singleton : ( { a } : Finset α ) . fold op b f = f a * b := rfl
#align finset.fold_singleton Finset.fold_singleton

@[simp]
theorem fold_map {g : γ ↪ α} {s : Finset γ} : (s.map g).fold op b f = s.fold op b (f ∘ g) := by
  simp only [fold, map, Multiset.map_map]
#align finset.fold_map Finset.fold_map

@[simp]
theorem fold_image [DecidableEq α] {g : γ → α} {s : Finset γ}
    (H : ∀ x ∈ s, ∀ y ∈ s, g x = g y → x = y) : (s.image g).fold op b f = s.fold op b (f ∘ g) := by
  simp only [fold, image_val_of_inj_on H, Multiset.map_map]
#align finset.fold_image Finset.fold_image

@[congr]
theorem fold_congr {g : α → β} (H : ∀ x ∈ s, f x = g x) : s.fold op b f = s.fold op b g := by
  rw [fold, fold, map_congr rfl H]
#align finset.fold_congr Finset.fold_congr

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `fold_op_distrib [])
      (Command.declSig
       [(Term.implicitBinder "{" [`f `g] [":" (Term.arrow `α "→" `β)] "}")
        (Term.implicitBinder "{" [`b₁ `b₂] [":" `β] "}")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app
          (Term.proj `s "." `fold)
          [`op
           (Finset.Data.Finset.Fold.op `b₁ " * " `b₂)
           (Term.fun
            "fun"
            (Term.basicFun
             [`x]
             []
             "=>"
             (Finset.Data.Finset.Fold.op (Term.app `f [`x]) " * " (Term.app `g [`x]))))])
         "="
         (Finset.Data.Finset.Fold.op
          (Term.app (Term.proj `s "." `fold) [`op `b₁ `f])
          " * "
          (Term.app (Term.proj `s "." `fold) [`op `b₂ `g])))))
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
            ["[" [(Tactic.simpLemma [] [] `fold) "," (Tactic.simpLemma [] [] `fold_distrib)] "]"]
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
           ["[" [(Tactic.simpLemma [] [] `fold) "," (Tactic.simpLemma [] [] `fold_distrib)] "]"]
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["[" [(Tactic.simpLemma [] [] `fold) "," (Tactic.simpLemma [] [] `fold_distrib)] "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `fold_distrib
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `fold
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app
        (Term.proj `s "." `fold)
        [`op
         (Finset.Data.Finset.Fold.op `b₁ " * " `b₂)
         (Term.fun
          "fun"
          (Term.basicFun
           [`x]
           []
           "=>"
           (Finset.Data.Finset.Fold.op (Term.app `f [`x]) " * " (Term.app `g [`x]))))])
       "="
       (Finset.Data.Finset.Fold.op
        (Term.app (Term.proj `s "." `fold) [`op `b₁ `f])
        " * "
        (Term.app (Term.proj `s "." `fold) [`op `b₂ `g])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Finset.Data.Finset.Fold.op
       (Term.app (Term.proj `s "." `fold) [`op `b₁ `f])
       " * "
       (Term.app (Term.proj `s "." `fold) [`op `b₂ `g]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.op', expected 'Finset.Data.Finset.Fold.op._@.Data.Finset.Fold._hyg.8'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  fold_op_distrib
  { f g : α → β } { b₁ b₂ : β }
    : s . fold op b₁ * b₂ fun x => f x * g x = s . fold op b₁ f * s . fold op b₂ g
  := by simp only [ fold , fold_distrib ]
#align finset.fold_op_distrib Finset.fold_op_distrib

theorem fold_const [Decidable (s = ∅)] (c : β) (h : op c (op b c) = op b c) :
    Finset.fold op b (fun _ => c) s = if s = ∅ then b else op b c := by
  classical
    induction' s using Finset.induction_on with x s hx IH
    · simp
    · simp only [Finset.fold_insert hx, IH, if_false, Finset.insert_ne_empty]
      split_ifs
      · rw [hc.comm]
      · exact h
#align finset.fold_const Finset.fold_const

theorem fold_hom {op' : γ → γ → γ} [IsCommutative γ op'] [IsAssociative γ op'] {m : β → γ}
    (hm : ∀ x y, m (op x y) = op' (m x) (m y)) :
    (s.fold op' (m b) fun x => m (f x)) = m (s.fold op b f) := by
  rw [fold, fold, ← fold_hom op hm, Multiset.map_map]
#align finset.fold_hom Finset.fold_hom

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `fold_disj_union [])
      (Command.declSig
       [(Term.implicitBinder "{" [`s₁ `s₂] [":" (Term.app `Finset [`α])] "}")
        (Term.implicitBinder "{" [`b₁ `b₂] [":" `β] "}")
        (Term.explicitBinder "(" [`h] [] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app
          (Term.proj (Term.app (Term.proj `s₁ "." `disjUnion) [`s₂ `h]) "." `fold)
          [`op (Finset.Data.Finset.Fold.op `b₁ " * " `b₂) `f])
         "="
         (Finset.Data.Finset.Fold.op
          (Term.app (Term.proj `s₁ "." `fold) [`op `b₁ `f])
          " * "
          (Term.app (Term.proj `s₂ "." `fold) [`op `b₂ `f])))))
      (Command.declValSimple
       ":="
       (Term.app
        (Term.proj
         («term_<|_»
          (Term.app `congr_arg [(Term.hole "_")])
          "<|"
          (Term.app `Multiset.map_add [(Term.hole "_") (Term.hole "_") (Term.hole "_")]))
         "."
         `trans)
        [(Term.app
          `Multiset.fold_add
          [(Term.hole "_") (Term.hole "_") (Term.hole "_") (Term.hole "_") (Term.hole "_")])])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        («term_<|_»
         (Term.app `congr_arg [(Term.hole "_")])
         "<|"
         (Term.app `Multiset.map_add [(Term.hole "_") (Term.hole "_") (Term.hole "_")]))
        "."
        `trans)
       [(Term.app
         `Multiset.fold_add
         [(Term.hole "_") (Term.hole "_") (Term.hole "_") (Term.hole "_") (Term.hole "_")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Multiset.fold_add
       [(Term.hole "_") (Term.hole "_") (Term.hole "_") (Term.hole "_") (Term.hole "_")])
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Multiset.fold_add
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `Multiset.fold_add
      [(Term.hole "_") (Term.hole "_") (Term.hole "_") (Term.hole "_") (Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       («term_<|_»
        (Term.app `congr_arg [(Term.hole "_")])
        "<|"
        (Term.app `Multiset.map_add [(Term.hole "_") (Term.hole "_") (Term.hole "_")]))
       "."
       `trans)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      («term_<|_»
       (Term.app `congr_arg [(Term.hole "_")])
       "<|"
       (Term.app `Multiset.map_add [(Term.hole "_") (Term.hole "_") (Term.hole "_")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Multiset.map_add [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
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
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Multiset.map_add
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      (Term.app `congr_arg [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `congr_arg
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 10, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_<|_»
      (Term.app `congr_arg [(Term.hole "_")])
      "<|"
      (Term.app `Multiset.map_add [(Term.hole "_") (Term.hole "_") (Term.hole "_")]))
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app
        (Term.proj (Term.app (Term.proj `s₁ "." `disjUnion) [`s₂ `h]) "." `fold)
        [`op (Finset.Data.Finset.Fold.op `b₁ " * " `b₂) `f])
       "="
       (Finset.Data.Finset.Fold.op
        (Term.app (Term.proj `s₁ "." `fold) [`op `b₁ `f])
        " * "
        (Term.app (Term.proj `s₂ "." `fold) [`op `b₂ `f])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Finset.Data.Finset.Fold.op
       (Term.app (Term.proj `s₁ "." `fold) [`op `b₁ `f])
       " * "
       (Term.app (Term.proj `s₂ "." `fold) [`op `b₂ `f]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.op', expected 'Finset.Data.Finset.Fold.op._@.Data.Finset.Fold._hyg.8'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  fold_disj_union
  { s₁ s₂ : Finset α } { b₁ b₂ : β } ( h )
    : s₁ . disjUnion s₂ h . fold op b₁ * b₂ f = s₁ . fold op b₁ f * s₂ . fold op b₂ f
  := congr_arg _ <| Multiset.map_add _ _ _ . trans Multiset.fold_add _ _ _ _ _
#align finset.fold_disj_union Finset.fold_disj_union

theorem fold_disj_Union {ι : Type _} {s : Finset ι} {t : ι → Finset α} {b : ι → β} {b₀ : β} (h) :
    (s.disjUnion t h).fold op (s.fold op b₀ b) f = s.fold op b₀ fun i => (t i).fold op (b i) f :=
  (congr_arg _ <| Multiset.map_bind _ _ _).trans (Multiset.fold_bind _ _ _ _ _)
#align finset.fold_disj_Union Finset.fold_disj_Union

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `fold_union_inter [])
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `DecidableEq [`α]) "]")
        (Term.implicitBinder "{" [`s₁ `s₂] [":" (Term.app `Finset [`α])] "}")
        (Term.implicitBinder "{" [`b₁ `b₂] [":" `β] "}")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Finset.Data.Finset.Fold.op
          (Term.app (Term.proj («term_∪_» `s₁ "∪" `s₂) "." `fold) [`op `b₁ `f])
          " * "
          (Term.app (Term.proj («term_∩_» `s₁ "∩" `s₂) "." `fold) [`op `b₂ `f]))
         "="
         (Finset.Data.Finset.Fold.op
          (Term.app (Term.proj `s₁ "." `fold) [`op `b₂ `f])
          " * "
          (Term.app (Term.proj `s₂ "." `fold) [`op `b₁ `f])))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.«tactic_<;>_»
            (Tactic.unfold "unfold" [`fold] [])
            "<;>"
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] (Term.app `fold_add [`op]))
               ","
               (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Multiset.map_add)
               ","
               (Tactic.rwRule [] `union_val)
               ","
               (Tactic.rwRule [] `inter_val)
               ","
               (Tactic.rwRule [] `union_add_inter)
               ","
               (Tactic.rwRule [] `Multiset.map_add)
               ","
               (Tactic.rwRule [] `hc.comm)
               ","
               (Tactic.rwRule [] `fold_add)]
              "]")
             []))])))
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
           (Tactic.unfold "unfold" [`fold] [])
           "<;>"
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] (Term.app `fold_add [`op]))
              ","
              (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Multiset.map_add)
              ","
              (Tactic.rwRule [] `union_val)
              ","
              (Tactic.rwRule [] `inter_val)
              ","
              (Tactic.rwRule [] `union_add_inter)
              ","
              (Tactic.rwRule [] `Multiset.map_add)
              ","
              (Tactic.rwRule [] `hc.comm)
              ","
              (Tactic.rwRule [] `fold_add)]
             "]")
            []))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.«tactic_<;>_»
       (Tactic.unfold "unfold" [`fold] [])
       "<;>"
       (Tactic.rwSeq
        "rw"
        []
        (Tactic.rwRuleSeq
         "["
         [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] (Term.app `fold_add [`op]))
          ","
          (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Multiset.map_add)
          ","
          (Tactic.rwRule [] `union_val)
          ","
          (Tactic.rwRule [] `inter_val)
          ","
          (Tactic.rwRule [] `union_add_inter)
          ","
          (Tactic.rwRule [] `Multiset.map_add)
          ","
          (Tactic.rwRule [] `hc.comm)
          ","
          (Tactic.rwRule [] `fold_add)]
         "]")
        []))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] (Term.app `fold_add [`op]))
         ","
         (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Multiset.map_add)
         ","
         (Tactic.rwRule [] `union_val)
         ","
         (Tactic.rwRule [] `inter_val)
         ","
         (Tactic.rwRule [] `union_add_inter)
         ","
         (Tactic.rwRule [] `Multiset.map_add)
         ","
         (Tactic.rwRule [] `hc.comm)
         ","
         (Tactic.rwRule [] `fold_add)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `fold_add
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hc.comm
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Multiset.map_add
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `union_add_inter
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `inter_val
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `union_val
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Multiset.map_add
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
[PrettyPrinter.parenthesize] ...precedences are 2 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
      (Tactic.unfold "unfold" [`fold] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Finset.Data.Finset.Fold.op
        (Term.app (Term.proj («term_∪_» `s₁ "∪" `s₂) "." `fold) [`op `b₁ `f])
        " * "
        (Term.app (Term.proj («term_∩_» `s₁ "∩" `s₂) "." `fold) [`op `b₂ `f]))
       "="
       (Finset.Data.Finset.Fold.op
        (Term.app (Term.proj `s₁ "." `fold) [`op `b₂ `f])
        " * "
        (Term.app (Term.proj `s₂ "." `fold) [`op `b₁ `f])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Finset.Data.Finset.Fold.op
       (Term.app (Term.proj `s₁ "." `fold) [`op `b₂ `f])
       " * "
       (Term.app (Term.proj `s₂ "." `fold) [`op `b₁ `f]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.op', expected 'Finset.Data.Finset.Fold.op._@.Data.Finset.Fold._hyg.8'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  fold_union_inter
  [ DecidableEq α ] { s₁ s₂ : Finset α } { b₁ b₂ : β }
    : s₁ ∪ s₂ . fold op b₁ f * s₁ ∩ s₂ . fold op b₂ f = s₁ . fold op b₂ f * s₂ . fold op b₁ f
  :=
    by
      unfold fold
        <;>
        rw
          [
            ← fold_add op
              ,
              ← Multiset.map_add
              ,
              union_val
              ,
              inter_val
              ,
              union_add_inter
              ,
              Multiset.map_add
              ,
              hc.comm
              ,
              fold_add
            ]
#align finset.fold_union_inter Finset.fold_union_inter

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
      (Command.declId `fold_insert_idem [])
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `DecidableEq [`α]) "]")
        (Term.instBinder "[" [`hi ":"] (Term.app `IsIdempotent [`β `op]) "]")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app (Term.proj (Term.app `insert [`a `s]) "." `fold) [`op `b `f])
         "="
         (Finset.Data.Finset.Fold.op
          (Term.app `f [`a])
          " * "
          (Term.app (Term.proj `s "." `fold) [`op `b `f])))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Classical.«tacticBy_cases_:_» "by_cases" [] («term_∈_» `a "∈" `s))
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] (Term.app `insert_erase [`h]))]
               "]")
              [])
             []
             (Tactic.simp
              "simp"
              []
              []
              []
              ["["
               [(Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `ha.assoc)
                ","
                (Tactic.simpLemma [] [] `hi.idempotent)]
               "]"]
              [])])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.apply "apply" (Term.app `fold_insert [`h]))])])))
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
         [(Classical.«tacticBy_cases_:_» "by_cases" [] («term_∈_» `a "∈" `s))
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] (Term.app `insert_erase [`h]))]
              "]")
             [])
            []
            (Tactic.simp
             "simp"
             []
             []
             []
             ["["
              [(Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `ha.assoc)
               ","
               (Tactic.simpLemma [] [] `hi.idempotent)]
              "]"]
             [])])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.apply "apply" (Term.app `fold_insert [`h]))])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.apply "apply" (Term.app `fold_insert [`h]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.apply "apply" (Term.app `fold_insert [`h]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `fold_insert [`h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `fold_insert
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
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
          [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] (Term.app `insert_erase [`h]))]
          "]")
         [])
        []
        (Tactic.simp
         "simp"
         []
         []
         []
         ["["
          [(Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `ha.assoc)
           ","
           (Tactic.simpLemma [] [] `hi.idempotent)]
          "]"]
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       []
       ["["
        [(Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `ha.assoc)
         ","
         (Tactic.simpLemma [] [] `hi.idempotent)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hi.idempotent
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ha.assoc
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] (Term.app `insert_erase [`h]))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `insert_erase [`h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `insert_erase
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Classical.«tacticBy_cases_:_» "by_cases" [] («term_∈_» `a "∈" `s))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∈_» `a "∈" `s)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `s
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `a
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app (Term.proj (Term.app `insert [`a `s]) "." `fold) [`op `b `f])
       "="
       (Finset.Data.Finset.Fold.op
        (Term.app `f [`a])
        " * "
        (Term.app (Term.proj `s "." `fold) [`op `b `f])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Finset.Data.Finset.Fold.op
       (Term.app `f [`a])
       " * "
       (Term.app (Term.proj `s "." `fold) [`op `b `f]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.op', expected 'Finset.Data.Finset.Fold.op._@.Data.Finset.Fold._hyg.8'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ simp ]
  theorem
    fold_insert_idem
    [ DecidableEq α ] [ hi : IsIdempotent β op ] : insert a s . fold op b f = f a * s . fold op b f
    :=
      by
        by_cases a ∈ s
          · rw [ ← insert_erase h ] simp [ ← ha.assoc , hi.idempotent ]
          · apply fold_insert h
#align finset.fold_insert_idem Finset.fold_insert_idem

theorem fold_image_idem [DecidableEq α] {g : γ → α} {s : Finset γ} [hi : IsIdempotent β op] :
    (image g s).fold op b f = s.fold op b (f ∘ g) :=
  by
  induction' s using Finset.cons_induction with x xs hx ih
  · rw [fold_empty, image_empty, fold_empty]
  · haveI := Classical.decEq γ
    rw [fold_cons, cons_eq_insert, image_insert, fold_insert_idem, ih]
#align finset.fold_image_idem Finset.fold_image_idem

/-- A stronger version of `finset.fold_ite`, but relies on
an explicit proof of idempotency on the seed element, rather
than relying on typeclass idempotency over the whole type. -/
theorem fold_ite' {g : α → β} (hb : op b b = b) (p : α → Prop) [DecidablePred p] :
    Finset.fold op b (fun i => ite (p i) (f i) (g i)) s =
      op (Finset.fold op b f (s.filter p)) (Finset.fold op b g (s.filter fun i => ¬p i)) :=
  by
  classical
    induction' s using Finset.induction_on with x s hx IH
    · simp [hb]
    · simp only [Finset.filter_congr_decidable, Finset.fold_insert hx]
      split_ifs with h h
      · have : x ∉ Finset.filter p s := by simp [hx]
        simp [Finset.filter_insert, h, Finset.fold_insert this, ha.assoc, IH]
      · have : x ∉ Finset.filter (fun i => ¬p i) s := by simp [hx]
        simp [Finset.filter_insert, h, Finset.fold_insert this, IH, ← ha.assoc, hc.comm]
#align finset.fold_ite' Finset.fold_ite'

/-- A weaker version of `finset.fold_ite'`,
relying on typeclass idempotency over the whole type,
instead of solely on the seed element.
However, this is easier to use because it does not generate side goals. -/
theorem fold_ite [IsIdempotent β op] {g : α → β} (p : α → Prop) [DecidablePred p] :
    Finset.fold op b (fun i => ite (p i) (f i) (g i)) s =
      op (Finset.fold op b f (s.filter p)) (Finset.fold op b g (s.filter fun i => ¬p i)) :=
  fold_ite' (IsIdempotent.idempotent _) _
#align finset.fold_ite Finset.fold_ite

theorem fold_op_rel_iff_and {r : β → β → Prop} (hr : ∀ {x y z}, r x (op y z) ↔ r x y ∧ r x z)
    {c : β} : r c (s.fold op b f) ↔ r c b ∧ ∀ x ∈ s, r c (f x) := by
  classical
    apply Finset.induction_on s
    · simp
    clear s
    intro a s ha IH
    rw [Finset.fold_insert ha, hr, IH, ← and_assoc', and_comm' (r c (f a)), and_assoc']
    apply and_congr Iff.rfl
    constructor
    · rintro ⟨h₁, h₂⟩
      intro b hb
      rw [Finset.mem_insert] at hb
      rcases hb with (rfl | hb) <;> solve_by_elim
    · intro h
      constructor
      · exact h a (Finset.mem_insert_self _ _)
      · intro b hb
        apply h b
        rw [Finset.mem_insert]
        right
        exact hb
#align finset.fold_op_rel_iff_and Finset.fold_op_rel_iff_and

theorem fold_op_rel_iff_or {r : β → β → Prop} (hr : ∀ {x y z}, r x (op y z) ↔ r x y ∨ r x z)
    {c : β} : r c (s.fold op b f) ↔ r c b ∨ ∃ x ∈ s, r c (f x) := by
  classical
    apply Finset.induction_on s
    · simp
    clear s
    intro a s ha IH
    rw [Finset.fold_insert ha, hr, IH, ← or_assoc', or_comm' (r c (f a)), or_assoc']
    apply or_congr Iff.rfl
    constructor
    · rintro (h₁ | ⟨x, hx, h₂⟩)
      · use a
        simp [h₁]
      · refine' ⟨x, by simp [hx], h₂⟩
    · rintro ⟨x, hx, h⟩
      rw [mem_insert] at hx
      cases hx
      · left
        rwa [hx] at h
      · right
        exact ⟨x, hx, h⟩
#align finset.fold_op_rel_iff_or Finset.fold_op_rel_iff_or

omit hc ha

@[simp]
theorem fold_union_empty_singleton [DecidableEq α] (s : Finset α) :
    Finset.fold (· ∪ ·) ∅ singleton s = s :=
  by
  apply Finset.induction_on s
  · simp only [fold_empty]
  · intro a s has ih
    rw [fold_insert has, ih, insert_eq]
#align finset.fold_union_empty_singleton Finset.fold_union_empty_singleton

theorem fold_sup_bot_singleton [DecidableEq α] (s : Finset α) :
    Finset.fold (· ⊔ ·) ⊥ singleton s = s :=
  fold_union_empty_singleton s
#align finset.fold_sup_bot_singleton Finset.fold_sup_bot_singleton

section Order

variable [LinearOrder β] (c : β)

theorem le_fold_min : c ≤ s.fold min b f ↔ c ≤ b ∧ ∀ x ∈ s, c ≤ f x :=
  fold_op_rel_iff_and fun x y z => le_min_iff
#align finset.le_fold_min Finset.le_fold_min

theorem fold_min_le : s.fold min b f ≤ c ↔ b ≤ c ∨ ∃ x ∈ s, f x ≤ c :=
  by
  show _ ≥ _ ↔ _
  apply fold_op_rel_iff_or
  intro x y z
  show _ ≤ _ ↔ _
  exact min_le_iff
#align finset.fold_min_le Finset.fold_min_le

theorem lt_fold_min : c < s.fold min b f ↔ c < b ∧ ∀ x ∈ s, c < f x :=
  fold_op_rel_iff_and fun x y z => lt_min_iff
#align finset.lt_fold_min Finset.lt_fold_min

theorem fold_min_lt : s.fold min b f < c ↔ b < c ∨ ∃ x ∈ s, f x < c :=
  by
  show _ > _ ↔ _
  apply fold_op_rel_iff_or
  intro x y z
  show _ < _ ↔ _
  exact min_lt_iff
#align finset.fold_min_lt Finset.fold_min_lt

theorem fold_max_le : s.fold max b f ≤ c ↔ b ≤ c ∧ ∀ x ∈ s, f x ≤ c :=
  by
  show _ ≥ _ ↔ _
  apply fold_op_rel_iff_and
  intro x y z
  show _ ≤ _ ↔ _
  exact max_le_iff
#align finset.fold_max_le Finset.fold_max_le

theorem le_fold_max : c ≤ s.fold max b f ↔ c ≤ b ∨ ∃ x ∈ s, c ≤ f x :=
  fold_op_rel_iff_or fun x y z => le_max_iff
#align finset.le_fold_max Finset.le_fold_max

theorem fold_max_lt : s.fold max b f < c ↔ b < c ∧ ∀ x ∈ s, f x < c :=
  by
  show _ > _ ↔ _
  apply fold_op_rel_iff_and
  intro x y z
  show _ < _ ↔ _
  exact max_lt_iff
#align finset.fold_max_lt Finset.fold_max_lt

theorem lt_fold_max : c < s.fold max b f ↔ c < b ∨ ∃ x ∈ s, c < f x :=
  fold_op_rel_iff_or fun x y z => lt_max_iff
#align finset.lt_fold_max Finset.lt_fold_max

theorem fold_max_add [Add β] [CovariantClass β β (Function.swap (· + ·)) (· ≤ ·)] (n : WithBot β)
    (s : Finset α) : (s.fold max ⊥ fun x : α => ↑(f x) + n) = s.fold max ⊥ (coe ∘ f) + n := by
  classical apply s.induction_on <;> simp (config := { contextual := true }) [max_add_add_right]
#align finset.fold_max_add Finset.fold_max_add

end Order

end Fold

end Finset

