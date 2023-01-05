/-
Copyright (c) 2015 Joe Hendrix. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joe Hendrix, Sebastian Ullrich

! This file was ported from Lean 3 source module data.bitvec.core
! leanprover-community/mathlib commit 6d0adfa76594f304b4650d098273d4366edeb61b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Vector.Basic
import Mathbin.Data.Nat.Pow

/-!
# Basic operations on bitvectors

This is a work-in-progress, and contains additions to other theories.

This file was moved to mathlib from core Lean in the switch to Lean 3.20.0c.
It is not fully in compliance with mathlib style standards.
-/


/-- `bitvec n` is a `vector` of `bool` with length `n`. -/
@[reducible]
def Bitvec (n : ℕ) :=
  Vector Bool n
#align bitvec Bitvec

namespace Bitvec

open Nat

open Vector

-- mathport name: «expr ++ₜ »
local infixl:65 "++ₜ" => Vector.append

/-- Create a zero bitvector -/
@[reducible]
protected def zero (n : ℕ) : Bitvec n :=
  repeat false n
#align bitvec.zero Bitvec.zero

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "Create a bitvector of length `n` whose `n-1`st entry is 1 and other entries are 0. -/")]
      [(Term.attributes
        "@["
        [(Term.attrInstance (Term.attrKind []) (Attr.simple `reducible []))]
        "]")]
      [(Command.protected "protected")]
      []
      []
      [])
     (Command.def
      "def"
      (Command.declId `one [])
      (Command.optDeclSig
       []
       [(Term.typeSpec
         ":"
         (Term.forall "∀" [`n] [(Term.typeSpec ":" (termℕ "ℕ"))] "," (Term.app `Bitvec [`n])))])
      (Command.declValEqns
       (Term.matchAltsWhereDecls
        (Term.matchAlts
         [(Term.matchAlt "|" [[(num "0")]] "=>" `nil)
          (Term.matchAlt
           "|"
           [[(Term.app `succ [`n])]]
           "=>"
           (Bitvec.Data.Bitvec.Core.«term_++ₜ_»
            (Term.app `repeat [`false `n])
            "++ₜ"
            (Vector.Data.Vector.Basic.«term_::ᵥ_» `tt " ::ᵥ " `nil)))])
        []))
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValEqns', expected 'Lean.Parser.Command.declValSimple'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Bitvec.Data.Bitvec.Core.«term_++ₜ_»
       (Term.app `repeat [`false `n])
       "++ₜ"
       (Vector.Data.Vector.Basic.«term_::ᵥ_» `tt " ::ᵥ " `nil))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Bitvec.Data.Bitvec.Core.«term_++ₜ_»', expected 'Bitvec.Data.Bitvec.Core.term_++ₜ_._@.Data.Bitvec.Core._hyg.10'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValEqns', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/-- Create a bitvector of length `n` whose `n-1`st entry is 1 and other entries are 0. -/
    @[ reducible ]
    protected
  def one : ∀ n : ℕ , Bitvec n | 0 => nil | succ n => repeat false n ++ₜ tt ::ᵥ nil
#align bitvec.one Bitvec.one

/-- Create a bitvector from another with a provably equal length. -/
protected def cong {a b : ℕ} (h : a = b) : Bitvec a → Bitvec b
  | ⟨x, p⟩ => ⟨x, h ▸ p⟩
#align bitvec.cong Bitvec.cong

/-- `bitvec` specific version of `vector.append` -/
def append {m n} : Bitvec m → Bitvec n → Bitvec (m + n) :=
  Vector.append
#align bitvec.append Bitvec.append

/-! ### Shift operations -/


section Shift

variable {n : ℕ}

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "`shl x i` is the bitvector obtained by left-shifting `x` `i` times and padding with `ff`.\nIf `x.length < i` then this will return the all-`ff`s bitvector. -/")]
      []
      []
      []
      []
      [])
     (Command.def
      "def"
      (Command.declId `shl [])
      (Command.optDeclSig
       [(Term.explicitBinder "(" [`x] [":" (Term.app `Bitvec [`n])] [] ")")
        (Term.explicitBinder "(" [`i] [":" (termℕ "ℕ")] [] ")")]
       [(Term.typeSpec ":" (Term.app `Bitvec [`n]))])
      (Command.declValSimple
       ":="
       («term_<|_»
        (Term.app
         `Bitvec.cong
         [(Term.byTactic
           "by"
           (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])])))])
        "<|"
        (Bitvec.Data.Bitvec.Core.«term_++ₜ_»
         (Term.app `drop [`i `x])
         "++ₜ"
         (Term.app `repeat [`false (Term.app `min [`n `i])])))
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_»
       (Term.app
        `Bitvec.cong
        [(Term.byTactic
          "by"
          (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])])))])
       "<|"
       (Bitvec.Data.Bitvec.Core.«term_++ₜ_»
        (Term.app `drop [`i `x])
        "++ₜ"
        (Term.app `repeat [`false (Term.app `min [`n `i])])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Bitvec.Data.Bitvec.Core.«term_++ₜ_»
       (Term.app `drop [`i `x])
       "++ₜ"
       (Term.app `repeat [`false (Term.app `min [`n `i])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Bitvec.Data.Bitvec.Core.«term_++ₜ_»', expected 'Bitvec.Data.Bitvec.Core.term_++ₜ_._@.Data.Bitvec.Core._hyg.10'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    `shl x i` is the bitvector obtained by left-shifting `x` `i` times and padding with `ff`.
    If `x.length < i` then this will return the all-`ff`s bitvector. -/
  def
    shl
    ( x : Bitvec n ) ( i : ℕ ) : Bitvec n
    := Bitvec.cong by simp <| drop i x ++ₜ repeat false min n i
#align bitvec.shl Bitvec.shl

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "`fill_shr x i fill` is the bitvector obtained by right-shifting `x` `i` times and then\npadding with `fill : bool`. If `x.length < i` then this will return the constant `fill`\nbitvector. -/")]
      []
      []
      []
      []
      [])
     (Command.def
      "def"
      (Command.declId `fillShr [])
      (Command.optDeclSig
       [(Term.explicitBinder "(" [`x] [":" (Term.app `Bitvec [`n])] [] ")")
        (Term.explicitBinder "(" [`i] [":" (termℕ "ℕ")] [] ")")
        (Term.explicitBinder "(" [`fill] [":" `Bool] [] ")")]
       [(Term.typeSpec ":" (Term.app `Bitvec [`n]))])
      (Command.declValSimple
       ":="
       («term_<|_»
        (Term.app
         `Bitvec.cong
         [(Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(Classical.«tacticBy_cases_:_» "by_cases" [] («term_≤_» `i "≤" `n))
              []
              (tactic__
               (cdotTk (patternIgnore (token.«· » "·")))
               [(Tactic.tacticHave_
                 "have"
                 (Term.haveDecl (Term.haveIdDecl [`h₁ []] [] ":=" (Term.app `Nat.sub_le [`n `i]))))
                []
                (Tactic.rwSeq
                 "rw"
                 []
                 (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `min_eq_right [`h]))] "]")
                 [])
                []
                (Tactic.rwSeq
                 "rw"
                 []
                 (Tactic.rwRuleSeq
                  "["
                  [(Tactic.rwRule [] (Term.app `min_eq_left [`h₁]))
                   ","
                   (Tactic.rwRule
                    [(patternIgnore (token.«← » "←"))]
                    (Term.app `add_tsub_assoc_of_le [`h]))
                   ","
                   (Tactic.rwRule [] `Nat.add_comm)
                   ","
                   (Tactic.rwRule [] `add_tsub_cancel_right)]
                  "]")
                 [])])
              []
              (tactic__
               (cdotTk (patternIgnore (token.«· » "·")))
               [(Tactic.tacticHave_
                 "have"
                 (Term.haveDecl (Term.haveIdDecl [`h₁ []] [] ":=" (Term.app `le_of_not_ge [`h]))))
                []
                (Tactic.rwSeq
                 "rw"
                 []
                 (Tactic.rwRuleSeq
                  "["
                  [(Tactic.rwRule [] (Term.app `min_eq_left [`h₁]))
                   ","
                   (Tactic.rwRule [] (Term.app `tsub_eq_zero_iff_le.mpr [`h₁]))
                   ","
                   (Tactic.rwRule [] `zero_min)
                   ","
                   (Tactic.rwRule [] `Nat.add_zero)]
                  "]")
                 [])])])))])
        "<|"
        (Bitvec.Data.Bitvec.Core.«term_++ₜ_»
         (Term.app `repeat [`fill (Term.app `min [`n `i])])
         "++ₜ"
         (Term.app `take [(«term_-_» `n "-" `i) `x])))
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_»
       (Term.app
        `Bitvec.cong
        [(Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Classical.«tacticBy_cases_:_» "by_cases" [] («term_≤_» `i "≤" `n))
             []
             (tactic__
              (cdotTk (patternIgnore (token.«· » "·")))
              [(Tactic.tacticHave_
                "have"
                (Term.haveDecl (Term.haveIdDecl [`h₁ []] [] ":=" (Term.app `Nat.sub_le [`n `i]))))
               []
               (Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `min_eq_right [`h]))] "]")
                [])
               []
               (Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule [] (Term.app `min_eq_left [`h₁]))
                  ","
                  (Tactic.rwRule
                   [(patternIgnore (token.«← » "←"))]
                   (Term.app `add_tsub_assoc_of_le [`h]))
                  ","
                  (Tactic.rwRule [] `Nat.add_comm)
                  ","
                  (Tactic.rwRule [] `add_tsub_cancel_right)]
                 "]")
                [])])
             []
             (tactic__
              (cdotTk (patternIgnore (token.«· » "·")))
              [(Tactic.tacticHave_
                "have"
                (Term.haveDecl (Term.haveIdDecl [`h₁ []] [] ":=" (Term.app `le_of_not_ge [`h]))))
               []
               (Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule [] (Term.app `min_eq_left [`h₁]))
                  ","
                  (Tactic.rwRule [] (Term.app `tsub_eq_zero_iff_le.mpr [`h₁]))
                  ","
                  (Tactic.rwRule [] `zero_min)
                  ","
                  (Tactic.rwRule [] `Nat.add_zero)]
                 "]")
                [])])])))])
       "<|"
       (Bitvec.Data.Bitvec.Core.«term_++ₜ_»
        (Term.app `repeat [`fill (Term.app `min [`n `i])])
        "++ₜ"
        (Term.app `take [(«term_-_» `n "-" `i) `x])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Bitvec.Data.Bitvec.Core.«term_++ₜ_»
       (Term.app `repeat [`fill (Term.app `min [`n `i])])
       "++ₜ"
       (Term.app `take [(«term_-_» `n "-" `i) `x]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Bitvec.Data.Bitvec.Core.«term_++ₜ_»', expected 'Bitvec.Data.Bitvec.Core.term_++ₜ_._@.Data.Bitvec.Core._hyg.10'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    `fill_shr x i fill` is the bitvector obtained by right-shifting `x` `i` times and then
    padding with `fill : bool`. If `x.length < i` then this will return the constant `fill`
    bitvector. -/
  def
    fillShr
    ( x : Bitvec n ) ( i : ℕ ) ( fill : Bool ) : Bitvec n
    :=
      Bitvec.cong
          by
            by_cases i ≤ n
              ·
                have h₁ := Nat.sub_le n i
                  rw [ min_eq_right h ]
                  rw
                    [
                      min_eq_left h₁
                        ,
                        ← add_tsub_assoc_of_le h
                        ,
                        Nat.add_comm
                        ,
                        add_tsub_cancel_right
                      ]
              ·
                have h₁ := le_of_not_ge h
                  rw [ min_eq_left h₁ , tsub_eq_zero_iff_le.mpr h₁ , zero_min , Nat.add_zero ]
        <|
        repeat fill min n i ++ₜ take n - i x
#align bitvec.fill_shr Bitvec.fillShr

/-- unsigned shift right -/
def ushr (x : Bitvec n) (i : ℕ) : Bitvec n :=
  fillShr x i false
#align bitvec.ushr Bitvec.ushr

/-- signed shift right -/
def sshr : ∀ {m : ℕ}, Bitvec m → ℕ → Bitvec m
  | 0, _, _ => nil
  | succ m, x, i => head x ::ᵥ fillShr (tail x) i (head x)
#align bitvec.sshr Bitvec.sshr

end Shift

/-! ### Bitwise operations -/


section Bitwise

variable {n : ℕ}

/-- bitwise not -/
def not : Bitvec n → Bitvec n :=
  map not
#align bitvec.not Bitvec.not

/-- bitwise and -/
def and : Bitvec n → Bitvec n → Bitvec n :=
  map₂ and
#align bitvec.and Bitvec.and

/-- bitwise or -/
def or : Bitvec n → Bitvec n → Bitvec n :=
  map₂ or
#align bitvec.or Bitvec.or

/-- bitwise xor -/
def xor : Bitvec n → Bitvec n → Bitvec n :=
  map₂ xor
#align bitvec.xor Bitvec.xor

end Bitwise

/-! ### Arithmetic operators -/


section Arith

variable {n : ℕ}

/-- `xor3 x y c` is `((x XOR y) XOR c)`. -/
protected def xor3 (x y c : Bool) :=
  xor (xor x y) c
#align bitvec.xor3 Bitvec.xor3

/-- `carry x y c` is `x && y || x && c || y && c`. -/
protected def carry (x y c : Bool) :=
  x && y || x && c || y && c
#align bitvec.carry Bitvec.carry

/-- `neg x` is the two's complement of `x`. -/
protected def neg (x : Bitvec n) : Bitvec n :=
  let f y c := (y || c, xor y c)
  Prod.snd (mapAccumr f x false)
#align bitvec.neg Bitvec.neg

/-- Add with carry (no overflow) -/
def adc (x y : Bitvec n) (c : Bool) : Bitvec (n + 1) :=
  let f x y c := (Bitvec.carry x y c, Bitvec.xor3 x y c)
  let ⟨c, z⟩ := Vector.mapAccumr₂ f x y c
  c ::ᵥ z
#align bitvec.adc Bitvec.adc

/-- The sum of two bitvectors -/
protected def add (x y : Bitvec n) : Bitvec n :=
  tail (adc x y false)
#align bitvec.add Bitvec.add

/-- Subtract with borrow -/
def sbb (x y : Bitvec n) (b : Bool) : Bool × Bitvec n :=
  let f x y c := (Bitvec.carry (not x) y c, Bitvec.xor3 x y c)
  Vector.mapAccumr₂ f x y b
#align bitvec.sbb Bitvec.sbb

/-- The difference of two bitvectors -/
protected def sub (x y : Bitvec n) : Bitvec n :=
  Prod.snd (sbb x y false)
#align bitvec.sub Bitvec.sub

instance : Zero (Bitvec n) :=
  ⟨Bitvec.zero n⟩

instance : One (Bitvec n) :=
  ⟨Bitvec.one n⟩

instance : Add (Bitvec n) :=
  ⟨Bitvec.add⟩

instance : Sub (Bitvec n) :=
  ⟨Bitvec.sub⟩

instance : Neg (Bitvec n) :=
  ⟨Bitvec.neg⟩

/-- The product of two bitvectors -/
protected def mul (x y : Bitvec n) : Bitvec n :=
  let f r b := cond b (r + r + y) (r + r)
  (toList x).foldl f 0
#align bitvec.mul Bitvec.mul

instance : Mul (Bitvec n) :=
  ⟨Bitvec.mul⟩

end Arith

/-! ### Comparison operators -/


section Comparison

variable {n : ℕ}

/-- `uborrow x y` returns `tt` iff the "subtract with borrow" operation on `x`, `y` and `ff`
required a borrow. -/
def uborrow (x y : Bitvec n) : Bool :=
  Prod.fst (sbb x y false)
#align bitvec.uborrow Bitvec.uborrow

/-- unsigned less-than proposition -/
def Ult (x y : Bitvec n) : Prop :=
  uborrow x y
#align bitvec.ult Bitvec.Ult

/-- unsigned greater-than proposition -/
def Ugt (x y : Bitvec n) : Prop :=
  Ult y x
#align bitvec.ugt Bitvec.Ugt

/-- unsigned less-than-or-equal-to proposition -/
def Ule (x y : Bitvec n) : Prop :=
  ¬Ult y x
#align bitvec.ule Bitvec.Ule

/-- unsigned greater-than-or-equal-to proposition -/
def Uge (x y : Bitvec n) : Prop :=
  Ule y x
#align bitvec.uge Bitvec.Uge

/-- `sborrow x y` returns `tt` iff `x < y` as two's complement integers -/
def sborrow : ∀ {n : ℕ}, Bitvec n → Bitvec n → Bool
  | 0, _, _ => false
  | succ n, x, y =>
    match (head x, head y) with
    | (tt, ff) => true
    | (ff, tt) => false
    | _ => uborrow (tail x) (tail y)
#align bitvec.sborrow Bitvec.sborrow

/-- signed less-than proposition -/
def Slt (x y : Bitvec n) : Prop :=
  sborrow x y
#align bitvec.slt Bitvec.Slt

/-- signed greater-than proposition -/
def Sgt (x y : Bitvec n) : Prop :=
  Slt y x
#align bitvec.sgt Bitvec.Sgt

/-- signed less-than-or-equal-to proposition -/
def Sle (x y : Bitvec n) : Prop :=
  ¬Slt y x
#align bitvec.sle Bitvec.Sle

/-- signed greater-than-or-equal-to proposition -/
def Sge (x y : Bitvec n) : Prop :=
  Sle y x
#align bitvec.sge Bitvec.Sge

end Comparison

/-! ### Conversion to `nat` and `int` -/


section Conversion

variable {α : Type}

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment "/--" "Create a bitvector from a `nat` -/")]
      []
      [(Command.protected "protected")]
      []
      []
      [])
     (Command.def
      "def"
      (Command.declId `ofNat [])
      (Command.optDeclSig
       []
       [(Term.typeSpec
         ":"
         (Term.forall
          "∀"
          [`n]
          [(Term.typeSpec ":" (termℕ "ℕ"))]
          ","
          (Term.arrow `Nat "→" (Term.app `Bitvec [`n]))))])
      (Command.declValEqns
       (Term.matchAltsWhereDecls
        (Term.matchAlts
         [(Term.matchAlt "|" [[(num "0") "," `x]] "=>" `nil)
          (Term.matchAlt
           "|"
           [[(Term.app `succ [`n]) "," `x]]
           "=>"
           (Bitvec.Data.Bitvec.Core.«term_++ₜ_»
            (Term.app `of_nat [`n («term_/_» `x "/" (num "2"))])
            "++ₜ"
            (Vector.Data.Vector.Basic.«term_::ᵥ_»
             (Term.app `decide [(«term_=_» («term_%_» `x "%" (num "2")) "=" (num "1"))])
             " ::ᵥ "
             `nil)))])
        []))
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValEqns', expected 'Lean.Parser.Command.declValSimple'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Bitvec.Data.Bitvec.Core.«term_++ₜ_»
       (Term.app `of_nat [`n («term_/_» `x "/" (num "2"))])
       "++ₜ"
       (Vector.Data.Vector.Basic.«term_::ᵥ_»
        (Term.app `decide [(«term_=_» («term_%_» `x "%" (num "2")) "=" (num "1"))])
        " ::ᵥ "
        `nil))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Bitvec.Data.Bitvec.Core.«term_++ₜ_»', expected 'Bitvec.Data.Bitvec.Core.term_++ₜ_._@.Data.Bitvec.Core._hyg.10'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValEqns', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/-- Create a bitvector from a `nat` -/ protected
  def
    ofNat
    : ∀ n : ℕ , Nat → Bitvec n
    | 0 , x => nil | succ n , x => of_nat n x / 2 ++ₜ decide x % 2 = 1 ::ᵥ nil
#align bitvec.of_nat Bitvec.ofNat

/-- Create a bitvector in the two's complement representation from an `int` -/
protected def ofInt : ∀ n : ℕ, Int → Bitvec (succ n)
  | n, Int.ofNat m => ff ::ᵥ Bitvec.ofNat n m
  | n, Int.negSucc m => tt ::ᵥ not (Bitvec.ofNat n m)
#align bitvec.of_int Bitvec.ofInt

/-- `add_lsb r b` is `r + r + 1` if `b` is `tt` and `r + r` otherwise. -/
def addLsb (r : ℕ) (b : Bool) :=
  r + r + cond b 1 0
#align bitvec.add_lsb Bitvec.addLsb

/-- Given a `list` of `bool`s, return the `nat` they represent as a list of binary digits. -/
def bitsToNat (v : List Bool) : Nat :=
  v.foldl addLsb 0
#align bitvec.bits_to_nat Bitvec.bitsToNat

/-- Return the natural number encoded by the input bitvector -/
protected def toNat {n : Nat} (v : Bitvec n) : Nat :=
  bitsToNat (toList v)
#align bitvec.to_nat Bitvec.toNat

theorem bits_to_nat_to_list {n : ℕ} (x : Bitvec n) : Bitvec.toNat x = bitsToNat (Vector.toList x) :=
  rfl
#align bitvec.bits_to_nat_to_list Bitvec.bits_to_nat_to_list

attribute [local simp] Nat.add_comm Nat.add_assoc Nat.add_left_comm Nat.mul_comm Nat.mul_assoc

attribute [local simp] Nat.zero_add Nat.add_zero Nat.one_mul Nat.mul_one Nat.zero_mul Nat.mul_zero

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `to_nat_append [])
      (Command.declSig
       [(Term.implicitBinder "{" [`m] [":" (termℕ "ℕ")] "}")
        (Term.explicitBinder "(" [`xs] [":" (Term.app `Bitvec [`m])] [] ")")
        (Term.explicitBinder "(" [`b] [":" `Bool] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app
          `Bitvec.toNat
          [(Bitvec.Data.Bitvec.Core.«term_++ₜ_»
            `xs
            "++ₜ"
            (Vector.Data.Vector.Basic.«term_::ᵥ_» `b " ::ᵥ " `nil))])
         "="
         («term_+_»
          («term_*_» (Term.app `Bitvec.toNat [`xs]) "*" (num "2"))
          "+"
          (Term.app `Bitvec.toNat [(Vector.Data.Vector.Basic.«term_::ᵥ_» `b " ::ᵥ " `nil)])))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.cases'
            "cases'"
            [(Tactic.casesTarget [] `xs)]
            []
            ["with" [(Lean.binderIdent `xs) (Lean.binderIdent `P)]])
           []
           (Tactic.simp
            "simp"
            []
            []
            []
            ["[" [(Tactic.simpLemma [] [] `bits_to_nat_to_list)] "]"]
            [])
           ";"
           (Tactic.clear "clear" [`P])
           []
           (Tactic.unfold "unfold" [`bits_to_nat `List.foldl] [])
           []
           (Tactic.generalize "generalize" [(Tactic.generalizeArg [`h ":"] (num "0") "=" `x)] [])
           ";"
           (Tactic.Conv.conv
            "conv"
            []
            ["in" [] (Term.app `add_lsb [`x `b])]
            "=>"
            (Tactic.Conv.convSeq
             (Tactic.Conv.convSeq1Indented
              [(Tactic.Conv.convRw__
                "rw"
                []
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `h)]
                 "]"))])))
           ";"
           (Tactic.clear "clear" [`h])
           []
           (Tactic.simp "simp" [] [] [] [] [])
           []
           (Tactic.induction'
            "induction'"
            [(Tactic.casesTarget [] `xs)]
            []
            ["with" [(Lean.binderIdent `x) (Lean.binderIdent `xs)]]
            ["generalizing" [`x]])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.simp "simp" [] [] [] [] [])
             []
             (Tactic.unfold "unfold" [`List.foldl `add_lsb] [])
             []
             (Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `Nat.mul_succ)] "]"] [])])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.simp "simp" [] [] [] [] []) [] (Tactic.apply "apply" `xs_ih)])])))
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
         [(Tactic.cases'
           "cases'"
           [(Tactic.casesTarget [] `xs)]
           []
           ["with" [(Lean.binderIdent `xs) (Lean.binderIdent `P)]])
          []
          (Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `bits_to_nat_to_list)] "]"] [])
          ";"
          (Tactic.clear "clear" [`P])
          []
          (Tactic.unfold "unfold" [`bits_to_nat `List.foldl] [])
          []
          (Tactic.generalize "generalize" [(Tactic.generalizeArg [`h ":"] (num "0") "=" `x)] [])
          ";"
          (Tactic.Conv.conv
           "conv"
           []
           ["in" [] (Term.app `add_lsb [`x `b])]
           "=>"
           (Tactic.Conv.convSeq
            (Tactic.Conv.convSeq1Indented
             [(Tactic.Conv.convRw__
               "rw"
               []
               (Tactic.rwRuleSeq
                "["
                [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `h)]
                "]"))])))
          ";"
          (Tactic.clear "clear" [`h])
          []
          (Tactic.simp "simp" [] [] [] [] [])
          []
          (Tactic.induction'
           "induction'"
           [(Tactic.casesTarget [] `xs)]
           []
           ["with" [(Lean.binderIdent `x) (Lean.binderIdent `xs)]]
           ["generalizing" [`x]])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.simp "simp" [] [] [] [] [])
            []
            (Tactic.unfold "unfold" [`List.foldl `add_lsb] [])
            []
            (Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `Nat.mul_succ)] "]"] [])])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.simp "simp" [] [] [] [] []) [] (Tactic.apply "apply" `xs_ih)])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.simp "simp" [] [] [] [] []) [] (Tactic.apply "apply" `xs_ih)])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.apply "apply" `xs_ih)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `xs_ih
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] [] [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.simp "simp" [] [] [] [] [])
        []
        (Tactic.unfold "unfold" [`List.foldl `add_lsb] [])
        []
        (Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `Nat.mul_succ)] "]"] [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `Nat.mul_succ)] "]"] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Nat.mul_succ
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.unfold "unfold" [`List.foldl `add_lsb] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] [] [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.induction'
       "induction'"
       [(Tactic.casesTarget [] `xs)]
       []
       ["with" [(Lean.binderIdent `x) (Lean.binderIdent `xs)]]
       ["generalizing" [`x]])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `xs
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] [] [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.clear "clear" [`h])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.Conv.conv
       "conv"
       []
       ["in" [] (Term.app `add_lsb [`x `b])]
       "=>"
       (Tactic.Conv.convSeq
        (Tactic.Conv.convSeq1Indented
         [(Tactic.Conv.convRw__
           "rw"
           []
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `h)] "]"))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.Conv.convSeq1Indented', expected 'Lean.Parser.Tactic.Conv.convSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `add_lsb [`x `b])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `b
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `add_lsb
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.generalize "generalize" [(Tactic.generalizeArg [`h ":"] (num "0") "=" `x)] [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.unfold "unfold" [`bits_to_nat `List.foldl] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.clear "clear" [`P])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `P
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `bits_to_nat_to_list)] "]"] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `bits_to_nat_to_list
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.cases'
       "cases'"
       [(Tactic.casesTarget [] `xs)]
       []
       ["with" [(Lean.binderIdent `xs) (Lean.binderIdent `P)]])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `xs
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app
        `Bitvec.toNat
        [(Bitvec.Data.Bitvec.Core.«term_++ₜ_»
          `xs
          "++ₜ"
          (Vector.Data.Vector.Basic.«term_::ᵥ_» `b " ::ᵥ " `nil))])
       "="
       («term_+_»
        («term_*_» (Term.app `Bitvec.toNat [`xs]) "*" (num "2"))
        "+"
        (Term.app `Bitvec.toNat [(Vector.Data.Vector.Basic.«term_::ᵥ_» `b " ::ᵥ " `nil)])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_»
       («term_*_» (Term.app `Bitvec.toNat [`xs]) "*" (num "2"))
       "+"
       (Term.app `Bitvec.toNat [(Vector.Data.Vector.Basic.«term_::ᵥ_» `b " ::ᵥ " `nil)]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Bitvec.toNat [(Vector.Data.Vector.Basic.«term_::ᵥ_» `b " ::ᵥ " `nil)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Vector.Data.Vector.Basic.«term_::ᵥ_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Vector.Data.Vector.Basic.«term_::ᵥ_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Vector.Data.Vector.Basic.«term_::ᵥ_» `b " ::ᵥ " `nil)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `nil
[PrettyPrinter.parenthesize] ...precedences are 67 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 67, term))
      `b
[PrettyPrinter.parenthesize] ...precedences are 68 >? 1024, (none, [anonymous]) <=? (some 67, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 67, (some 67, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Vector.Data.Vector.Basic.«term_::ᵥ_» `b " ::ᵥ " `nil)
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Bitvec.toNat
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      («term_*_» (Term.app `Bitvec.toNat [`xs]) "*" (num "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (Term.app `Bitvec.toNat [`xs])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `xs
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Bitvec.toNat
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1022, (some 1023, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 65 >? 70, (some 71, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app
       `Bitvec.toNat
       [(Bitvec.Data.Bitvec.Core.«term_++ₜ_»
         `xs
         "++ₜ"
         (Vector.Data.Vector.Basic.«term_::ᵥ_» `b " ::ᵥ " `nil))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Bitvec.Data.Bitvec.Core.«term_++ₜ_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Bitvec.Data.Bitvec.Core.«term_++ₜ_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Bitvec.Data.Bitvec.Core.«term_++ₜ_»
       `xs
       "++ₜ"
       (Vector.Data.Vector.Basic.«term_::ᵥ_» `b " ::ᵥ " `nil))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Bitvec.Data.Bitvec.Core.«term_++ₜ_»', expected 'Bitvec.Data.Bitvec.Core.term_++ₜ_._@.Data.Bitvec.Core._hyg.10'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  to_nat_append
  { m : ℕ } ( xs : Bitvec m ) ( b : Bool )
    : Bitvec.toNat xs ++ₜ b ::ᵥ nil = Bitvec.toNat xs * 2 + Bitvec.toNat b ::ᵥ nil
  :=
    by
      cases' xs with xs P
        simp [ bits_to_nat_to_list ]
        ;
        clear P
        unfold bits_to_nat List.foldl
        generalize h : 0 = x
        ;
        conv in add_lsb x b => rw [ ← h ]
        ;
        clear h
        simp
        induction' xs with x xs generalizing x
        · simp unfold List.foldl add_lsb simp [ Nat.mul_succ ]
        · simp apply xs_ih
#align bitvec.to_nat_append Bitvec.to_nat_append

theorem bits_to_nat_to_bool (n : ℕ) : Bitvec.toNat (decide (n % 2 = 1) ::ᵥ nil) = n % 2 :=
  by
  simp [bits_to_nat_to_list]
  unfold bits_to_nat add_lsb List.foldl cond
  simp [cond_to_bool_mod_two]
#align bitvec.bits_to_nat_to_bool Bitvec.bits_to_nat_to_bool

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `of_nat_succ [])
      (Command.declSig
       [(Term.implicitBinder "{" [`k `n] [":" (termℕ "ℕ")] "}")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app `Bitvec.ofNat [(Term.app `succ [`k]) `n])
         "="
         (Bitvec.Data.Bitvec.Core.«term_++ₜ_»
          (Term.app `Bitvec.ofNat [`k («term_/_» `n "/" (num "2"))])
          "++ₜ"
          (Vector.Data.Vector.Basic.«term_::ᵥ_»
           (Term.app `decide [(«term_=_» («term_%_» `n "%" (num "2")) "=" (num "1"))])
           " ::ᵥ "
           `nil)))))
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
       (Term.app `Bitvec.ofNat [(Term.app `succ [`k]) `n])
       "="
       (Bitvec.Data.Bitvec.Core.«term_++ₜ_»
        (Term.app `Bitvec.ofNat [`k («term_/_» `n "/" (num "2"))])
        "++ₜ"
        (Vector.Data.Vector.Basic.«term_::ᵥ_»
         (Term.app `decide [(«term_=_» («term_%_» `n "%" (num "2")) "=" (num "1"))])
         " ::ᵥ "
         `nil)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Bitvec.Data.Bitvec.Core.«term_++ₜ_»
       (Term.app `Bitvec.ofNat [`k («term_/_» `n "/" (num "2"))])
       "++ₜ"
       (Vector.Data.Vector.Basic.«term_::ᵥ_»
        (Term.app `decide [(«term_=_» («term_%_» `n "%" (num "2")) "=" (num "1"))])
        " ::ᵥ "
        `nil))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Bitvec.Data.Bitvec.Core.«term_++ₜ_»', expected 'Bitvec.Data.Bitvec.Core.term_++ₜ_._@.Data.Bitvec.Core._hyg.10'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  of_nat_succ
  { k n : ℕ } : Bitvec.ofNat succ k n = Bitvec.ofNat k n / 2 ++ₜ decide n % 2 = 1 ::ᵥ nil
  := rfl
#align bitvec.of_nat_succ Bitvec.of_nat_succ

theorem to_nat_of_nat {k n : ℕ} : Bitvec.toNat (Bitvec.ofNat k n) = n % 2 ^ k :=
  by
  induction' k with k ih generalizing n
  · simp [Nat.mod_one]
    rfl
  · rw [of_nat_succ, to_nat_append, ih, bits_to_nat_to_bool, mod_pow_succ, Nat.mul_comm]
#align bitvec.to_nat_of_nat Bitvec.to_nat_of_nat

/-- Return the integer encoded by the input bitvector -/
protected def toInt : ∀ {n : Nat}, Bitvec n → Int
  | 0, _ => 0
  | succ n, v =>
    cond (head v) (Int.negSucc <| Bitvec.toNat <| Not <| tail v)
      (Int.ofNat <| Bitvec.toNat <| tail v)
#align bitvec.to_int Bitvec.toInt

end Conversion

/-! ### Miscellaneous instances -/


private def repr {n : Nat} : Bitvec n → String
  | ⟨bs, p⟩ => "0b" ++ (bs.map fun b : Bool => if b then '1' else '0').asString
#align bitvec.repr bitvec.repr

instance (n : Nat) : Repr (Bitvec n) :=
  ⟨repr⟩

end Bitvec

instance {n} {x y : Bitvec n} : Decidable (Bitvec.Ult x y) :=
  Bool.decidableEq _ _

instance {n} {x y : Bitvec n} : Decidable (Bitvec.Ugt x y) :=
  Bool.decidableEq _ _

