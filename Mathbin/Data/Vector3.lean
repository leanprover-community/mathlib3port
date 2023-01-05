/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

! This file was ported from Lean 3 source module data.vector3
! leanprover-community/mathlib commit 6d0adfa76594f304b4650d098273d4366edeb61b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Fin.Fin2
import Mathbin.Tactic.Localized

/-!
# Alternate definition of `vector` in terms of `fin2`

This file provides a locale `vector3` which overrides the `[a, b, c]` notation to create a `vector3`
instead of a `list`.

The `::` notation is also overloaded by this file to mean `vector3.cons`.
-/


open Fin2 Nat

universe u

variable {α : Type _} {m n : ℕ}

/-- Alternate definition of `vector` based on `fin2`. -/
def Vector3 (α : Type u) (n : ℕ) : Type u :=
  Fin2 n → α
#align vector3 Vector3

instance [Inhabited α] : Inhabited (Vector3 α n) :=
  Pi.inhabited _

namespace Vector3

/-- The empty vector -/
@[match_pattern]
def nil : Vector3 α 0 :=
  fun.
#align vector3.nil Vector3.nil

/-- The vector cons operation -/
@[match_pattern]
def cons (a : α) (v : Vector3 α n) : Vector3 α (succ n) := fun i =>
  by
  refine' i.cases' _ _
  exact a
  exact v
#align vector3.cons Vector3.cons

-- mathport name: vector.list
/- We do not want to make the following notation global, because then these expressions will be
overloaded, and only the expected type will be able to disambiguate the meaning. Worse: Lean will
try to insert a coercion from `vector3 α _` to `list α`, if a list is expected. -/
scoped notation3"["(l", "* => foldr (h t => Vector3.cons h t) Vector3.nil)"]" => l

-- mathport name: vector.cons
notation a "::" b => cons a b

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem cons_fz (a : α) (v : Vector3 α n) : (a::v) fz = a :=
  rfl
#align vector3.cons_fz Vector3.cons_fz

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem cons_fs (a : α) (v : Vector3 α n) (i) : (a::v) (fs i) = v i :=
  rfl
#align vector3.cons_fs Vector3.cons_fs

/-- Get the `i`th element of a vector -/
@[reducible]
def nth (i : Fin2 n) (v : Vector3 α n) : α :=
  v i
#align vector3.nth Vector3.nth

/-- Construct a vector from a function on `fin2`. -/
@[reducible]
def ofFn (f : Fin2 n → α) : Vector3 α n :=
  f
#align vector3.of_fn Vector3.ofFn

/-- Get the head of a nonempty vector. -/
def head (v : Vector3 α (succ n)) : α :=
  v fz
#align vector3.head Vector3.head

/-- Get the tail of a nonempty vector. -/
def tail (v : Vector3 α (succ n)) : Vector3 α n := fun i => v (fs i)
#align vector3.tail Vector3.tail

theorem eq_nil (v : Vector3 α 0) : v = [] :=
  funext fun i => nomatch i
#align vector3.eq_nil Vector3.eq_nil

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem cons_head_tail (v : Vector3 α (succ n)) : (head v::tail v) = v :=
  funext fun i => Fin2.cases' rfl (fun _ => rfl) i
#align vector3.cons_head_tail Vector3.cons_head_tail

/-- Eliminator for an empty vector. -/
def nilElim {C : Vector3 α 0 → Sort u} (H : C []) (v : Vector3 α 0) : C v := by
  rw [eq_nil v] <;> apply H
#align vector3.nil_elim Vector3.nilElim

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- Recursion principle for a nonempty vector. -/
def consElim {C : Vector3 α (succ n) → Sort u} (H : ∀ (a : α) (t : Vector3 α n), C (a::t))
    (v : Vector3 α (succ n)) : C v := by rw [← cons_head_tail v] <;> apply H
#align vector3.cons_elim Vector3.consElim

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem cons_elim_cons {C H a t} : @consElim α n C H (a::t) = H a t :=
  rfl
#align vector3.cons_elim_cons Vector3.cons_elim_cons

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- Recursion principle with the vector as first argument. -/
@[elab_as_elim]
protected def recOn {C : ∀ {n}, Vector3 α n → Sort u} {n} (v : Vector3 α n) (H0 : C [])
    (Hs : ∀ {n} (a) (w : Vector3 α n), C w → C (a::w)) : C v :=
  Nat.recOn n (fun v => v.nilElim H0) (fun n IH v => v.consElim fun a t => Hs _ _ (IH _)) v
#align vector3.rec_on Vector3.recOn

@[simp]
theorem rec_on_nil {C H0 Hs} : @Vector3.recOn α (@C) 0 [] H0 @Hs = H0 :=
  rfl
#align vector3.rec_on_nil Vector3.rec_on_nil

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem rec_on_cons {C H0 Hs n a v} :
    @Vector3.recOn α (@C) (succ n) (a::v) H0 @Hs = Hs a v (@Vector3.recOn α (@C) n v H0 @Hs) :=
  rfl
#align vector3.rec_on_cons Vector3.rec_on_cons

/-- Append two vectors -/
def append (v : Vector3 α m) (w : Vector3 α n) : Vector3 α (n + m) :=
  Nat.recOn m (fun _ => w)
    (fun m IH v => v.consElim fun a t => @Fin2.cases' (n + m) (fun _ => α) a (IH t)) v
#align vector3.append Vector3.append

-- mathport name: «expr +-+ »
local infixl:65 " +-+ " => Vector3.append

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
      (Command.declId `append_nil [])
      (Command.declSig
       [(Term.explicitBinder "(" [`w] [":" (Term.app `Vector3 [`α `n])] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Vector3.Data.Vector3.«term_+-+_» (Vector3.Data.Vector3.vector.list "[" [] "]") " +-+ " `w)
         "="
         `w)))
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
       (Vector3.Data.Vector3.«term_+-+_» (Vector3.Data.Vector3.vector.list "[" [] "]") " +-+ " `w)
       "="
       `w)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `w
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Vector3.Data.Vector3.«term_+-+_» (Vector3.Data.Vector3.vector.list "[" [] "]") " +-+ " `w)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Vector3.Data.Vector3.«term_+-+_»', expected 'Vector3.Data.Vector3.term_+-+_._@.Data.Vector3._hyg.966'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ simp ] theorem append_nil ( w : Vector3 α n ) : [ ] +-+ w = w := rfl
#align vector3.append_nil Vector3.append_nil

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
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
      (Command.declId `append_cons [])
      (Command.declSig
       [(Term.explicitBinder "(" [`a] [":" `α] [] ")")
        (Term.explicitBinder "(" [`v] [":" (Term.app `Vector3 [`α `m])] [] ")")
        (Term.explicitBinder "(" [`w] [":" (Term.app `Vector3 [`α `n])] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Vector3.Data.Vector3.«term_+-+_» (Vector3.Data.Vector3.vector.cons `a "::" `v) " +-+ " `w)
         "="
         (Vector3.Data.Vector3.vector.cons
          `a
          "::"
          (Vector3.Data.Vector3.«term_+-+_» `v " +-+ " `w)))))
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
       (Vector3.Data.Vector3.«term_+-+_» (Vector3.Data.Vector3.vector.cons `a "::" `v) " +-+ " `w)
       "="
       (Vector3.Data.Vector3.vector.cons `a "::" (Vector3.Data.Vector3.«term_+-+_» `v " +-+ " `w)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Vector3.Data.Vector3.vector.cons `a "::" (Vector3.Data.Vector3.«term_+-+_» `v " +-+ " `w))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Vector3.Data.Vector3.«term_+-+_» `v " +-+ " `w)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Vector3.Data.Vector3.«term_+-+_»', expected 'Vector3.Data.Vector3.term_+-+_._@.Data.Vector3._hyg.966'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ simp ]
  theorem
    append_cons
    ( a : α ) ( v : Vector3 α m ) ( w : Vector3 α n ) : a :: v +-+ w = a :: v +-+ w
    := rfl
#align vector3.append_cons Vector3.append_cons

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
      (Command.declId `append_left [])
      (Command.declSig
       []
       (Term.typeSpec
        ":"
        (Term.forall
         "∀"
         [(Term.implicitBinder "{" [`m] [] "}")
          (Term.explicitBinder "(" [`i] [":" (Term.app `Fin2 [`m])] [] ")")
          (Term.explicitBinder "(" [`v] [":" (Term.app `Vector3 [`α `m])] [] ")")
          (Term.implicitBinder "{" [`n] [] "}")
          (Term.explicitBinder "(" [`w] [":" (Term.app `Vector3 [`α `n])] [] ")")]
         []
         ","
         («term_=_»
          (Term.app (Vector3.Data.Vector3.«term_+-+_» `v " +-+ " `w) [(Term.app `left [`n `i])])
          "="
          (Term.app `v [`i])))))
      (Command.declValEqns
       (Term.matchAltsWhereDecls
        (Term.matchAlts
         [(Term.matchAlt
           "|"
           [[(Term.hole "_") "," (Term.app (Term.explicit "@" `fz) [`m]) "," `v "," `n "," `w]]
           "=>"
           (Term.app
            (Term.proj `v "." `consElim)
            [(Term.fun
              "fun"
              (Term.basicFun
               [`a `t]
               []
               "=>"
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(Tactic.simp
                    "simp"
                    []
                    []
                    []
                    ["[" [(Tactic.simpStar "*") "," (Tactic.simpLemma [] [] `left)] "]"]
                    [])])))))]))
          (Term.matchAlt
           "|"
           [[(Term.hole "_") "," (Term.app (Term.explicit "@" `fs) [`m `i]) "," `v "," `n "," `w]]
           "=>"
           (Term.app
            (Term.proj `v "." `consElim)
            [(Term.fun
              "fun"
              (Term.basicFun
               [`a `t]
               []
               "=>"
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(Tactic.simp
                    "simp"
                    []
                    []
                    []
                    ["[" [(Tactic.simpStar "*") "," (Tactic.simpLemma [] [] `left)] "]"]
                    [])])))))]))])
        []))
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValEqns', expected 'Lean.Parser.Command.declValSimple'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj `v "." `consElim)
       [(Term.fun
         "fun"
         (Term.basicFun
          [`a `t]
          []
          "=>"
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(Tactic.simp
               "simp"
               []
               []
               []
               ["[" [(Tactic.simpStar "*") "," (Tactic.simpLemma [] [] `left)] "]"]
               [])])))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`a `t]
        []
        "=>"
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Tactic.simp
             "simp"
             []
             []
             []
             ["[" [(Tactic.simpStar "*") "," (Tactic.simpLemma [] [] `left)] "]"]
             [])])))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.simp
           "simp"
           []
           []
           []
           ["[" [(Tactic.simpStar "*") "," (Tactic.simpLemma [] [] `left)] "]"]
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       []
       ["[" [(Tactic.simpStar "*") "," (Tactic.simpLemma [] [] `left)] "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `left
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `t
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `v "." `consElim)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `v
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `w
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `v
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.explicit "@" `fs) [`m `i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `m
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.explicit "@" `fs)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `fs
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (some 1024,
     term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app
       (Term.proj `v "." `consElim)
       [(Term.fun
         "fun"
         (Term.basicFun
          [`a `t]
          []
          "=>"
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(Tactic.simp
               "simp"
               []
               []
               []
               ["[" [(Tactic.simpStar "*") "," (Tactic.simpLemma [] [] `left)] "]"]
               [])])))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`a `t]
        []
        "=>"
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Tactic.simp
             "simp"
             []
             []
             []
             ["[" [(Tactic.simpStar "*") "," (Tactic.simpLemma [] [] `left)] "]"]
             [])])))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.simp
           "simp"
           []
           []
           []
           ["[" [(Tactic.simpStar "*") "," (Tactic.simpLemma [] [] `left)] "]"]
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       []
       ["[" [(Tactic.simpStar "*") "," (Tactic.simpLemma [] [] `left)] "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `left
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `t
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `v "." `consElim)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `v
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `w
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `v
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.explicit "@" `fz) [`m])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `m
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.explicit "@" `fz)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `fz
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (some 1024,
     term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.forall
       "∀"
       [(Term.implicitBinder "{" [`m] [] "}")
        (Term.explicitBinder "(" [`i] [":" (Term.app `Fin2 [`m])] [] ")")
        (Term.explicitBinder "(" [`v] [":" (Term.app `Vector3 [`α `m])] [] ")")
        (Term.implicitBinder "{" [`n] [] "}")
        (Term.explicitBinder "(" [`w] [":" (Term.app `Vector3 [`α `n])] [] ")")]
       []
       ","
       («term_=_»
        (Term.app (Vector3.Data.Vector3.«term_+-+_» `v " +-+ " `w) [(Term.app `left [`n `i])])
        "="
        (Term.app `v [`i])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Term.app (Vector3.Data.Vector3.«term_+-+_» `v " +-+ " `w) [(Term.app `left [`n `i])])
       "="
       (Term.app `v [`i]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `v [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `v
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app (Vector3.Data.Vector3.«term_+-+_» `v " +-+ " `w) [(Term.app `left [`n `i])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `left [`n `i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `left
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `left [`n `i]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Vector3.Data.Vector3.«term_+-+_» `v " +-+ " `w)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Vector3.Data.Vector3.«term_+-+_»', expected 'Vector3.Data.Vector3.term_+-+_._@.Data.Vector3._hyg.966'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ simp ]
  theorem
    append_left
    : ∀ { m } ( i : Fin2 m ) ( v : Vector3 α m ) { n } ( w : Vector3 α n ) , v +-+ w left n i = v i
    | _ , @ fz m , v , n , w => v . consElim fun a t => by simp [ * , left ]
      | _ , @ fs m i , v , n , w => v . consElim fun a t => by simp [ * , left ]
#align vector3.append_left Vector3.append_left

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
      (Command.declId `append_add [])
      (Command.declSig
       []
       (Term.typeSpec
        ":"
        (Term.forall
         "∀"
         [(Term.implicitBinder "{" [`m] [] "}")
          (Term.explicitBinder "(" [`v] [":" (Term.app `Vector3 [`α `m])] [] ")")
          (Term.implicitBinder "{" [`n] [] "}")
          (Term.explicitBinder "(" [`w] [":" (Term.app `Vector3 [`α `n])] [] ")")
          (Term.explicitBinder "(" [`i] [":" (Term.app `Fin2 [`n])] [] ")")]
         []
         ","
         («term_=_»
          (Term.app (Vector3.Data.Vector3.«term_+-+_» `v " +-+ " `w) [(Term.app `add [`i `m])])
          "="
          (Term.app `w [`i])))))
      (Command.declValEqns
       (Term.matchAltsWhereDecls
        (Term.matchAlts
         [(Term.matchAlt "|" [[(num "0") "," `v "," `n "," `w "," `i]] "=>" `rfl)
          (Term.matchAlt
           "|"
           [[(Term.app `succ [`m]) "," `v "," `n "," `w "," `i]]
           "=>"
           (Term.app
            (Term.proj `v "." `consElim)
            [(Term.fun
              "fun"
              (Term.basicFun
               [`a `t]
               []
               "=>"
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(Tactic.simp
                    "simp"
                    []
                    []
                    []
                    ["[" [(Tactic.simpStar "*") "," (Tactic.simpLemma [] [] `add)] "]"]
                    [])])))))]))])
        []))
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValEqns', expected 'Lean.Parser.Command.declValSimple'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj `v "." `consElim)
       [(Term.fun
         "fun"
         (Term.basicFun
          [`a `t]
          []
          "=>"
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(Tactic.simp
               "simp"
               []
               []
               []
               ["[" [(Tactic.simpStar "*") "," (Tactic.simpLemma [] [] `add)] "]"]
               [])])))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`a `t]
        []
        "=>"
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Tactic.simp
             "simp"
             []
             []
             []
             ["[" [(Tactic.simpStar "*") "," (Tactic.simpLemma [] [] `add)] "]"]
             [])])))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.simp
           "simp"
           []
           []
           []
           ["[" [(Tactic.simpStar "*") "," (Tactic.simpLemma [] [] `add)] "]"]
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       []
       ["[" [(Tactic.simpStar "*") "," (Tactic.simpLemma [] [] `add)] "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `add
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `t
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `v "." `consElim)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `v
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `w
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `v
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `succ [`m])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `m
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `succ
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      `rfl
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `w
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `v
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.forall
       "∀"
       [(Term.implicitBinder "{" [`m] [] "}")
        (Term.explicitBinder "(" [`v] [":" (Term.app `Vector3 [`α `m])] [] ")")
        (Term.implicitBinder "{" [`n] [] "}")
        (Term.explicitBinder "(" [`w] [":" (Term.app `Vector3 [`α `n])] [] ")")
        (Term.explicitBinder "(" [`i] [":" (Term.app `Fin2 [`n])] [] ")")]
       []
       ","
       («term_=_»
        (Term.app (Vector3.Data.Vector3.«term_+-+_» `v " +-+ " `w) [(Term.app `add [`i `m])])
        "="
        (Term.app `w [`i])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Term.app (Vector3.Data.Vector3.«term_+-+_» `v " +-+ " `w) [(Term.app `add [`i `m])])
       "="
       (Term.app `w [`i]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `w [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `w
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app (Vector3.Data.Vector3.«term_+-+_» `v " +-+ " `w) [(Term.app `add [`i `m])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `add [`i `m])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `m
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `add
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `add [`i `m]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Vector3.Data.Vector3.«term_+-+_» `v " +-+ " `w)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Vector3.Data.Vector3.«term_+-+_»', expected 'Vector3.Data.Vector3.term_+-+_._@.Data.Vector3._hyg.966'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ simp ]
  theorem
    append_add
    : ∀ { m } ( v : Vector3 α m ) { n } ( w : Vector3 α n ) ( i : Fin2 n ) , v +-+ w add i m = w i
    | 0 , v , n , w , i => rfl
      | succ m , v , n , w , i => v . consElim fun a t => by simp [ * , add ]
#align vector3.append_add Vector3.append_add

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- Insert `a` into `v` at index `i`. -/
def insert (a : α) (v : Vector3 α n) (i : Fin2 (succ n)) : Vector3 α (succ n) := fun j =>
  (a::v) (insertPerm i j)
#align vector3.insert Vector3.insert

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem insert_fz (a : α) (v : Vector3 α n) : insert a v fz = a::v := by
  refine' funext fun j => j.cases' _ _ <;> intros <;> rfl
#align vector3.insert_fz Vector3.insert_fz

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem insert_fs (a : α) (b : α) (v : Vector3 α n) (i : Fin2 (succ n)) :
    insert a (b::v) (fs i) = b::insert a v i :=
  funext fun j => by
    refine' j.cases' _ fun j => _ <;> simp [insert, insert_perm]
    refine' Fin2.cases' _ _ (insert_perm i j) <;> simp [insert_perm]
#align vector3.insert_fs Vector3.insert_fs

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `append_insert [])
      (Command.declSig
       [(Term.explicitBinder "(" [`a] [":" `α] [] ")")
        (Term.explicitBinder "(" [`t] [":" (Term.app `Vector3 [`α `m])] [] ")")
        (Term.explicitBinder "(" [`v] [":" (Term.app `Vector3 [`α `n])] [] ")")
        (Term.explicitBinder "(" [`i] [":" (Term.app `Fin2 [(Term.app `succ [`n])])] [] ")")
        (Term.explicitBinder
         "("
         [`e]
         [":"
          («term_=_»
           («term_+_» (Term.app `succ [`n]) "+" `m)
           "="
           (Term.app `succ [(«term_+_» `n "+" `m)]))]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app
          `insert
          [`a
           (Vector3.Data.Vector3.«term_+-+_» `t " +-+ " `v)
           (Term.app `Eq.recOn [`e (Term.app (Term.proj `i "." `add) [`m])])])
         "="
         (Term.app
          `Eq.recOn
          [`e (Vector3.Data.Vector3.«term_+-+_» `t " +-+ " (Term.app `insert [`a `v `i]))]))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.refine'
            "refine'"
            (Term.app
             `Vector3.recOn
             [`t
              (Term.fun "fun" (Term.basicFun [`e] [] "=>" (Term.hole "_")))
              (Term.fun "fun" (Term.basicFun [`k `b `t `IH `e] [] "=>" (Term.hole "_")))
              `e]))
           ";"
           (Tactic.tacticRfl "rfl")
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl (Term.haveIdDecl [`e' []] [] ":=" (Term.app `succ_add [`n `k]))))
           []
           (Tactic.change
            "change"
            («term_=_»
             (Term.app
              `insert
              [`a
               (Vector3.Data.Vector3.vector.cons
                `b
                "::"
                (Vector3.Data.Vector3.«term_+-+_» `t " +-+ " `v))
               (Term.app
                `Eq.recOn
                [(Term.app `congr_arg [`succ `e']) (Term.app `fs [(Term.app `add [`i `k])])])])
             "="
             (Term.app
              `Eq.recOn
              [(Term.app `congr_arg [`succ `e'])
               (Vector3.Data.Vector3.vector.cons
                `b
                "::"
                (Vector3.Data.Vector3.«term_+-+_» `t " +-+ " (Term.app `insert [`a `v `i])))]))
            [])
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule
               [(patternIgnore (token.«← » "←"))]
               (Term.typeAscription
                "("
                (Term.app `Eq.drecOn [`e' `rfl])
                ":"
                [(«term_=_»
                  (Term.app
                   `fs
                   [(Term.typeAscription
                     "("
                     (Term.app `Eq.recOn [`e' (Term.app `i.add [`k])])
                     ":"
                     [(Term.app `Fin2 [(Term.app `succ [(«term_+_» `n "+" `k)])])]
                     ")")])
                  "="
                  (Term.app
                   `Eq.recOn
                   [(Term.app `congr_arg [`succ `e']) (Term.app `fs [(Term.app `i.add [`k])])]))]
                ")"))]
             "]")
            [])
           []
           (Tactic.simp "simp" [] [] [] [] [])
           ";"
           (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `IH)] "]") [])
           ";"
           (Tactic.exact "exact" (Term.app `Eq.drecOn [`e' `rfl]))])))
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
         [(Tactic.refine'
           "refine'"
           (Term.app
            `Vector3.recOn
            [`t
             (Term.fun "fun" (Term.basicFun [`e] [] "=>" (Term.hole "_")))
             (Term.fun "fun" (Term.basicFun [`k `b `t `IH `e] [] "=>" (Term.hole "_")))
             `e]))
          ";"
          (Tactic.tacticRfl "rfl")
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl (Term.haveIdDecl [`e' []] [] ":=" (Term.app `succ_add [`n `k]))))
          []
          (Tactic.change
           "change"
           («term_=_»
            (Term.app
             `insert
             [`a
              (Vector3.Data.Vector3.vector.cons
               `b
               "::"
               (Vector3.Data.Vector3.«term_+-+_» `t " +-+ " `v))
              (Term.app
               `Eq.recOn
               [(Term.app `congr_arg [`succ `e']) (Term.app `fs [(Term.app `add [`i `k])])])])
            "="
            (Term.app
             `Eq.recOn
             [(Term.app `congr_arg [`succ `e'])
              (Vector3.Data.Vector3.vector.cons
               `b
               "::"
               (Vector3.Data.Vector3.«term_+-+_» `t " +-+ " (Term.app `insert [`a `v `i])))]))
           [])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule
              [(patternIgnore (token.«← » "←"))]
              (Term.typeAscription
               "("
               (Term.app `Eq.drecOn [`e' `rfl])
               ":"
               [(«term_=_»
                 (Term.app
                  `fs
                  [(Term.typeAscription
                    "("
                    (Term.app `Eq.recOn [`e' (Term.app `i.add [`k])])
                    ":"
                    [(Term.app `Fin2 [(Term.app `succ [(«term_+_» `n "+" `k)])])]
                    ")")])
                 "="
                 (Term.app
                  `Eq.recOn
                  [(Term.app `congr_arg [`succ `e']) (Term.app `fs [(Term.app `i.add [`k])])]))]
               ")"))]
            "]")
           [])
          []
          (Tactic.simp "simp" [] [] [] [] [])
          ";"
          (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `IH)] "]") [])
          ";"
          (Tactic.exact "exact" (Term.app `Eq.drecOn [`e' `rfl]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" (Term.app `Eq.drecOn [`e' `rfl]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Eq.drecOn [`e' `rfl])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rfl
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `e'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Eq.drecOn
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `IH)] "]") [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `IH
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] [] [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule
          [(patternIgnore (token.«← » "←"))]
          (Term.typeAscription
           "("
           (Term.app `Eq.drecOn [`e' `rfl])
           ":"
           [(«term_=_»
             (Term.app
              `fs
              [(Term.typeAscription
                "("
                (Term.app `Eq.recOn [`e' (Term.app `i.add [`k])])
                ":"
                [(Term.app `Fin2 [(Term.app `succ [(«term_+_» `n "+" `k)])])]
                ")")])
             "="
             (Term.app
              `Eq.recOn
              [(Term.app `congr_arg [`succ `e']) (Term.app `fs [(Term.app `i.add [`k])])]))]
           ")"))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription
       "("
       (Term.app `Eq.drecOn [`e' `rfl])
       ":"
       [(«term_=_»
         (Term.app
          `fs
          [(Term.typeAscription
            "("
            (Term.app `Eq.recOn [`e' (Term.app `i.add [`k])])
            ":"
            [(Term.app `Fin2 [(Term.app `succ [(«term_+_» `n "+" `k)])])]
            ")")])
         "="
         (Term.app
          `Eq.recOn
          [(Term.app `congr_arg [`succ `e']) (Term.app `fs [(Term.app `i.add [`k])])]))]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Term.app
        `fs
        [(Term.typeAscription
          "("
          (Term.app `Eq.recOn [`e' (Term.app `i.add [`k])])
          ":"
          [(Term.app `Fin2 [(Term.app `succ [(«term_+_» `n "+" `k)])])]
          ")")])
       "="
       (Term.app
        `Eq.recOn
        [(Term.app `congr_arg [`succ `e']) (Term.app `fs [(Term.app `i.add [`k])])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Eq.recOn
       [(Term.app `congr_arg [`succ `e']) (Term.app `fs [(Term.app `i.add [`k])])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `fs [(Term.app `i.add [`k])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `i.add [`k])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `i.add
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `i.add [`k]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `fs
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `fs [(Term.paren "(" (Term.app `i.add [`k]) ")")])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `congr_arg [`succ `e'])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `e'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `succ
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `congr_arg
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `congr_arg [`succ `e']) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Eq.recOn
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app
       `fs
       [(Term.typeAscription
         "("
         (Term.app `Eq.recOn [`e' (Term.app `i.add [`k])])
         ":"
         [(Term.app `Fin2 [(Term.app `succ [(«term_+_» `n "+" `k)])])]
         ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription
       "("
       (Term.app `Eq.recOn [`e' (Term.app `i.add [`k])])
       ":"
       [(Term.app `Fin2 [(Term.app `succ [(«term_+_» `n "+" `k)])])]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Fin2 [(Term.app `succ [(«term_+_» `n "+" `k)])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `succ [(«term_+_» `n "+" `k)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_+_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_+_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_» `n "+" `k)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `n
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_+_» `n "+" `k) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `succ
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `succ [(Term.paren "(" («term_+_» `n "+" `k) ")")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Fin2
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Eq.recOn [`e' (Term.app `i.add [`k])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `i.add [`k])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `i.add
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `i.add [`k]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `e'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Eq.recOn
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `fs
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Eq.drecOn [`e' `rfl])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rfl
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `e'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Eq.drecOn
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.change
       "change"
       («term_=_»
        (Term.app
         `insert
         [`a
          (Vector3.Data.Vector3.vector.cons
           `b
           "::"
           (Vector3.Data.Vector3.«term_+-+_» `t " +-+ " `v))
          (Term.app
           `Eq.recOn
           [(Term.app `congr_arg [`succ `e']) (Term.app `fs [(Term.app `add [`i `k])])])])
        "="
        (Term.app
         `Eq.recOn
         [(Term.app `congr_arg [`succ `e'])
          (Vector3.Data.Vector3.vector.cons
           `b
           "::"
           (Vector3.Data.Vector3.«term_+-+_» `t " +-+ " (Term.app `insert [`a `v `i])))]))
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Term.app
        `insert
        [`a
         (Vector3.Data.Vector3.vector.cons `b "::" (Vector3.Data.Vector3.«term_+-+_» `t " +-+ " `v))
         (Term.app
          `Eq.recOn
          [(Term.app `congr_arg [`succ `e']) (Term.app `fs [(Term.app `add [`i `k])])])])
       "="
       (Term.app
        `Eq.recOn
        [(Term.app `congr_arg [`succ `e'])
         (Vector3.Data.Vector3.vector.cons
          `b
          "::"
          (Vector3.Data.Vector3.«term_+-+_» `t " +-+ " (Term.app `insert [`a `v `i])))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Eq.recOn
       [(Term.app `congr_arg [`succ `e'])
        (Vector3.Data.Vector3.vector.cons
         `b
         "::"
         (Vector3.Data.Vector3.«term_+-+_» `t " +-+ " (Term.app `insert [`a `v `i])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Vector3.Data.Vector3.vector.cons', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Vector3.Data.Vector3.vector.cons', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Vector3.Data.Vector3.vector.cons
       `b
       "::"
       (Vector3.Data.Vector3.«term_+-+_» `t " +-+ " (Term.app `insert [`a `v `i])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Vector3.Data.Vector3.«term_+-+_» `t " +-+ " (Term.app `insert [`a `v `i]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Vector3.Data.Vector3.«term_+-+_»', expected 'Vector3.Data.Vector3.term_+-+_._@.Data.Vector3._hyg.966'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  append_insert
  ( a : α )
      ( t : Vector3 α m )
      ( v : Vector3 α n )
      ( i : Fin2 succ n )
      ( e : succ n + m = succ n + m )
    : insert a t +-+ v Eq.recOn e i . add m = Eq.recOn e t +-+ insert a v i
  :=
    by
      refine' Vector3.recOn t fun e => _ fun k b t IH e => _ e
        ;
        rfl
        have e' := succ_add n k
        change
          insert a b :: t +-+ v Eq.recOn congr_arg succ e' fs add i k
            =
            Eq.recOn congr_arg succ e' b :: t +-+ insert a v i
        rw
          [
            ←
              (
                Eq.drecOn e' rfl
                :
                fs ( Eq.recOn e' i.add k : Fin2 succ n + k ) = Eq.recOn congr_arg succ e' fs i.add k
                )
            ]
        simp
        ;
        rw [ IH ]
        ;
        exact Eq.drecOn e' rfl
#align vector3.append_insert Vector3.append_insert

end Vector3

section Vector3

open Vector3

open Vector3

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- "Curried" exists, i.e. `∃ x₁ ... xₙ, f [x₁, ..., xₙ]`. -/
def VectorEx : ∀ k, (Vector3 α k → Prop) → Prop
  | 0, f => f []
  | succ k, f => ∃ x : α, VectorEx k fun v => f (x::v)
#align vector_ex VectorEx

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- "Curried" forall, i.e. `∀ x₁ ... xₙ, f [x₁, ..., xₙ]`. -/
def VectorAll : ∀ k, (Vector3 α k → Prop) → Prop
  | 0, f => f []
  | succ k, f => ∀ x : α, VectorAll k fun v => f (x::v)
#align vector_all VectorAll

theorem exists_vector_zero (f : Vector3 α 0 → Prop) : Exists f ↔ f [] :=
  ⟨fun ⟨v, fv⟩ => by rw [← eq_nil v] <;> exact fv, fun f0 => ⟨[], f0⟩⟩
#align exists_vector_zero exists_vector_zero

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem exists_vector_succ (f : Vector3 α (succ n) → Prop) : Exists f ↔ ∃ x v, f (x::v) :=
  ⟨fun ⟨v, fv⟩ => ⟨_, _, by rw [cons_head_tail v] <;> exact fv⟩, fun ⟨x, v, fxv⟩ => ⟨_, fxv⟩⟩
#align exists_vector_succ exists_vector_succ

theorem vector_ex_iff_exists : ∀ {n} (f : Vector3 α n → Prop), VectorEx n f ↔ Exists f
  | 0, f => (exists_vector_zero f).symm
  | succ n, f =>
    Iff.trans (exists_congr fun x => vector_ex_iff_exists _) (exists_vector_succ f).symm
#align vector_ex_iff_exists vector_ex_iff_exists

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem vector_all_iff_forall : ∀ {n} (f : Vector3 α n → Prop), VectorAll n f ↔ ∀ v, f v
  | 0, f => ⟨fun f0 v => v.nilElim f0, fun al => al []⟩
  | succ n, f =>
    (forall_congr' fun x => vector_all_iff_forall fun v => f (x::v)).trans
      ⟨fun al v => v.consElim al, fun al x v => al (x::v)⟩
#align vector_all_iff_forall vector_all_iff_forall

/-- `vector_allp p v` is equivalent to `∀ i, p (v i)`, but unfolds directly to a conjunction,
  i.e. `vector_allp p [0, 1, 2] = p 0 ∧ p 1 ∧ p 2`. -/
def VectorAllp (p : α → Prop) (v : Vector3 α n) : Prop :=
  Vector3.recOn v True fun n a v IH =>
    @Vector3.recOn _ (fun n v => Prop) _ v (p a) fun n b v' _ => p a ∧ IH
#align vector_allp VectorAllp

@[simp]
theorem vector_allp_nil (p : α → Prop) : VectorAllp p [] = True :=
  rfl
#align vector_allp_nil vector_allp_nil

@[simp]
theorem vector_allp_singleton (p : α → Prop) (x : α) : VectorAllp p [x] = p x :=
  rfl
#align vector_allp_singleton vector_allp_singleton

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem vector_allp_cons (p : α → Prop) (x : α) (v : Vector3 α n) :
    VectorAllp p (x::v) ↔ p x ∧ VectorAllp p v :=
  Vector3.recOn v (and_true_iff _).symm fun n a v IH => Iff.rfl
#align vector_allp_cons vector_allp_cons

theorem vector_allp_iff_forall (p : α → Prop) (v : Vector3 α n) : VectorAllp p v ↔ ∀ i, p (v i) :=
  by
  refine' v.rec_on _ _
  · exact ⟨fun _ => Fin2.elim0, fun _ => trivial⟩
  · simp
    refine' fun n a v IH =>
      (and_congr_right fun _ => IH).trans
        ⟨fun ⟨pa, h⟩ i => by
          refine' i.cases' _ _
          exacts[pa, h], fun h => ⟨_, fun i => _⟩⟩
    · have h0 := h fz
      simp at h0
      exact h0
    · have hs := h (fs i)
      simp at hs
      exact hs
#align vector_allp_iff_forall vector_allp_iff_forall

theorem VectorAllp.imp {p q : α → Prop} (h : ∀ x, p x → q x) {v : Vector3 α n}
    (al : VectorAllp p v) : VectorAllp q v :=
  (vector_allp_iff_forall _ _).2 fun i => h _ <| (vector_allp_iff_forall _ _).1 al _
#align vector_allp.imp VectorAllp.imp

end Vector3

