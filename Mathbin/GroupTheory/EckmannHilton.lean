/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Kenny Lau, Robert Y. Lewis

! This file was ported from Lean 3 source module group_theory.eckmann_hilton
! leanprover-community/mathlib commit 26f081a2fb920140ed5bc5cc5344e84bcc7cb2b2
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Group.Defs

/-!
# Eckmann-Hilton argument

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

The Eckmann-Hilton argument says that if a type carries two monoid structures that distribute
over one another, then they are equal, and in addition commutative.
The main application lies in proving that higher homotopy groups (`πₙ` for `n ≥ 2`) are commutative.

## Main declarations

* `eckmann_hilton.comm_monoid`: If a type carries a unital magma structure that distributes
  over a unital binary operation, then the magma is a commutative monoid.
* `eckmann_hilton.comm_group`: If a type carries a group structure that distributes
  over a unital binary operation, then the group is commutative.

-/


universe u

namespace EckmannHilton

variable {X : Type u}

-- mathport name: «expr < > »
local notation a " <" m "> " b => m a b

#print EckmannHilton.IsUnital /-
/-- `is_unital m e` expresses that `e : X` is a left and right unit
for the binary operation `m : X → X → X`. -/
structure IsUnital (m : X → X → X) (e : X) extends IsLeftId _ m e, IsRightId _ m e : Prop
#align eckmann_hilton.is_unital EckmannHilton.IsUnital
-/

/- warning: eckmann_hilton.mul_one_class.is_unital -> EckmannHilton.MulOneClass.isUnital is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [G : MulOneClass.{u1} X], EckmannHilton.IsUnital.{u1} X (HMul.hMul.{u1, u1, u1} X X X (instHMul.{u1} X (MulOneClass.toHasMul.{u1} X G))) (OfNat.ofNat.{u1} X 1 (OfNat.mk.{u1} X 1 (One.one.{u1} X (MulOneClass.toHasOne.{u1} X G))))
but is expected to have type
  forall {X : Type.{u1}} [G : MulOneClass.{u1} X], EckmannHilton.IsUnital.{u1} X (fun (x._@.Mathlib.GroupTheory.EckmannHilton._hyg.284 : X) (x._@.Mathlib.GroupTheory.EckmannHilton._hyg.286 : X) => HMul.hMul.{u1, u1, u1} X X X (instHMul.{u1} X (MulOneClass.toMul.{u1} X G)) x._@.Mathlib.GroupTheory.EckmannHilton._hyg.284 x._@.Mathlib.GroupTheory.EckmannHilton._hyg.286) (OfNat.ofNat.{u1} X 1 (One.toOfNat1.{u1} X (MulOneClass.toOne.{u1} X G)))
Case conversion may be inaccurate. Consider using '#align eckmann_hilton.mul_one_class.is_unital EckmannHilton.MulOneClass.isUnitalₓ'. -/
@[to_additive EckmannHilton.AddZeroClass.is_unital]
theorem MulOneClass.isUnital [G : MulOneClass X] : IsUnital (· * ·) (1 : X) :=
  IsUnital.mk (by infer_instance) (by infer_instance)
#align eckmann_hilton.mul_one_class.is_unital EckmannHilton.MulOneClass.isUnital

variable {m₁ m₂ : X → X → X} {e₁ e₂ : X}

variable (h₁ : IsUnital m₁ e₁) (h₂ : IsUnital m₂ e₂)

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.variable
     "variable"
     [(Term.explicitBinder
       "("
       [`distrib]
       [":"
        (Term.forall
         "∀"
         [`a `b `c `d]
         []
         ","
         («term_=_»
          (EckmannHilton.GroupTheory.EckmannHilton.«term_<_>_»
           (EckmannHilton.GroupTheory.EckmannHilton.«term_<_>_» `a " <" `m₂ "> " `b)
           " <"
           `m₁
           "> "
           (EckmannHilton.GroupTheory.EckmannHilton.«term_<_>_» `c " <" `m₂ "> " `d))
          "="
          (EckmannHilton.GroupTheory.EckmannHilton.«term_<_>_»
           (EckmannHilton.GroupTheory.EckmannHilton.«term_<_>_» `a " <" `m₁ "> " `c)
           " <"
           `m₂
           "> "
           (EckmannHilton.GroupTheory.EckmannHilton.«term_<_>_» `b " <" `m₁ "> " `d))))]
       []
       ")")])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.forall
       "∀"
       [`a `b `c `d]
       []
       ","
       («term_=_»
        (EckmannHilton.GroupTheory.EckmannHilton.«term_<_>_»
         (EckmannHilton.GroupTheory.EckmannHilton.«term_<_>_» `a " <" `m₂ "> " `b)
         " <"
         `m₁
         "> "
         (EckmannHilton.GroupTheory.EckmannHilton.«term_<_>_» `c " <" `m₂ "> " `d))
        "="
        (EckmannHilton.GroupTheory.EckmannHilton.«term_<_>_»
         (EckmannHilton.GroupTheory.EckmannHilton.«term_<_>_» `a " <" `m₁ "> " `c)
         " <"
         `m₂
         "> "
         (EckmannHilton.GroupTheory.EckmannHilton.«term_<_>_» `b " <" `m₁ "> " `d))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (EckmannHilton.GroupTheory.EckmannHilton.«term_<_>_»
        (EckmannHilton.GroupTheory.EckmannHilton.«term_<_>_» `a " <" `m₂ "> " `b)
        " <"
        `m₁
        "> "
        (EckmannHilton.GroupTheory.EckmannHilton.«term_<_>_» `c " <" `m₂ "> " `d))
       "="
       (EckmannHilton.GroupTheory.EckmannHilton.«term_<_>_»
        (EckmannHilton.GroupTheory.EckmannHilton.«term_<_>_» `a " <" `m₁ "> " `c)
        " <"
        `m₂
        "> "
        (EckmannHilton.GroupTheory.EckmannHilton.«term_<_>_» `b " <" `m₁ "> " `d)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (EckmannHilton.GroupTheory.EckmannHilton.«term_<_>_»
       (EckmannHilton.GroupTheory.EckmannHilton.«term_<_>_» `a " <" `m₁ "> " `c)
       " <"
       `m₂
       "> "
       (EckmannHilton.GroupTheory.EckmannHilton.«term_<_>_» `b " <" `m₁ "> " `d))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'EckmannHilton.GroupTheory.EckmannHilton.«term_<_>_»', expected 'EckmannHilton.GroupTheory.EckmannHilton.term_<_>_._@.GroupTheory.EckmannHilton._hyg.6'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.instBinder'-/-- failed to format: format: uncaught backtrack exception
variable ( distrib : ∀ a b c d , a < m₂ > b < m₁ > c < m₂ > d = a < m₁ > c < m₂ > b < m₁ > d )

include h₁ h₂ distrib

#print EckmannHilton.one /-
/-- If a type carries two unital binary operations that distribute over each other,
then they have the same unit elements.

In fact, the two operations are the same, and give a commutative monoid structure,
see `eckmann_hilton.comm_monoid`. -/
theorem one : e₁ = e₂ := by
  simpa only [h₁.left_id, h₁.right_id, h₂.left_id, h₂.right_id] using Distrib e₂ e₁ e₁ e₂
#align eckmann_hilton.one EckmannHilton.one
-/

#print EckmannHilton.mul /-
/-- If a type carries two unital binary operations that distribute over each other,
then these operations are equal.

In fact, they give a commutative monoid structure, see `eckmann_hilton.comm_monoid`. -/
theorem mul : m₁ = m₂ := by
  funext a b
  calc
    m₁ a b = m₁ (m₂ a e₁) (m₂ e₁ b) := by
      simp only [one h₁ h₂ Distrib, h₁.left_id, h₁.right_id, h₂.left_id, h₂.right_id]
    _ = m₂ a b := by simp only [Distrib, h₁.left_id, h₁.right_id, h₂.left_id, h₂.right_id]
    
#align eckmann_hilton.mul EckmannHilton.mul
-/

#print EckmannHilton.mul_comm /-
/-- If a type carries two unital binary operations that distribute over each other,
then these operations are commutative.

In fact, they give a commutative monoid structure, see `eckmann_hilton.comm_monoid`. -/
theorem mul_comm : IsCommutative _ m₂ :=
  ⟨fun a b => by simpa [mul h₁ h₂ Distrib, h₂.left_id, h₂.right_id] using Distrib e₂ a b e₂⟩
#align eckmann_hilton.mul_comm EckmannHilton.mul_comm
-/

#print EckmannHilton.mul_assoc /-
/-- If a type carries two unital binary operations that distribute over each other,
then these operations are associative.

In fact, they give a commutative monoid structure, see `eckmann_hilton.comm_monoid`. -/
theorem mul_assoc : IsAssociative _ m₂ :=
  ⟨fun a b c => by simpa [mul h₁ h₂ Distrib, h₂.left_id, h₂.right_id] using Distrib a b e₂ c⟩
#align eckmann_hilton.mul_assoc EckmannHilton.mul_assoc
-/

omit h₁ h₂ distrib

/- warning: eckmann_hilton.comm_monoid -> EckmannHilton.commMonoid is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {m₁ : X -> X -> X} {e₁ : X}, (EckmannHilton.IsUnital.{u1} X m₁ e₁) -> (forall [h : MulOneClass.{u1} X], (forall (a : X) (b : X) (c : X) (d : X), Eq.{succ u1} X (m₁ (HMul.hMul.{u1, u1, u1} X X X (instHMul.{u1} X (MulOneClass.toHasMul.{u1} X h)) a b) (HMul.hMul.{u1, u1, u1} X X X (instHMul.{u1} X (MulOneClass.toHasMul.{u1} X h)) c d)) (HMul.hMul.{u1, u1, u1} X X X (instHMul.{u1} X (MulOneClass.toHasMul.{u1} X h)) (m₁ a c) (m₁ b d))) -> (CommMonoid.{u1} X))
but is expected to have type
  forall {X : Type.{u1}} {m₁ : X -> X -> X} {e₁ : X}, (EckmannHilton.IsUnital.{u1} X m₁ e₁) -> (forall [h : MulOneClass.{u1} X], (forall (a : X) (b : X) (c : X) (d : X), Eq.{succ u1} X (m₁ (HMul.hMul.{u1, u1, u1} X X X (instHMul.{u1} X (MulOneClass.toMul.{u1} X h)) a b) (HMul.hMul.{u1, u1, u1} X X X (instHMul.{u1} X (MulOneClass.toMul.{u1} X h)) c d)) (HMul.hMul.{u1, u1, u1} X X X (instHMul.{u1} X (MulOneClass.toMul.{u1} X h)) (m₁ a c) (m₁ b d))) -> (CommMonoid.{u1} X))
Case conversion may be inaccurate. Consider using '#align eckmann_hilton.comm_monoid EckmannHilton.commMonoidₓ'. -/
/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "If a type carries a unital magma structure that distributes over a unital binary\noperations, then the magma structure is a commutative monoid. -/")]
      [(Term.attributes
        "@["
        [(Term.attrInstance (Term.attrKind []) (Attr.simple `reducible []))
         ","
         (Term.attrInstance
          (Term.attrKind [])
          (to_additive
           "to_additive"
           []
           []
           (to_additiveRest
            []
            []
            [(str
              "\"If a type carries a unital additive magma structure that distributes over\\na unital binary operations, then the additive magma structure is a commutative additive monoid.\"")])))]
        "]")]
      []
      []
      []
      [])
     (Command.def
      "def"
      (Command.declId `commMonoid [])
      (Command.optDeclSig
       [(Term.instBinder "[" [`h ":"] (Term.app `MulOneClass [`X]) "]")
        (Term.explicitBinder
         "("
         [`distrib]
         [":"
          (Term.forall
           "∀"
           [`a `b `c `d]
           []
           ","
           («term_=_»
            (EckmannHilton.GroupTheory.EckmannHilton.«term_<_>_»
             («term_*_» `a "*" `b)
             " <"
             `m₁
             "> "
             («term_*_» `c "*" `d))
            "="
            («term_*_»
             (EckmannHilton.GroupTheory.EckmannHilton.«term_<_>_» `a " <" `m₁ "> " `c)
             "*"
             (EckmannHilton.GroupTheory.EckmannHilton.«term_<_>_» `b " <" `m₁ "> " `d))))]
         []
         ")")]
       [(Term.typeSpec ":" (Term.app `CommMonoid [`X]))])
      (Command.declValSimple
       ":="
       (Term.structInst
        "{"
        [[`h] "with"]
        [(Term.structInstField
          (Term.structInstLVal `mul [])
          ":="
          (Term.paren "(" («term_*_» (Term.cdot "·") "*" (Term.cdot "·")) ")"))
         []
         (Term.structInstField (Term.structInstLVal `one []) ":=" (num "1"))
         []
         (Term.structInstField
          (Term.structInstLVal `mul_comm [])
          ":="
          (Term.proj (Term.app `mul_comm [`h₁ `MulOneClass.isUnital `Distrib]) "." `comm))
         []
         (Term.structInstField
          (Term.structInstLVal `mul_assoc [])
          ":="
          (Term.proj (Term.app `mul_assoc [`h₁ `MulOneClass.isUnital `Distrib]) "." `assoc))]
        (Term.optEllipsis [])
        []
        "}")
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.structInst
       "{"
       [[`h] "with"]
       [(Term.structInstField
         (Term.structInstLVal `mul [])
         ":="
         (Term.paren "(" («term_*_» (Term.cdot "·") "*" (Term.cdot "·")) ")"))
        []
        (Term.structInstField (Term.structInstLVal `one []) ":=" (num "1"))
        []
        (Term.structInstField
         (Term.structInstLVal `mul_comm [])
         ":="
         (Term.proj (Term.app `mul_comm [`h₁ `MulOneClass.isUnital `Distrib]) "." `comm))
        []
        (Term.structInstField
         (Term.structInstLVal `mul_assoc [])
         ":="
         (Term.proj (Term.app `mul_assoc [`h₁ `MulOneClass.isUnital `Distrib]) "." `assoc))]
       (Term.optEllipsis [])
       []
       "}")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.app `mul_assoc [`h₁ `MulOneClass.isUnital `Distrib]) "." `assoc)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `mul_assoc [`h₁ `MulOneClass.isUnital `Distrib])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Distrib
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `MulOneClass.isUnital
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `h₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `mul_assoc
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `mul_assoc [`h₁ `MulOneClass.isUnital `Distrib])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.app `mul_comm [`h₁ `MulOneClass.isUnital `Distrib]) "." `comm)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `mul_comm [`h₁ `MulOneClass.isUnital `Distrib])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Distrib
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `MulOneClass.isUnital
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `h₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `mul_comm
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `mul_comm [`h₁ `MulOneClass.isUnital `Distrib])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.paren "(" («term_*_» (Term.cdot "·") "*" (Term.cdot "·")) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_» (Term.cdot "·") "*" (Term.cdot "·"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.cdot "·")
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (Term.cdot "·")
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app `CommMonoid [`X])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `X
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `CommMonoid
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.forall
       "∀"
       [`a `b `c `d]
       []
       ","
       («term_=_»
        (EckmannHilton.GroupTheory.EckmannHilton.«term_<_>_»
         («term_*_» `a "*" `b)
         " <"
         `m₁
         "> "
         («term_*_» `c "*" `d))
        "="
        («term_*_»
         (EckmannHilton.GroupTheory.EckmannHilton.«term_<_>_» `a " <" `m₁ "> " `c)
         "*"
         (EckmannHilton.GroupTheory.EckmannHilton.«term_<_>_» `b " <" `m₁ "> " `d))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (EckmannHilton.GroupTheory.EckmannHilton.«term_<_>_»
        («term_*_» `a "*" `b)
        " <"
        `m₁
        "> "
        («term_*_» `c "*" `d))
       "="
       («term_*_»
        (EckmannHilton.GroupTheory.EckmannHilton.«term_<_>_» `a " <" `m₁ "> " `c)
        "*"
        (EckmannHilton.GroupTheory.EckmannHilton.«term_<_>_» `b " <" `m₁ "> " `d)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_»
       (EckmannHilton.GroupTheory.EckmannHilton.«term_<_>_» `a " <" `m₁ "> " `c)
       "*"
       (EckmannHilton.GroupTheory.EckmannHilton.«term_<_>_» `b " <" `m₁ "> " `d))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (EckmannHilton.GroupTheory.EckmannHilton.«term_<_>_» `b " <" `m₁ "> " `d)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'EckmannHilton.GroupTheory.EckmannHilton.«term_<_>_»', expected 'EckmannHilton.GroupTheory.EckmannHilton.term_<_>_._@.GroupTheory.EckmannHilton._hyg.6'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
      If a type carries a unital magma structure that distributes over a unital binary
      operations, then the magma structure is a commutative monoid. -/
    @[
      reducible
        ,
        to_additive
          "If a type carries a unital additive magma structure that distributes over\na unital binary operations, then the additive magma structure is a commutative additive monoid."
      ]
  def
    commMonoid
    [ h : MulOneClass X ] ( distrib : ∀ a b c d , a * b < m₁ > c * d = a < m₁ > c * b < m₁ > d )
      : CommMonoid X
    :=
      {
        h with
        mul := ( · * · )
          one := 1
          mul_comm := mul_comm h₁ MulOneClass.isUnital Distrib . comm
          mul_assoc := mul_assoc h₁ MulOneClass.isUnital Distrib . assoc
        }
#align eckmann_hilton.comm_monoid EckmannHilton.commMonoid

/- warning: eckmann_hilton.comm_group -> EckmannHilton.commGroup is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {m₁ : X -> X -> X} {e₁ : X}, (EckmannHilton.IsUnital.{u1} X m₁ e₁) -> (forall [G : Group.{u1} X], (forall (a : X) (b : X) (c : X) (d : X), Eq.{succ u1} X (m₁ (HMul.hMul.{u1, u1, u1} X X X (instHMul.{u1} X (MulOneClass.toHasMul.{u1} X (Monoid.toMulOneClass.{u1} X (DivInvMonoid.toMonoid.{u1} X (Group.toDivInvMonoid.{u1} X G))))) a b) (HMul.hMul.{u1, u1, u1} X X X (instHMul.{u1} X (MulOneClass.toHasMul.{u1} X (Monoid.toMulOneClass.{u1} X (DivInvMonoid.toMonoid.{u1} X (Group.toDivInvMonoid.{u1} X G))))) c d)) (HMul.hMul.{u1, u1, u1} X X X (instHMul.{u1} X (MulOneClass.toHasMul.{u1} X (Monoid.toMulOneClass.{u1} X (DivInvMonoid.toMonoid.{u1} X (Group.toDivInvMonoid.{u1} X G))))) (m₁ a c) (m₁ b d))) -> (CommGroup.{u1} X))
but is expected to have type
  forall {X : Type.{u1}} {m₁ : X -> X -> X} {e₁ : X}, (EckmannHilton.IsUnital.{u1} X m₁ e₁) -> (forall [G : Group.{u1} X], (forall (a : X) (b : X) (c : X) (d : X), Eq.{succ u1} X (m₁ (HMul.hMul.{u1, u1, u1} X X X (instHMul.{u1} X (MulOneClass.toMul.{u1} X (Monoid.toMulOneClass.{u1} X (DivInvMonoid.toMonoid.{u1} X (Group.toDivInvMonoid.{u1} X G))))) a b) (HMul.hMul.{u1, u1, u1} X X X (instHMul.{u1} X (MulOneClass.toMul.{u1} X (Monoid.toMulOneClass.{u1} X (DivInvMonoid.toMonoid.{u1} X (Group.toDivInvMonoid.{u1} X G))))) c d)) (HMul.hMul.{u1, u1, u1} X X X (instHMul.{u1} X (MulOneClass.toMul.{u1} X (Monoid.toMulOneClass.{u1} X (DivInvMonoid.toMonoid.{u1} X (Group.toDivInvMonoid.{u1} X G))))) (m₁ a c) (m₁ b d))) -> (CommGroup.{u1} X))
Case conversion may be inaccurate. Consider using '#align eckmann_hilton.comm_group EckmannHilton.commGroupₓ'. -/
/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "If a type carries a group structure that distributes over a unital binary operation,\nthen the group is commutative. -/")]
      [(Term.attributes
        "@["
        [(Term.attrInstance (Term.attrKind []) (Attr.simple `reducible []))
         ","
         (Term.attrInstance
          (Term.attrKind [])
          (to_additive
           "to_additive"
           []
           []
           (to_additiveRest
            []
            []
            [(str
              "\"If a type carries an additive group structure that\\ndistributes over a unital binary operation, then the additive group is commutative.\"")])))]
        "]")]
      []
      []
      []
      [])
     (Command.def
      "def"
      (Command.declId `commGroup [])
      (Command.optDeclSig
       [(Term.instBinder "[" [`G ":"] (Term.app `Group [`X]) "]")
        (Term.explicitBinder
         "("
         [`distrib]
         [":"
          (Term.forall
           "∀"
           [`a `b `c `d]
           []
           ","
           («term_=_»
            (EckmannHilton.GroupTheory.EckmannHilton.«term_<_>_»
             («term_*_» `a "*" `b)
             " <"
             `m₁
             "> "
             («term_*_» `c "*" `d))
            "="
            («term_*_»
             (EckmannHilton.GroupTheory.EckmannHilton.«term_<_>_» `a " <" `m₁ "> " `c)
             "*"
             (EckmannHilton.GroupTheory.EckmannHilton.«term_<_>_» `b " <" `m₁ "> " `d))))]
         []
         ")")]
       [(Term.typeSpec ":" (Term.app `CommGroup [`X]))])
      (Command.declValSimple
       ":="
       (Term.structInst
        "{"
        [[(Term.app `EckmannHilton.commMonoid [`h₁ `Distrib]) "," `G] "with"]
        []
        (Term.optEllipsis [])
        []
        "}")
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.structInst
       "{"
       [[(Term.app `EckmannHilton.commMonoid [`h₁ `Distrib]) "," `G] "with"]
       []
       (Term.optEllipsis [])
       []
       "}")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `G
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `EckmannHilton.commMonoid [`h₁ `Distrib])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Distrib
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `h₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `EckmannHilton.commMonoid
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app `CommGroup [`X])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `X
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `CommGroup
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.forall
       "∀"
       [`a `b `c `d]
       []
       ","
       («term_=_»
        (EckmannHilton.GroupTheory.EckmannHilton.«term_<_>_»
         («term_*_» `a "*" `b)
         " <"
         `m₁
         "> "
         («term_*_» `c "*" `d))
        "="
        («term_*_»
         (EckmannHilton.GroupTheory.EckmannHilton.«term_<_>_» `a " <" `m₁ "> " `c)
         "*"
         (EckmannHilton.GroupTheory.EckmannHilton.«term_<_>_» `b " <" `m₁ "> " `d))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (EckmannHilton.GroupTheory.EckmannHilton.«term_<_>_»
        («term_*_» `a "*" `b)
        " <"
        `m₁
        "> "
        («term_*_» `c "*" `d))
       "="
       («term_*_»
        (EckmannHilton.GroupTheory.EckmannHilton.«term_<_>_» `a " <" `m₁ "> " `c)
        "*"
        (EckmannHilton.GroupTheory.EckmannHilton.«term_<_>_» `b " <" `m₁ "> " `d)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_»
       (EckmannHilton.GroupTheory.EckmannHilton.«term_<_>_» `a " <" `m₁ "> " `c)
       "*"
       (EckmannHilton.GroupTheory.EckmannHilton.«term_<_>_» `b " <" `m₁ "> " `d))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (EckmannHilton.GroupTheory.EckmannHilton.«term_<_>_» `b " <" `m₁ "> " `d)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'EckmannHilton.GroupTheory.EckmannHilton.«term_<_>_»', expected 'EckmannHilton.GroupTheory.EckmannHilton.term_<_>_._@.GroupTheory.EckmannHilton._hyg.6'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
      If a type carries a group structure that distributes over a unital binary operation,
      then the group is commutative. -/
    @[
      reducible
        ,
        to_additive
          "If a type carries an additive group structure that\ndistributes over a unital binary operation, then the additive group is commutative."
      ]
  def
    commGroup
    [ G : Group X ] ( distrib : ∀ a b c d , a * b < m₁ > c * d = a < m₁ > c * b < m₁ > d )
      : CommGroup X
    := { EckmannHilton.commMonoid h₁ Distrib , G with }
#align eckmann_hilton.comm_group EckmannHilton.commGroup

end EckmannHilton

