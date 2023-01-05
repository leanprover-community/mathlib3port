/-
Copyright (c) 2022 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux

! This file was ported from Lean 3 source module algebra.star.pointwise
! leanprover-community/mathlib commit 5a3e819569b0f12cbec59d740a2613018e7b8eec
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Star.Basic
import Mathbin.Data.Set.Finite
import Mathbin.Data.Set.Pointwise.Basic

/-!
# Pointwise star operation on sets

This file defines the star operation pointwise on sets and provides the basic API.
Besides basic facts about about how the star operation acts on sets (e.g., `(s ∩ t)⋆ = s⋆ ∩ t⋆`),
if `s t : set α`, then under suitable assumption on `α`, it is shown

* `(s + t)⋆ = s⋆ + t⋆`
* `(s * t)⋆ = t⋆ + s⋆`
* `(s⁻¹)⋆ = (s⋆)⁻¹`
-/


namespace Set

open Pointwise

-- mathport name: «expr ⋆»
local postfix:max "⋆" => star

variable {α : Type _} {s t : Set α} {a : α}

/-- The set `(star s : set α)` is defined as `{x | star x ∈ s}` in locale `pointwise`.
In the usual case where `star` is involutive, it is equal to `{star s | x ∈ s}`, see
`set.image_star`. -/
protected def hasStar [HasStar α] : HasStar (Set α) :=
  ⟨preimage HasStar.star⟩
#align set.has_star Set.hasStar

scoped[Pointwise] attribute [instance] Set.hasStar

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
      (Command.declId `star_empty [])
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `HasStar [`α]) "]")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Set.Algebra.Star.Pointwise.«term_⋆»
          (Term.typeAscription "(" («term∅» "∅") ":" [(Term.app `Set [`α])] ")")
          "⋆")
         "="
         («term∅» "∅"))))
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
       (Set.Algebra.Star.Pointwise.«term_⋆»
        (Term.typeAscription "(" («term∅» "∅") ":" [(Term.app `Set [`α])] ")")
        "⋆")
       "="
       («term∅» "∅"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term∅» "∅")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Set.Algebra.Star.Pointwise.«term_⋆»
       (Term.typeAscription "(" («term∅» "∅") ":" [(Term.app `Set [`α])] ")")
       "⋆")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.Algebra.Star.Pointwise.«term_⋆»', expected 'Set.Algebra.Star.Pointwise.term_⋆._@.Algebra.Star.Pointwise._hyg.8'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ simp ] theorem star_empty [ HasStar α ] : ( ∅ : Set α ) ⋆ = ∅ := rfl
#align set.star_empty Set.star_empty

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
      (Command.declId `star_univ [])
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `HasStar [`α]) "]")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Set.Algebra.Star.Pointwise.«term_⋆»
          (Term.typeAscription "(" `univ ":" [(Term.app `Set [`α])] ")")
          "⋆")
         "="
         `univ)))
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
       (Set.Algebra.Star.Pointwise.«term_⋆»
        (Term.typeAscription "(" `univ ":" [(Term.app `Set [`α])] ")")
        "⋆")
       "="
       `univ)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `univ
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Set.Algebra.Star.Pointwise.«term_⋆»
       (Term.typeAscription "(" `univ ":" [(Term.app `Set [`α])] ")")
       "⋆")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.Algebra.Star.Pointwise.«term_⋆»', expected 'Set.Algebra.Star.Pointwise.term_⋆._@.Algebra.Star.Pointwise._hyg.8'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ simp ] theorem star_univ [ HasStar α ] : ( univ : Set α ) ⋆ = univ := rfl
#align set.star_univ Set.star_univ

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
      (Command.declId `nonempty_star [])
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `HasInvolutiveStar [`α]) "]")
        (Term.implicitBinder "{" [`s] [":" (Term.app `Set [`α])] "}")]
       (Term.typeSpec
        ":"
        («term_↔_»
         (Term.proj (Set.Algebra.Star.Pointwise.«term_⋆» `s "⋆") "." `Nonempty)
         "↔"
         (Term.proj `s "." `Nonempty))))
      (Command.declValSimple
       ":="
       (Term.proj (Term.proj `star_involutive "." `Surjective) "." `nonempty_preimage)
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.proj `star_involutive "." `Surjective) "." `nonempty_preimage)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj `star_involutive "." `Surjective)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `star_involutive
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_↔_»
       (Term.proj (Set.Algebra.Star.Pointwise.«term_⋆» `s "⋆") "." `Nonempty)
       "↔"
       (Term.proj `s "." `Nonempty))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `s "." `Nonempty)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `s
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 21 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 20, term))
      (Term.proj (Set.Algebra.Star.Pointwise.«term_⋆» `s "⋆") "." `Nonempty)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Set.Algebra.Star.Pointwise.«term_⋆» `s "⋆")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.Algebra.Star.Pointwise.«term_⋆»', expected 'Set.Algebra.Star.Pointwise.term_⋆._@.Algebra.Star.Pointwise._hyg.8'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ simp ]
  theorem
    nonempty_star
    [ HasInvolutiveStar α ] { s : Set α } : s ⋆ . Nonempty ↔ s . Nonempty
    := star_involutive . Surjective . nonempty_preimage
#align set.nonempty_star Set.nonempty_star

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `Nonempty.star [])
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `HasInvolutiveStar [`α]) "]")
        (Term.implicitBinder "{" [`s] [":" (Term.app `Set [`α])] "}")
        (Term.explicitBinder "(" [`h] [":" (Term.proj `s "." `Nonempty)] [] ")")]
       (Term.typeSpec ":" (Term.proj (Set.Algebra.Star.Pointwise.«term_⋆» `s "⋆") "." `Nonempty)))
      (Command.declValSimple ":=" (Term.app (Term.proj `nonempty_star "." (fieldIdx "2")) [`h]) [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj `nonempty_star "." (fieldIdx "2")) [`h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `nonempty_star "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `nonempty_star
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.proj (Set.Algebra.Star.Pointwise.«term_⋆» `s "⋆") "." `Nonempty)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Set.Algebra.Star.Pointwise.«term_⋆» `s "⋆")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.Algebra.Star.Pointwise.«term_⋆»', expected 'Set.Algebra.Star.Pointwise.term_⋆._@.Algebra.Star.Pointwise._hyg.8'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  Nonempty.star
  [ HasInvolutiveStar α ] { s : Set α } ( h : s . Nonempty ) : s ⋆ . Nonempty
  := nonempty_star . 2 h
#align set.nonempty.star Set.Nonempty.star

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
      (Command.declId `mem_star [])
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `HasStar [`α]) "]")]
       (Term.typeSpec
        ":"
        («term_↔_»
         («term_∈_» `a "∈" (Set.Algebra.Star.Pointwise.«term_⋆» `s "⋆"))
         "↔"
         («term_∈_» (Set.Algebra.Star.Pointwise.«term_⋆» `a "⋆") "∈" `s))))
      (Command.declValSimple ":=" `Iff.rfl [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Iff.rfl
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_↔_»
       («term_∈_» `a "∈" (Set.Algebra.Star.Pointwise.«term_⋆» `s "⋆"))
       "↔"
       («term_∈_» (Set.Algebra.Star.Pointwise.«term_⋆» `a "⋆") "∈" `s))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∈_» (Set.Algebra.Star.Pointwise.«term_⋆» `a "⋆") "∈" `s)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `s
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Set.Algebra.Star.Pointwise.«term_⋆» `a "⋆")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.Algebra.Star.Pointwise.«term_⋆»', expected 'Set.Algebra.Star.Pointwise.term_⋆._@.Algebra.Star.Pointwise._hyg.8'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ simp ] theorem mem_star [ HasStar α ] : a ∈ s ⋆ ↔ a ⋆ ∈ s := Iff.rfl
#align set.mem_star Set.mem_star

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `star_mem_star [])
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `HasInvolutiveStar [`α]) "]")]
       (Term.typeSpec
        ":"
        («term_↔_»
         («term_∈_»
          (Set.Algebra.Star.Pointwise.«term_⋆» `a "⋆")
          "∈"
          (Set.Algebra.Star.Pointwise.«term_⋆» `s "⋆"))
         "↔"
         («term_∈_» `a "∈" `s))))
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
            ["[" [(Tactic.simpLemma [] [] `mem_star) "," (Tactic.simpLemma [] [] `star_star)] "]"]
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
           ["[" [(Tactic.simpLemma [] [] `mem_star) "," (Tactic.simpLemma [] [] `star_star)] "]"]
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["[" [(Tactic.simpLemma [] [] `mem_star) "," (Tactic.simpLemma [] [] `star_star)] "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `star_star
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mem_star
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_↔_»
       («term_∈_»
        (Set.Algebra.Star.Pointwise.«term_⋆» `a "⋆")
        "∈"
        (Set.Algebra.Star.Pointwise.«term_⋆» `s "⋆"))
       "↔"
       («term_∈_» `a "∈" `s))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∈_» `a "∈" `s)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `s
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `a
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 21 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 20, term))
      («term_∈_»
       (Set.Algebra.Star.Pointwise.«term_⋆» `a "⋆")
       "∈"
       (Set.Algebra.Star.Pointwise.«term_⋆» `s "⋆"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Set.Algebra.Star.Pointwise.«term_⋆» `s "⋆")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.Algebra.Star.Pointwise.«term_⋆»', expected 'Set.Algebra.Star.Pointwise.term_⋆._@.Algebra.Star.Pointwise._hyg.8'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  star_mem_star
  [ HasInvolutiveStar α ] : a ⋆ ∈ s ⋆ ↔ a ∈ s
  := by simp only [ mem_star , star_star ]
#align set.star_mem_star Set.star_mem_star

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
      (Command.declId `star_preimage [])
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `HasStar [`α]) "]")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Set.Data.Set.Image.«term_⁻¹'_» `HasStar.star " ⁻¹' " `s)
         "="
         (Set.Algebra.Star.Pointwise.«term_⋆» `s "⋆"))))
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
       (Set.Data.Set.Image.«term_⁻¹'_» `HasStar.star " ⁻¹' " `s)
       "="
       (Set.Algebra.Star.Pointwise.«term_⋆» `s "⋆"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Set.Algebra.Star.Pointwise.«term_⋆» `s "⋆")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.Algebra.Star.Pointwise.«term_⋆»', expected 'Set.Algebra.Star.Pointwise.term_⋆._@.Algebra.Star.Pointwise._hyg.8'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ simp ] theorem star_preimage [ HasStar α ] : HasStar.star ⁻¹' s = s ⋆ := rfl
#align set.star_preimage Set.star_preimage

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
      (Command.declId `image_star [])
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `HasInvolutiveStar [`α]) "]")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Set.Data.Set.Image.term_''_ `HasStar.star " '' " `s)
         "="
         (Set.Algebra.Star.Pointwise.«term_⋆» `s "⋆"))))
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
            ["[" [(Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `star_preimage)] "]"]
            [])
           []
           (Tactic.«tactic_<;>_»
            (Tactic.«tactic_<;>_»
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `image_eq_preimage_of_inverse)] "]")
              [])
             "<;>"
             (Tactic.intro "intro" []))
            "<;>"
            (Tactic.simp
             "simp"
             []
             []
             ["only"]
             ["[" [(Tactic.simpLemma [] [] `star_star)] "]"]
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
         [(Tactic.simp
           "simp"
           []
           []
           ["only"]
           ["[" [(Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `star_preimage)] "]"]
           [])
          []
          (Tactic.«tactic_<;>_»
           (Tactic.«tactic_<;>_»
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `image_eq_preimage_of_inverse)] "]")
             [])
            "<;>"
            (Tactic.intro "intro" []))
           "<;>"
           (Tactic.simp
            "simp"
            []
            []
            ["only"]
            ["[" [(Tactic.simpLemma [] [] `star_star)] "]"]
            []))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.«tactic_<;>_»
       (Tactic.«tactic_<;>_»
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `image_eq_preimage_of_inverse)] "]")
         [])
        "<;>"
        (Tactic.intro "intro" []))
       "<;>"
       (Tactic.simp "simp" [] [] ["only"] ["[" [(Tactic.simpLemma [] [] `star_star)] "]"] []))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] ["only"] ["[" [(Tactic.simpLemma [] [] `star_star)] "]"] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `star_star
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 2 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
      (Tactic.«tactic_<;>_»
       (Tactic.rwSeq
        "rw"
        []
        (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `image_eq_preimage_of_inverse)] "]")
        [])
       "<;>"
       (Tactic.intro "intro" []))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.intro "intro" [])
[PrettyPrinter.parenthesize] ...precedences are 2 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `image_eq_preimage_of_inverse)] "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `image_eq_preimage_of_inverse
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["[" [(Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `star_preimage)] "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `star_preimage
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Set.Data.Set.Image.term_''_ `HasStar.star " '' " `s)
       "="
       (Set.Algebra.Star.Pointwise.«term_⋆» `s "⋆"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Set.Algebra.Star.Pointwise.«term_⋆» `s "⋆")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.Algebra.Star.Pointwise.«term_⋆»', expected 'Set.Algebra.Star.Pointwise.term_⋆._@.Algebra.Star.Pointwise._hyg.8'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ simp ]
  theorem
    image_star
    [ HasInvolutiveStar α ] : HasStar.star '' s = s ⋆
    :=
      by
        simp only [ ← star_preimage ]
          rw [ image_eq_preimage_of_inverse ] <;> intro <;> simp only [ star_star ]
#align set.image_star Set.image_star

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
      (Command.declId `inter_star [])
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `HasStar [`α]) "]")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Set.Algebra.Star.Pointwise.«term_⋆» («term_∩_» `s "∩" `t) "⋆")
         "="
         («term_∩_»
          (Set.Algebra.Star.Pointwise.«term_⋆» `s "⋆")
          "∩"
          (Set.Algebra.Star.Pointwise.«term_⋆» `t "⋆")))))
      (Command.declValSimple ":=" `preimage_inter [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `preimage_inter
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Set.Algebra.Star.Pointwise.«term_⋆» («term_∩_» `s "∩" `t) "⋆")
       "="
       («term_∩_»
        (Set.Algebra.Star.Pointwise.«term_⋆» `s "⋆")
        "∩"
        (Set.Algebra.Star.Pointwise.«term_⋆» `t "⋆")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∩_»
       (Set.Algebra.Star.Pointwise.«term_⋆» `s "⋆")
       "∩"
       (Set.Algebra.Star.Pointwise.«term_⋆» `t "⋆"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Set.Algebra.Star.Pointwise.«term_⋆» `t "⋆")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.Algebra.Star.Pointwise.«term_⋆»', expected 'Set.Algebra.Star.Pointwise.term_⋆._@.Algebra.Star.Pointwise._hyg.8'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ simp ] theorem inter_star [ HasStar α ] : s ∩ t ⋆ = s ⋆ ∩ t ⋆ := preimage_inter
#align set.inter_star Set.inter_star

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
      (Command.declId `union_star [])
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `HasStar [`α]) "]")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Set.Algebra.Star.Pointwise.«term_⋆» («term_∪_» `s "∪" `t) "⋆")
         "="
         («term_∪_»
          (Set.Algebra.Star.Pointwise.«term_⋆» `s "⋆")
          "∪"
          (Set.Algebra.Star.Pointwise.«term_⋆» `t "⋆")))))
      (Command.declValSimple ":=" `preimage_union [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `preimage_union
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Set.Algebra.Star.Pointwise.«term_⋆» («term_∪_» `s "∪" `t) "⋆")
       "="
       («term_∪_»
        (Set.Algebra.Star.Pointwise.«term_⋆» `s "⋆")
        "∪"
        (Set.Algebra.Star.Pointwise.«term_⋆» `t "⋆")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∪_»
       (Set.Algebra.Star.Pointwise.«term_⋆» `s "⋆")
       "∪"
       (Set.Algebra.Star.Pointwise.«term_⋆» `t "⋆"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Set.Algebra.Star.Pointwise.«term_⋆» `t "⋆")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.Algebra.Star.Pointwise.«term_⋆»', expected 'Set.Algebra.Star.Pointwise.term_⋆._@.Algebra.Star.Pointwise._hyg.8'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ simp ] theorem union_star [ HasStar α ] : s ∪ t ⋆ = s ⋆ ∪ t ⋆ := preimage_union
#align set.union_star Set.union_star

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
      (Command.declId `Inter_star [])
      (Command.declSig
       [(Term.implicitBinder "{" [`ι] [":" (Term.sort "Sort" [(Level.hole "_")])] "}")
        (Term.instBinder "[" [] (Term.app `HasStar [`α]) "]")
        (Term.explicitBinder "(" [`s] [":" (Term.arrow `ι "→" (Term.app `Set [`α]))] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Set.Algebra.Star.Pointwise.«term_⋆»
          (Set.Data.Set.Lattice.«term⋂_,_»
           "⋂"
           (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
           ", "
           (Term.app `s [`i]))
          "⋆")
         "="
         (Set.Data.Set.Lattice.«term⋂_,_»
          "⋂"
          (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
          ", "
          (Set.Algebra.Star.Pointwise.«term_⋆» (Term.app `s [`i]) "⋆")))))
      (Command.declValSimple ":=" `preimage_Inter [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `preimage_Inter
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Set.Algebra.Star.Pointwise.«term_⋆»
        (Set.Data.Set.Lattice.«term⋂_,_»
         "⋂"
         (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
         ", "
         (Term.app `s [`i]))
        "⋆")
       "="
       (Set.Data.Set.Lattice.«term⋂_,_»
        "⋂"
        (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
        ", "
        (Set.Algebra.Star.Pointwise.«term_⋆» (Term.app `s [`i]) "⋆")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Set.Data.Set.Lattice.«term⋂_,_»
       "⋂"
       (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
       ", "
       (Set.Algebra.Star.Pointwise.«term_⋆» (Term.app `s [`i]) "⋆"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Set.Algebra.Star.Pointwise.«term_⋆» (Term.app `s [`i]) "⋆")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.Algebra.Star.Pointwise.«term_⋆»', expected 'Set.Algebra.Star.Pointwise.term_⋆._@.Algebra.Star.Pointwise._hyg.8'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ simp ]
  theorem
    Inter_star
    { ι : Sort _ } [ HasStar α ] ( s : ι → Set α ) : ⋂ i , s i ⋆ = ⋂ i , s i ⋆
    := preimage_Inter
#align set.Inter_star Set.Inter_star

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
      (Command.declId `Union_star [])
      (Command.declSig
       [(Term.implicitBinder "{" [`ι] [":" (Term.sort "Sort" [(Level.hole "_")])] "}")
        (Term.instBinder "[" [] (Term.app `HasStar [`α]) "]")
        (Term.explicitBinder "(" [`s] [":" (Term.arrow `ι "→" (Term.app `Set [`α]))] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Set.Algebra.Star.Pointwise.«term_⋆»
          (Set.Data.Set.Lattice.«term⋃_,_»
           "⋃"
           (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
           ", "
           (Term.app `s [`i]))
          "⋆")
         "="
         (Set.Data.Set.Lattice.«term⋃_,_»
          "⋃"
          (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
          ", "
          (Set.Algebra.Star.Pointwise.«term_⋆» (Term.app `s [`i]) "⋆")))))
      (Command.declValSimple ":=" `preimage_Union [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `preimage_Union
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Set.Algebra.Star.Pointwise.«term_⋆»
        (Set.Data.Set.Lattice.«term⋃_,_»
         "⋃"
         (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
         ", "
         (Term.app `s [`i]))
        "⋆")
       "="
       (Set.Data.Set.Lattice.«term⋃_,_»
        "⋃"
        (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
        ", "
        (Set.Algebra.Star.Pointwise.«term_⋆» (Term.app `s [`i]) "⋆")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Set.Data.Set.Lattice.«term⋃_,_»
       "⋃"
       (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
       ", "
       (Set.Algebra.Star.Pointwise.«term_⋆» (Term.app `s [`i]) "⋆"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Set.Algebra.Star.Pointwise.«term_⋆» (Term.app `s [`i]) "⋆")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.Algebra.Star.Pointwise.«term_⋆»', expected 'Set.Algebra.Star.Pointwise.term_⋆._@.Algebra.Star.Pointwise._hyg.8'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ simp ]
  theorem
    Union_star
    { ι : Sort _ } [ HasStar α ] ( s : ι → Set α ) : ⋃ i , s i ⋆ = ⋃ i , s i ⋆
    := preimage_Union
#align set.Union_star Set.Union_star

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
      (Command.declId `compl_star [])
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `HasStar [`α]) "]")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Set.Algebra.Star.Pointwise.«term_⋆» (Order.Basic.«term_ᶜ» `s "ᶜ") "⋆")
         "="
         (Order.Basic.«term_ᶜ» (Set.Algebra.Star.Pointwise.«term_⋆» `s "⋆") "ᶜ"))))
      (Command.declValSimple ":=" `preimage_compl [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `preimage_compl
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Set.Algebra.Star.Pointwise.«term_⋆» (Order.Basic.«term_ᶜ» `s "ᶜ") "⋆")
       "="
       (Order.Basic.«term_ᶜ» (Set.Algebra.Star.Pointwise.«term_⋆» `s "⋆") "ᶜ"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Order.Basic.«term_ᶜ» (Set.Algebra.Star.Pointwise.«term_⋆» `s "⋆") "ᶜ")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 999, term))
      (Set.Algebra.Star.Pointwise.«term_⋆» `s "⋆")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.Algebra.Star.Pointwise.«term_⋆»', expected 'Set.Algebra.Star.Pointwise.term_⋆._@.Algebra.Star.Pointwise._hyg.8'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ simp ] theorem compl_star [ HasStar α ] : s ᶜ ⋆ = s ⋆ ᶜ := preimage_compl
#align set.compl_star Set.compl_star

@[simp]
instance [HasInvolutiveStar α] : HasInvolutiveStar (Set α)
    where
  star := HasStar.star
  star_involutive s := by simp only [← star_preimage, preimage_preimage, star_star, preimage_id']

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
      (Command.declId `star_subset_star [])
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `HasInvolutiveStar [`α]) "]")
        (Term.implicitBinder "{" [`s `t] [":" (Term.app `Set [`α])] "}")]
       (Term.typeSpec
        ":"
        («term_↔_»
         («term_⊆_»
          (Set.Algebra.Star.Pointwise.«term_⋆» `s "⋆")
          "⊆"
          (Set.Algebra.Star.Pointwise.«term_⋆» `t "⋆"))
         "↔"
         («term_⊆_» `s "⊆" `t))))
      (Command.declValSimple
       ":="
       (Term.proj (Term.proj `Equiv.star "." `Surjective) "." `preimage_subset_preimage_iff)
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.proj `Equiv.star "." `Surjective) "." `preimage_subset_preimage_iff)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj `Equiv.star "." `Surjective)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `Equiv.star
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_↔_»
       («term_⊆_»
        (Set.Algebra.Star.Pointwise.«term_⋆» `s "⋆")
        "⊆"
        (Set.Algebra.Star.Pointwise.«term_⋆» `t "⋆"))
       "↔"
       («term_⊆_» `s "⊆" `t))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_⊆_» `s "⊆" `t)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `t
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `s
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 21 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 20, term))
      («term_⊆_»
       (Set.Algebra.Star.Pointwise.«term_⋆» `s "⋆")
       "⊆"
       (Set.Algebra.Star.Pointwise.«term_⋆» `t "⋆"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Set.Algebra.Star.Pointwise.«term_⋆» `t "⋆")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.Algebra.Star.Pointwise.«term_⋆»', expected 'Set.Algebra.Star.Pointwise.term_⋆._@.Algebra.Star.Pointwise._hyg.8'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ simp ]
  theorem
    star_subset_star
    [ HasInvolutiveStar α ] { s t : Set α } : s ⋆ ⊆ t ⋆ ↔ s ⊆ t
    := Equiv.star . Surjective . preimage_subset_preimage_iff
#align set.star_subset_star Set.star_subset_star

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `star_subset [])
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `HasInvolutiveStar [`α]) "]")
        (Term.implicitBinder "{" [`s `t] [":" (Term.app `Set [`α])] "}")]
       (Term.typeSpec
        ":"
        («term_↔_»
         («term_⊆_» (Set.Algebra.Star.Pointwise.«term_⋆» `s "⋆") "⊆" `t)
         "↔"
         («term_⊆_» `s "⊆" (Set.Algebra.Star.Pointwise.«term_⋆» `t "⋆")))))
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
             [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `star_subset_star)
              ","
              (Tactic.rwRule [] `star_star)]
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
            [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `star_subset_star)
             ","
             (Tactic.rwRule [] `star_star)]
            "]")
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `star_subset_star)
         ","
         (Tactic.rwRule [] `star_star)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `star_star
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `star_subset_star
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_↔_»
       («term_⊆_» (Set.Algebra.Star.Pointwise.«term_⋆» `s "⋆") "⊆" `t)
       "↔"
       («term_⊆_» `s "⊆" (Set.Algebra.Star.Pointwise.«term_⋆» `t "⋆")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_⊆_» `s "⊆" (Set.Algebra.Star.Pointwise.«term_⋆» `t "⋆"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Set.Algebra.Star.Pointwise.«term_⋆» `t "⋆")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.Algebra.Star.Pointwise.«term_⋆»', expected 'Set.Algebra.Star.Pointwise.term_⋆._@.Algebra.Star.Pointwise._hyg.8'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  star_subset
  [ HasInvolutiveStar α ] { s t : Set α } : s ⋆ ⊆ t ↔ s ⊆ t ⋆
  := by rw [ ← star_subset_star , star_star ]
#align set.star_subset Set.star_subset

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `Finite.star [])
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `HasInvolutiveStar [`α]) "]")
        (Term.implicitBinder "{" [`s] [":" (Term.app `Set [`α])] "}")
        (Term.explicitBinder "(" [`hs] [":" (Term.proj `s "." `Finite)] [] ")")]
       (Term.typeSpec ":" (Term.proj (Set.Algebra.Star.Pointwise.«term_⋆» `s "⋆") "." `Finite)))
      (Command.declValSimple
       ":="
       («term_<|_»
        (Term.proj `hs "." `Preimage)
        "<|"
        (Term.app (Term.proj `star_injective "." `InjOn) [(Term.hole "_")]))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_»
       (Term.proj `hs "." `Preimage)
       "<|"
       (Term.app (Term.proj `star_injective "." `InjOn) [(Term.hole "_")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj `star_injective "." `InjOn) [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `star_injective "." `InjOn)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `star_injective
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      (Term.proj `hs "." `Preimage)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hs
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 10, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.proj (Set.Algebra.Star.Pointwise.«term_⋆» `s "⋆") "." `Finite)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Set.Algebra.Star.Pointwise.«term_⋆» `s "⋆")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.Algebra.Star.Pointwise.«term_⋆»', expected 'Set.Algebra.Star.Pointwise.term_⋆._@.Algebra.Star.Pointwise._hyg.8'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  Finite.star
  [ HasInvolutiveStar α ] { s : Set α } ( hs : s . Finite ) : s ⋆ . Finite
  := hs . Preimage <| star_injective . InjOn _
#align set.finite.star Set.Finite.star

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `star_singleton [])
      (Command.declSig
       [(Term.implicitBinder "{" [`β] [":" (Term.type "Type" [(Level.hole "_")])] "}")
        (Term.instBinder "[" [] (Term.app `HasInvolutiveStar [`β]) "]")
        (Term.explicitBinder "(" [`x] [":" `β] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Set.Algebra.Star.Pointwise.«term_⋆»
          (Term.typeAscription "(" («term{_}» "{" [`x] "}") ":" [(Term.app `Set [`β])] ")")
          "⋆")
         "="
         («term{_}» "{" [(Set.Algebra.Star.Pointwise.«term_⋆» `x "⋆")] "}"))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Std.Tactic.Ext.tacticExt1___
            "ext1"
            [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `y))])
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [] `mem_star)
              ","
              (Tactic.rwRule [] `mem_singleton_iff)
              ","
              (Tactic.rwRule [] `mem_singleton_iff)
              ","
              (Tactic.rwRule [] `star_eq_iff_star_eq)
              ","
              (Tactic.rwRule [] `eq_comm)]
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
         [(Std.Tactic.Ext.tacticExt1___
           "ext1"
           [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `y))])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `mem_star)
             ","
             (Tactic.rwRule [] `mem_singleton_iff)
             ","
             (Tactic.rwRule [] `mem_singleton_iff)
             ","
             (Tactic.rwRule [] `star_eq_iff_star_eq)
             ","
             (Tactic.rwRule [] `eq_comm)]
            "]")
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `mem_star)
         ","
         (Tactic.rwRule [] `mem_singleton_iff)
         ","
         (Tactic.rwRule [] `mem_singleton_iff)
         ","
         (Tactic.rwRule [] `star_eq_iff_star_eq)
         ","
         (Tactic.rwRule [] `eq_comm)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `eq_comm
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `star_eq_iff_star_eq
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mem_singleton_iff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mem_singleton_iff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mem_star
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Ext.tacticExt1___
       "ext1"
       [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `y))])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Set.Algebra.Star.Pointwise.«term_⋆»
        (Term.typeAscription "(" («term{_}» "{" [`x] "}") ":" [(Term.app `Set [`β])] ")")
        "⋆")
       "="
       («term{_}» "{" [(Set.Algebra.Star.Pointwise.«term_⋆» `x "⋆")] "}"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term{_}» "{" [(Set.Algebra.Star.Pointwise.«term_⋆» `x "⋆")] "}")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Set.Algebra.Star.Pointwise.«term_⋆» `x "⋆")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.Algebra.Star.Pointwise.«term_⋆»', expected 'Set.Algebra.Star.Pointwise.term_⋆._@.Algebra.Star.Pointwise._hyg.8'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  star_singleton
  { β : Type _ } [ HasInvolutiveStar β ] ( x : β ) : ( { x } : Set β ) ⋆ = { x ⋆ }
  :=
    by
      ext1 y rw [ mem_star , mem_singleton_iff , mem_singleton_iff , star_eq_iff_star_eq , eq_comm ]
#align set.star_singleton Set.star_singleton

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [(Command.protected "protected")] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `star_mul [])
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `Monoid [`α]) "]")
        (Term.instBinder "[" [] (Term.app `StarSemigroup [`α]) "]")
        (Term.explicitBinder "(" [`s `t] [":" (Term.app `Set [`α])] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Set.Algebra.Star.Pointwise.«term_⋆» («term_*_» `s "*" `t) "⋆")
         "="
         («term_*_»
          (Set.Algebra.Star.Pointwise.«term_⋆» `t "⋆")
          "*"
          (Set.Algebra.Star.Pointwise.«term_⋆» `s "⋆")))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Mathlib.Tactic.tacticSimp_rw__
            "simp_rw"
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `image_star)
              ","
              (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `image2_mul)
              ","
              (Tactic.rwRule [] `image_image2)
              ","
              (Tactic.rwRule [] `image2_image_left)
              ","
              (Tactic.rwRule [] `image2_image_right)
              ","
              (Tactic.rwRule [] `star_mul)
              ","
              (Tactic.rwRule [] (Term.app `image2_swap [(Term.hole "_") `s `t]))]
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
         [(Mathlib.Tactic.tacticSimp_rw__
           "simp_rw"
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `image_star)
             ","
             (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `image2_mul)
             ","
             (Tactic.rwRule [] `image_image2)
             ","
             (Tactic.rwRule [] `image2_image_left)
             ","
             (Tactic.rwRule [] `image2_image_right)
             ","
             (Tactic.rwRule [] `star_mul)
             ","
             (Tactic.rwRule [] (Term.app `image2_swap [(Term.hole "_") `s `t]))]
            "]")
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.tacticSimp_rw__
       "simp_rw"
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `image_star)
         ","
         (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `image2_mul)
         ","
         (Tactic.rwRule [] `image_image2)
         ","
         (Tactic.rwRule [] `image2_image_left)
         ","
         (Tactic.rwRule [] `image2_image_right)
         ","
         (Tactic.rwRule [] `star_mul)
         ","
         (Tactic.rwRule [] (Term.app `image2_swap [(Term.hole "_") `s `t]))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `image2_swap [(Term.hole "_") `s `t])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `t
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `s
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `image2_swap
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `star_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `image2_image_right
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `image2_image_left
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `image_image2
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `image2_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `image_star
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Set.Algebra.Star.Pointwise.«term_⋆» («term_*_» `s "*" `t) "⋆")
       "="
       («term_*_»
        (Set.Algebra.Star.Pointwise.«term_⋆» `t "⋆")
        "*"
        (Set.Algebra.Star.Pointwise.«term_⋆» `s "⋆")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_»
       (Set.Algebra.Star.Pointwise.«term_⋆» `t "⋆")
       "*"
       (Set.Algebra.Star.Pointwise.«term_⋆» `s "⋆"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Set.Algebra.Star.Pointwise.«term_⋆» `s "⋆")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.Algebra.Star.Pointwise.«term_⋆»', expected 'Set.Algebra.Star.Pointwise.term_⋆._@.Algebra.Star.Pointwise._hyg.8'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
protected
  theorem
    star_mul
    [ Monoid α ] [ StarSemigroup α ] ( s t : Set α ) : s * t ⋆ = t ⋆ * s ⋆
    :=
      by
        simp_rw
          [
            ← image_star
              ,
              ← image2_mul
              ,
              image_image2
              ,
              image2_image_left
              ,
              image2_image_right
              ,
              star_mul
              ,
              image2_swap _ s t
            ]
#align set.star_mul Set.star_mul

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [(Command.protected "protected")] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `star_add [])
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `AddMonoid [`α]) "]")
        (Term.instBinder "[" [] (Term.app `StarAddMonoid [`α]) "]")
        (Term.explicitBinder "(" [`s `t] [":" (Term.app `Set [`α])] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Set.Algebra.Star.Pointwise.«term_⋆» («term_+_» `s "+" `t) "⋆")
         "="
         («term_+_»
          (Set.Algebra.Star.Pointwise.«term_⋆» `s "⋆")
          "+"
          (Set.Algebra.Star.Pointwise.«term_⋆» `t "⋆")))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Mathlib.Tactic.tacticSimp_rw__
            "simp_rw"
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `image_star)
              ","
              (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `image2_add)
              ","
              (Tactic.rwRule [] `image_image2)
              ","
              (Tactic.rwRule [] `image2_image_left)
              ","
              (Tactic.rwRule [] `image2_image_right)
              ","
              (Tactic.rwRule [] `star_add)]
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
         [(Mathlib.Tactic.tacticSimp_rw__
           "simp_rw"
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `image_star)
             ","
             (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `image2_add)
             ","
             (Tactic.rwRule [] `image_image2)
             ","
             (Tactic.rwRule [] `image2_image_left)
             ","
             (Tactic.rwRule [] `image2_image_right)
             ","
             (Tactic.rwRule [] `star_add)]
            "]")
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.tacticSimp_rw__
       "simp_rw"
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `image_star)
         ","
         (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `image2_add)
         ","
         (Tactic.rwRule [] `image_image2)
         ","
         (Tactic.rwRule [] `image2_image_left)
         ","
         (Tactic.rwRule [] `image2_image_right)
         ","
         (Tactic.rwRule [] `star_add)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `star_add
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `image2_image_right
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `image2_image_left
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `image_image2
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `image2_add
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `image_star
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Set.Algebra.Star.Pointwise.«term_⋆» («term_+_» `s "+" `t) "⋆")
       "="
       («term_+_»
        (Set.Algebra.Star.Pointwise.«term_⋆» `s "⋆")
        "+"
        (Set.Algebra.Star.Pointwise.«term_⋆» `t "⋆")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_»
       (Set.Algebra.Star.Pointwise.«term_⋆» `s "⋆")
       "+"
       (Set.Algebra.Star.Pointwise.«term_⋆» `t "⋆"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Set.Algebra.Star.Pointwise.«term_⋆» `t "⋆")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.Algebra.Star.Pointwise.«term_⋆»', expected 'Set.Algebra.Star.Pointwise.term_⋆._@.Algebra.Star.Pointwise._hyg.8'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
protected
  theorem
    star_add
    [ AddMonoid α ] [ StarAddMonoid α ] ( s t : Set α ) : s + t ⋆ = s ⋆ + t ⋆
    :=
      by
        simp_rw
          [
            ← image_star
              ,
              ← image2_add
              ,
              image_image2
              ,
              image2_image_left
              ,
              image2_image_right
              ,
              star_add
            ]
#align set.star_add Set.star_add

@[simp]
instance [HasStar α] [HasTrivialStar α] : HasTrivialStar (Set α)
    where star_trivial s := by
    rw [← star_preimage]
    ext1
    simp [star_trivial]

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [(Command.protected "protected")] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `star_inv [])
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `Group [`α]) "]")
        (Term.instBinder "[" [] (Term.app `StarSemigroup [`α]) "]")
        (Term.explicitBinder "(" [`s] [":" (Term.app `Set [`α])] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Set.Algebra.Star.Pointwise.«term_⋆» («term_⁻¹» `s "⁻¹") "⋆")
         "="
         («term_⁻¹» (Set.Algebra.Star.Pointwise.«term_⋆» `s "⋆") "⁻¹"))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Std.Tactic.Ext.«tacticExt___:_» "ext" [] [])
           []
           (Tactic.simp
            "simp"
            []
            []
            ["only"]
            ["["
             [(Tactic.simpLemma [] [] `mem_star)
              ","
              (Tactic.simpLemma [] [] `mem_inv)
              ","
              (Tactic.simpLemma [] [] `star_inv)]
             "]"]
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
         [(Std.Tactic.Ext.«tacticExt___:_» "ext" [] [])
          []
          (Tactic.simp
           "simp"
           []
           []
           ["only"]
           ["["
            [(Tactic.simpLemma [] [] `mem_star)
             ","
             (Tactic.simpLemma [] [] `mem_inv)
             ","
             (Tactic.simpLemma [] [] `star_inv)]
            "]"]
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["["
        [(Tactic.simpLemma [] [] `mem_star)
         ","
         (Tactic.simpLemma [] [] `mem_inv)
         ","
         (Tactic.simpLemma [] [] `star_inv)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `star_inv
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mem_inv
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mem_star
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Ext.«tacticExt___:_» "ext" [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Set.Algebra.Star.Pointwise.«term_⋆» («term_⁻¹» `s "⁻¹") "⋆")
       "="
       («term_⁻¹» (Set.Algebra.Star.Pointwise.«term_⋆» `s "⋆") "⁻¹"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_⁻¹» (Set.Algebra.Star.Pointwise.«term_⋆» `s "⋆") "⁻¹")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Set.Algebra.Star.Pointwise.«term_⋆» `s "⋆")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.Algebra.Star.Pointwise.«term_⋆»', expected 'Set.Algebra.Star.Pointwise.term_⋆._@.Algebra.Star.Pointwise._hyg.8'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
protected
  theorem
    star_inv
    [ Group α ] [ StarSemigroup α ] ( s : Set α ) : s ⁻¹ ⋆ = s ⋆ ⁻¹
    := by ext simp only [ mem_star , mem_inv , star_inv ]
#align set.star_inv Set.star_inv

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [(Command.protected "protected")] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `star_inv' [])
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `DivisionRing [`α]) "]")
        (Term.instBinder "[" [] (Term.app `StarRing [`α]) "]")
        (Term.explicitBinder "(" [`s] [":" (Term.app `Set [`α])] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Set.Algebra.Star.Pointwise.«term_⋆» («term_⁻¹» `s "⁻¹") "⋆")
         "="
         («term_⁻¹» (Set.Algebra.Star.Pointwise.«term_⋆» `s "⋆") "⁻¹"))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Std.Tactic.Ext.«tacticExt___:_» "ext" [] [])
           []
           (Tactic.simp
            "simp"
            []
            []
            ["only"]
            ["["
             [(Tactic.simpLemma [] [] `mem_star)
              ","
              (Tactic.simpLemma [] [] `mem_inv)
              ","
              (Tactic.simpLemma [] [] `star_inv')]
             "]"]
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
         [(Std.Tactic.Ext.«tacticExt___:_» "ext" [] [])
          []
          (Tactic.simp
           "simp"
           []
           []
           ["only"]
           ["["
            [(Tactic.simpLemma [] [] `mem_star)
             ","
             (Tactic.simpLemma [] [] `mem_inv)
             ","
             (Tactic.simpLemma [] [] `star_inv')]
            "]"]
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["["
        [(Tactic.simpLemma [] [] `mem_star)
         ","
         (Tactic.simpLemma [] [] `mem_inv)
         ","
         (Tactic.simpLemma [] [] `star_inv')]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `star_inv'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mem_inv
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mem_star
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Ext.«tacticExt___:_» "ext" [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Set.Algebra.Star.Pointwise.«term_⋆» («term_⁻¹» `s "⁻¹") "⋆")
       "="
       («term_⁻¹» (Set.Algebra.Star.Pointwise.«term_⋆» `s "⋆") "⁻¹"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_⁻¹» (Set.Algebra.Star.Pointwise.«term_⋆» `s "⋆") "⁻¹")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Set.Algebra.Star.Pointwise.«term_⋆» `s "⋆")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.Algebra.Star.Pointwise.«term_⋆»', expected 'Set.Algebra.Star.Pointwise.term_⋆._@.Algebra.Star.Pointwise._hyg.8'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
protected
  theorem
    star_inv'
    [ DivisionRing α ] [ StarRing α ] ( s : Set α ) : s ⁻¹ ⋆ = s ⋆ ⁻¹
    := by ext simp only [ mem_star , mem_inv , star_inv' ]
#align set.star_inv' Set.star_inv'

end Set

