/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang

! This file was ported from Lean 3 source module algebra.category.Group.epi_mono
! leanprover-community/mathlib commit 6afc9b06856ad973f6a2619e3e8a0a8d537a58f2
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Category.GroupCat.EquivalenceGroupAddGroup
import Mathbin.GroupTheory.QuotientGroup

/-!
# Monomorphisms and epimorphisms in `Group`
In this file, we prove monomorphisms in category of group are injective homomorphisms and
epimorphisms are surjective homomorphisms.
-/


noncomputable section

universe u v

namespace MonoidHom

open QuotientGroup

variable {A : Type u} {B : Type v}

section

variable [Group A] [Group B]

@[to_additive AddMonoidHom.ker_eq_bot_of_cancel]
theorem ker_eq_bot_of_cancel {f : A →* B} (h : ∀ u v : f.ker →* A, f.comp u = f.comp v → u = v) :
    f.ker = ⊥ := by simpa using _root_.congr_arg range (h f.ker.subtype 1 (by tidy))
#align monoid_hom.ker_eq_bot_of_cancel MonoidHom.ker_eq_bot_of_cancel

end

section

variable [CommGroup A] [CommGroup B]

@[to_additive AddMonoidHom.range_eq_top_of_cancel]
theorem range_eq_top_of_cancel {f : A →* B}
    (h : ∀ u v : B →* B ⧸ f.range, u.comp f = v.comp f → u = v) : f.range = ⊤ :=
  by
  specialize h 1 (QuotientGroup.mk' _) _
  · ext1
    simp only [one_apply, coe_comp, coe_mk', Function.comp_apply]
    rw [show (1 : B ⧸ f.range) = (1 : B) from QuotientGroup.coe_one _, QuotientGroup.eq, inv_one,
      one_mul]
    exact ⟨x, rfl⟩
  replace h : (QuotientGroup.mk' _).ker = (1 : B →* B ⧸ f.range).ker := by rw [h]
  rwa [ker_one, QuotientGroup.ker_mk] at h
#align monoid_hom.range_eq_top_of_cancel MonoidHom.range_eq_top_of_cancel

end

end MonoidHom

section

open CategoryTheory

namespace GroupCat

variable {A B : GroupCat.{u}} (f : A ⟶ B)

@[to_additive AddGroupCat.ker_eq_bot_of_mono]
theorem ker_eq_bot_of_mono [Mono f] : f.ker = ⊥ :=
  MonoidHom.ker_eq_bot_of_cancel fun u v =>
    (@cancel_mono _ _ _ _ _ f _ (show GroupCat.of f.ker ⟶ A from u) _).1
#align Group.ker_eq_bot_of_mono GroupCat.ker_eq_bot_of_mono

@[to_additive AddGroupCat.mono_iff_ker_eq_bot]
theorem mono_iff_ker_eq_bot : Mono f ↔ f.ker = ⊥ :=
  ⟨fun h => @ker_eq_bot_of_mono f h, fun h =>
    ConcreteCategory.mono_of_injective _ <| (MonoidHom.ker_eq_bot_iff f).1 h⟩
#align Group.mono_iff_ker_eq_bot GroupCat.mono_iff_ker_eq_bot

@[to_additive AddGroupCat.mono_iff_injective]
theorem mono_iff_injective : Mono f ↔ Function.Injective f :=
  Iff.trans (mono_iff_ker_eq_bot f) <| MonoidHom.ker_eq_bot_iff f
#align Group.mono_iff_injective GroupCat.mono_iff_injective

namespace SurjectiveOfEpiAuxs

-- mathport name: exprX
local notation "X" => Set.range (Function.swap leftCoset f.range.carrier)

/-- Define `X'` to be the set of all left cosets with an extra point at "infinity".
-/
@[nolint has_nonempty_instance]
inductive XWithInfinity
  | from_coset : Set.range (Function.swap leftCoset f.range.carrier) → X_with_infinity
  | infinity : X_with_infinity
#align Group.surjective_of_epi_auxs.X_with_infinity GroupCat.SurjectiveOfEpiAuxs.XWithInfinity

open XWithInfinity Equiv.Perm

open Coset

-- mathport name: exprX'
local notation "X'" => XWithInfinity f

-- mathport name: «expr∞»
local notation "∞" => XWithInfinity.infinity

-- mathport name: exprSX'
/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.notation
     []
     []
     (Term.attrKind [(Term.local "local")])
     "notation"
     []
     []
     []
     [(str "\"SX'\"")]
     "=>"
     (Term.app
      `Equiv.Perm
      [(GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.termX' "X'")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Equiv.Perm
       [(GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.termX' "X'")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.termX'', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.termX'', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.termX' "X'")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.termX'', expected 'GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.termX'._@.Algebra.Category.GroupCat.EpiMono._hyg.1283'-/-- failed to format: format: uncaught backtrack exception
local notation "SX'" => Equiv.Perm X'

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.instance
      (Term.attrKind [])
      "instance"
      []
      []
      (Command.declSig
       []
       (Term.typeSpec
        ":"
        (Term.app
         `HasSmul
         [`B (GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.termX' "X'")])))
      (Command.whereStructInst
       "where"
       [(Command.whereStructField
         (Term.letDecl
          (Term.letIdDecl
           `smul
           [`b `x]
           []
           ":="
           (Term.match
            "match"
            []
            []
            [(Term.matchDiscr [] `x)]
            "with"
            (Term.matchAlts
             [(Term.matchAlt
               "|"
               [[(Term.app `from_coset [`y])]]
               "=>"
               (Term.app
                `from_coset
                [(Term.anonymousCtor
                  "⟨"
                  [(Coset.GroupTheory.Coset.left_coset `b " *l " `y)
                   ","
                   (Term.byTactic
                    "by"
                    (Tactic.tacticSeq
                     (Tactic.tacticSeq1Indented
                      [(Tactic.rwSeq
                        "rw"
                        []
                        (Tactic.rwRuleSeq
                         "["
                         [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Subtype.val_eq_coe)
                          ","
                          (Tactic.rwRule
                           [(patternIgnore (token.«← » "←"))]
                           (Term.proj (Term.proj `y "." (fieldIdx "2")) "." `some_spec))
                          ","
                          (Tactic.rwRule [] `left_coset_assoc)]
                         "]")
                        [])
                       []
                       (Mathlib.Tactic.«tacticUse_,,»
                        "use"
                        [(«term_*_»
                          `b
                          "*"
                          (Term.proj (Term.proj `y "." (fieldIdx "2")) "." `some))])])))]
                  "⟩")]))
              (Term.matchAlt
               "|"
               [[(GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.«term∞» "∞")]]
               "=>"
               (GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.«term∞» "∞"))])))))]
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.whereStructInst', expected 'Lean.Parser.Command.declValSimple'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.whereStructInst', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.match
       "match"
       []
       []
       [(Term.matchDiscr [] `x)]
       "with"
       (Term.matchAlts
        [(Term.matchAlt
          "|"
          [[(Term.app `from_coset [`y])]]
          "=>"
          (Term.app
           `from_coset
           [(Term.anonymousCtor
             "⟨"
             [(Coset.GroupTheory.Coset.left_coset `b " *l " `y)
              ","
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Tactic.rwSeq
                   "rw"
                   []
                   (Tactic.rwRuleSeq
                    "["
                    [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Subtype.val_eq_coe)
                     ","
                     (Tactic.rwRule
                      [(patternIgnore (token.«← » "←"))]
                      (Term.proj (Term.proj `y "." (fieldIdx "2")) "." `some_spec))
                     ","
                     (Tactic.rwRule [] `left_coset_assoc)]
                    "]")
                   [])
                  []
                  (Mathlib.Tactic.«tacticUse_,,»
                   "use"
                   [(«term_*_»
                     `b
                     "*"
                     (Term.proj (Term.proj `y "." (fieldIdx "2")) "." `some))])])))]
             "⟩")]))
         (Term.matchAlt
          "|"
          [[(GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.«term∞» "∞")]]
          "=>"
          (GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.«term∞» "∞"))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.«term∞» "∞")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.«term∞»', expected 'GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.term∞._@.Algebra.Category.GroupCat.EpiMono._hyg.1797'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letIdDecl', expected 'Lean.Parser.Term.letPatDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letIdDecl', expected 'Lean.Parser.Term.letEqnsDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
instance
  : HasSmul B X'
  where
    smul
      b x
      :=
      match
        x
        with
        |
            from_coset y
            =>
            from_coset
              ⟨
                b *l y
                  ,
                  by
                    rw [ ← Subtype.val_eq_coe , ← y . 2 . some_spec , left_coset_assoc ]
                      use b * y . 2 . some
                ⟩
          | ∞ => ∞

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `mul_smul [])
      (Command.declSig
       [(Term.explicitBinder "(" [`b `b'] [":" `B] [] ")")
        (Term.explicitBinder
         "("
         [`x]
         [":" (GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.termX' "X'")]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Algebra.Group.Defs.«term_•_» («term_*_» `b "*" `b') " • " `x)
         "="
         (Algebra.Group.Defs.«term_•_» `b " • " (Algebra.Group.Defs.«term_•_» `b' " • " `x)))))
      (Command.declValSimple
       ":="
       (Term.match
        "match"
        []
        []
        [(Term.matchDiscr [] `x)]
        "with"
        (Term.matchAlts
         [(Term.matchAlt
           "|"
           [[(Term.app `from_coset [`y])]]
           "=>"
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.change
                "change"
                («term_=_»
                 (Term.app `from_coset [(Term.hole "_")])
                 "="
                 (Term.app `from_coset [(Term.hole "_")]))
                [])
               []
               (Tactic.simp
                "simp"
                []
                []
                ["only"]
                ["["
                 [(Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `Subtype.val_eq_coe)
                  ","
                  (Tactic.simpLemma [] [] `left_coset_assoc)]
                 "]"]
                [])]))))
          (Term.matchAlt
           "|"
           [[(GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.«term∞» "∞")]]
           "=>"
           `rfl)]))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.match
       "match"
       []
       []
       [(Term.matchDiscr [] `x)]
       "with"
       (Term.matchAlts
        [(Term.matchAlt
          "|"
          [[(Term.app `from_coset [`y])]]
          "=>"
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(Tactic.change
               "change"
               («term_=_»
                (Term.app `from_coset [(Term.hole "_")])
                "="
                (Term.app `from_coset [(Term.hole "_")]))
               [])
              []
              (Tactic.simp
               "simp"
               []
               []
               ["only"]
               ["["
                [(Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `Subtype.val_eq_coe)
                 ","
                 (Tactic.simpLemma [] [] `left_coset_assoc)]
                "]"]
               [])]))))
         (Term.matchAlt
          "|"
          [[(GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.«term∞» "∞")]]
          "=>"
          `rfl)]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rfl
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.«term∞» "∞")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.«term∞»', expected 'GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.term∞._@.Algebra.Category.GroupCat.EpiMono._hyg.1797'
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
  mul_smul
  ( b b' : B ) ( x : X' ) : b * b' • x = b • b' • x
  :=
    match
      x
      with
      |
          from_coset y
          =>
          by
            change from_coset _ = from_coset _ simp only [ ← Subtype.val_eq_coe , left_coset_assoc ]
        | ∞ => rfl
#align Group.surjective_of_epi_auxs.mul_smul GroupCat.SurjectiveOfEpiAuxs.mul_smul

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `one_smul [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`x]
         [":" (GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.termX' "X'")]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Algebra.Group.Defs.«term_•_» (Term.typeAscription "(" (num "1") ":" [`B] ")") " • " `x)
         "="
         `x)))
      (Command.declValSimple
       ":="
       (Term.match
        "match"
        []
        []
        [(Term.matchDiscr [] `x)]
        "with"
        (Term.matchAlts
         [(Term.matchAlt
           "|"
           [[(Term.app `from_coset [`y])]]
           "=>"
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.change
                "change"
                («term_=_»
                 (Term.app `from_coset [(Term.hole "_")])
                 "="
                 (Term.app `from_coset [(Term.hole "_")]))
                [])
               []
               (Tactic.simp
                "simp"
                []
                []
                ["only"]
                ["["
                 [(Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `Subtype.val_eq_coe)
                  ","
                  (Tactic.simpLemma [] [] `one_left_coset)
                  ","
                  (Tactic.simpLemma [] [] `Subtype.ext_iff_val)]
                 "]"]
                [])]))))
          (Term.matchAlt
           "|"
           [[(GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.«term∞» "∞")]]
           "=>"
           `rfl)]))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.match
       "match"
       []
       []
       [(Term.matchDiscr [] `x)]
       "with"
       (Term.matchAlts
        [(Term.matchAlt
          "|"
          [[(Term.app `from_coset [`y])]]
          "=>"
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(Tactic.change
               "change"
               («term_=_»
                (Term.app `from_coset [(Term.hole "_")])
                "="
                (Term.app `from_coset [(Term.hole "_")]))
               [])
              []
              (Tactic.simp
               "simp"
               []
               []
               ["only"]
               ["["
                [(Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `Subtype.val_eq_coe)
                 ","
                 (Tactic.simpLemma [] [] `one_left_coset)
                 ","
                 (Tactic.simpLemma [] [] `Subtype.ext_iff_val)]
                "]"]
               [])]))))
         (Term.matchAlt
          "|"
          [[(GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.«term∞» "∞")]]
          "=>"
          `rfl)]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rfl
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.«term∞» "∞")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.«term∞»', expected 'GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.term∞._@.Algebra.Category.GroupCat.EpiMono._hyg.1797'
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
  one_smul
  ( x : X' ) : ( 1 : B ) • x = x
  :=
    match
      x
      with
      |
          from_coset y
          =>
          by
            change from_coset _ = from_coset _
              simp only [ ← Subtype.val_eq_coe , one_left_coset , Subtype.ext_iff_val ]
        | ∞ => rfl
#align Group.surjective_of_epi_auxs.one_smul GroupCat.SurjectiveOfEpiAuxs.one_smul

theorem from_coset_eq_of_mem_range {b : B} (hb : b ∈ f.range) :
    from_coset ⟨b *l f.range.carrier, ⟨b, rfl⟩⟩ =
      from_coset ⟨f.range.carrier, ⟨1, one_left_coset _⟩⟩ :=
  by
  congr
  change b *l f.range = f.range
  nth_rw 2 [show (f.range : Set B) = 1 *l f.range from (one_left_coset _).symm]
  rw [left_coset_eq_iff, mul_one]
  exact Subgroup.inv_mem _ hb
#align
  Group.surjective_of_epi_auxs.from_coset_eq_of_mem_range GroupCat.SurjectiveOfEpiAuxs.from_coset_eq_of_mem_range

theorem from_coset_ne_of_nin_range {b : B} (hb : b ∉ f.range) :
    from_coset ⟨b *l f.range.carrier, ⟨b, rfl⟩⟩ ≠
      from_coset ⟨f.range.carrier, ⟨1, one_left_coset _⟩⟩ :=
  by
  intro r
  simp only [Subtype.mk_eq_mk] at r
  change b *l f.range = f.range at r
  nth_rw 2 [show (f.range : Set B) = 1 *l f.range from (one_left_coset _).symm] at r
  rw [left_coset_eq_iff, mul_one] at r
  exact hb (inv_inv b ▸ Subgroup.inv_mem _ r)
#align
  Group.surjective_of_epi_auxs.from_coset_ne_of_nin_range GroupCat.SurjectiveOfEpiAuxs.from_coset_ne_of_nin_range

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.instance
      (Term.attrKind [])
      "instance"
      []
      []
      (Command.declSig
       []
       (Term.typeSpec
        ":"
        (Term.app
         `DecidableEq
         [(GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.termX' "X'")])))
      (Command.declValSimple ":=" (Term.app `Classical.decEq [(Term.hole "_")]) [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Classical.decEq [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Classical.decEq
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app
       `DecidableEq
       [(GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.termX' "X'")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.termX'', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.termX'', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.termX' "X'")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.termX'', expected 'GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.termX'._@.Algebra.Category.GroupCat.EpiMono._hyg.1283'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
instance : DecidableEq X' := Classical.decEq _

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "Let `τ` be the permutation on `X'` exchanging `f.range` and the point at infinity.\n-/")]
      []
      []
      [(Command.noncomputable "noncomputable")]
      []
      [])
     (Command.def
      "def"
      (Command.declId `tau [])
      (Command.optDeclSig
       []
       [(Term.typeSpec
         ":"
         (GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.termSX' "SX'"))])
      (Command.declValSimple
       ":="
       (Term.app
        `Equiv.swap
        [(Term.app
          `from_coset
          [(Term.anonymousCtor
            "⟨"
            [(Term.proj (Term.proj `f "." `range) "." `carrier)
             ","
             (Term.anonymousCtor
              "⟨"
              [(num "1") "," (Term.app `one_left_coset [(Term.hole "_")])]
              "⟩")]
            "⟩")])
         (GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.«term∞» "∞")])
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Equiv.swap
       [(Term.app
         `from_coset
         [(Term.anonymousCtor
           "⟨"
           [(Term.proj (Term.proj `f "." `range) "." `carrier)
            ","
            (Term.anonymousCtor
             "⟨"
             [(num "1") "," (Term.app `one_left_coset [(Term.hole "_")])]
             "⟩")]
           "⟩")])
        (GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.«term∞» "∞")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.«term∞»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.«term∞»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.«term∞» "∞")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.«term∞»', expected 'GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.term∞._@.Algebra.Category.GroupCat.EpiMono._hyg.1797'
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
      Let `τ` be the permutation on `X'` exchanging `f.range` and the point at infinity.
      -/
    noncomputable
  def tau : SX' := Equiv.swap from_coset ⟨ f . range . carrier , ⟨ 1 , one_left_coset _ ⟩ ⟩ ∞
#align Group.surjective_of_epi_auxs.tau GroupCat.SurjectiveOfEpiAuxs.tau

-- mathport name: exprτ
local notation "τ" => tau f

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `τ_apply_infinity [])
      (Command.declSig
       []
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app
          (GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.termτ "τ")
          [(GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.«term∞» "∞")])
         "="
         (Term.app
          `from_coset
          [(Term.anonymousCtor
            "⟨"
            [(Term.proj (Term.proj `f "." `range) "." `carrier)
             ","
             (Term.anonymousCtor
              "⟨"
              [(num "1") "," (Term.app `one_left_coset [(Term.hole "_")])]
              "⟩")]
            "⟩")]))))
      (Command.declValSimple
       ":="
       (Term.app `Equiv.swap_apply_right [(Term.hole "_") (Term.hole "_")])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Equiv.swap_apply_right [(Term.hole "_") (Term.hole "_")])
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
      `Equiv.swap_apply_right
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app
        (GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.termτ "τ")
        [(GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.«term∞» "∞")])
       "="
       (Term.app
        `from_coset
        [(Term.anonymousCtor
          "⟨"
          [(Term.proj (Term.proj `f "." `range) "." `carrier)
           ","
           (Term.anonymousCtor
            "⟨"
            [(num "1") "," (Term.app `one_left_coset [(Term.hole "_")])]
            "⟩")]
          "⟩")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `from_coset
       [(Term.anonymousCtor
         "⟨"
         [(Term.proj (Term.proj `f "." `range) "." `carrier)
          ","
          (Term.anonymousCtor "⟨" [(num "1") "," (Term.app `one_left_coset [(Term.hole "_")])] "⟩")]
         "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.proj (Term.proj `f "." `range) "." `carrier)
        ","
        (Term.anonymousCtor "⟨" [(num "1") "," (Term.app `one_left_coset [(Term.hole "_")])] "⟩")]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [(num "1") "," (Term.app `one_left_coset [(Term.hole "_")])] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `one_left_coset [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `one_left_coset
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.proj `f "." `range) "." `carrier)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj `f "." `range)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `from_coset
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app
       (GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.termτ "τ")
       [(GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.«term∞» "∞")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.«term∞»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.«term∞»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.«term∞» "∞")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.«term∞»', expected 'GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.term∞._@.Algebra.Category.GroupCat.EpiMono._hyg.1797'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  τ_apply_infinity
  : τ ∞ = from_coset ⟨ f . range . carrier , ⟨ 1 , one_left_coset _ ⟩ ⟩
  := Equiv.swap_apply_right _ _
#align Group.surjective_of_epi_auxs.τ_apply_infinity GroupCat.SurjectiveOfEpiAuxs.τ_apply_infinity

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `τ_apply_from_coset [])
      (Command.declSig
       []
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app
          (GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.termτ "τ")
          [(Term.app
            `from_coset
            [(Term.anonymousCtor
              "⟨"
              [(Term.proj (Term.proj `f "." `range) "." `carrier)
               ","
               (Term.anonymousCtor
                "⟨"
                [(num "1") "," (Term.app `one_left_coset [(Term.hole "_")])]
                "⟩")]
              "⟩")])])
         "="
         (GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.«term∞» "∞"))))
      (Command.declValSimple
       ":="
       (Term.app `Equiv.swap_apply_left [(Term.hole "_") (Term.hole "_")])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Equiv.swap_apply_left [(Term.hole "_") (Term.hole "_")])
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
      `Equiv.swap_apply_left
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app
        (GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.termτ "τ")
        [(Term.app
          `from_coset
          [(Term.anonymousCtor
            "⟨"
            [(Term.proj (Term.proj `f "." `range) "." `carrier)
             ","
             (Term.anonymousCtor
              "⟨"
              [(num "1") "," (Term.app `one_left_coset [(Term.hole "_")])]
              "⟩")]
            "⟩")])])
       "="
       (GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.«term∞» "∞"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.«term∞» "∞")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.«term∞»', expected 'GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.term∞._@.Algebra.Category.GroupCat.EpiMono._hyg.1797'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  τ_apply_from_coset
  : τ from_coset ⟨ f . range . carrier , ⟨ 1 , one_left_coset _ ⟩ ⟩ = ∞
  := Equiv.swap_apply_left _ _
#align
  Group.surjective_of_epi_auxs.τ_apply_from_coset GroupCat.SurjectiveOfEpiAuxs.τ_apply_from_coset

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `τ_apply_from_coset' [])
      (Command.declSig
       [(Term.explicitBinder "(" [`x] [":" `B] [] ")")
        (Term.explicitBinder "(" [`hx] [":" («term_∈_» `x "∈" (Term.proj `f "." `range))] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app
          (GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.termτ "τ")
          [(Term.app
            `from_coset
            [(Term.anonymousCtor
              "⟨"
              [(Coset.GroupTheory.Coset.left_coset
                `x
                " *l "
                (Term.proj (Term.proj `f "." `range) "." `carrier))
               ","
               (Term.anonymousCtor "⟨" [`x "," `rfl] "⟩")]
              "⟩")])])
         "="
         (GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.«term∞» "∞"))))
      (Command.declValSimple
       ":="
       (Term.subst
        (Term.proj (Term.app `from_coset_eq_of_mem_range [(Term.hole "_") `hx]) "." `symm)
        "▸"
        [(Term.app `τ_apply_from_coset [(Term.hole "_")])])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.subst
       (Term.proj (Term.app `from_coset_eq_of_mem_range [(Term.hole "_") `hx]) "." `symm)
       "▸"
       [(Term.app `τ_apply_from_coset [(Term.hole "_")])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `τ_apply_from_coset [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `τ_apply_from_coset
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 75 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 75, term))
      (Term.proj (Term.app `from_coset_eq_of_mem_range [(Term.hole "_") `hx]) "." `symm)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `from_coset_eq_of_mem_range [(Term.hole "_") `hx])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hx
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `from_coset_eq_of_mem_range
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `from_coset_eq_of_mem_range [(Term.hole "_") `hx])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 75, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 75, (some 75, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app
        (GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.termτ "τ")
        [(Term.app
          `from_coset
          [(Term.anonymousCtor
            "⟨"
            [(Coset.GroupTheory.Coset.left_coset
              `x
              " *l "
              (Term.proj (Term.proj `f "." `range) "." `carrier))
             ","
             (Term.anonymousCtor "⟨" [`x "," `rfl] "⟩")]
            "⟩")])])
       "="
       (GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.«term∞» "∞"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.«term∞» "∞")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.«term∞»', expected 'GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.term∞._@.Algebra.Category.GroupCat.EpiMono._hyg.1797'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  τ_apply_from_coset'
  ( x : B ) ( hx : x ∈ f . range ) : τ from_coset ⟨ x *l f . range . carrier , ⟨ x , rfl ⟩ ⟩ = ∞
  := from_coset_eq_of_mem_range _ hx . symm ▸ τ_apply_from_coset _
#align
  Group.surjective_of_epi_auxs.τ_apply_from_coset' GroupCat.SurjectiveOfEpiAuxs.τ_apply_from_coset'

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `τ_symm_apply_from_coset [])
      (Command.declSig
       []
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app
          (Term.app
           `Equiv.symm
           [(GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.termτ "τ")])
          [(Term.app
            `from_coset
            [(Term.anonymousCtor
              "⟨"
              [(Term.proj (Term.proj `f "." `range) "." `carrier)
               ","
               (Term.anonymousCtor
                "⟨"
                [(num "1") "," (Term.app `one_left_coset [(Term.hole "_")])]
                "⟩")]
              "⟩")])])
         "="
         (GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.«term∞» "∞"))))
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
             [(Tactic.rwRule [] `tau)
              ","
              (Tactic.rwRule [] `Equiv.symm_swap)
              ","
              (Tactic.rwRule [] `Equiv.swap_apply_left)]
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
            [(Tactic.rwRule [] `tau)
             ","
             (Tactic.rwRule [] `Equiv.symm_swap)
             ","
             (Tactic.rwRule [] `Equiv.swap_apply_left)]
            "]")
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `tau)
         ","
         (Tactic.rwRule [] `Equiv.symm_swap)
         ","
         (Tactic.rwRule [] `Equiv.swap_apply_left)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Equiv.swap_apply_left
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Equiv.symm_swap
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `tau
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app
        (Term.app
         `Equiv.symm
         [(GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.termτ "τ")])
        [(Term.app
          `from_coset
          [(Term.anonymousCtor
            "⟨"
            [(Term.proj (Term.proj `f "." `range) "." `carrier)
             ","
             (Term.anonymousCtor
              "⟨"
              [(num "1") "," (Term.app `one_left_coset [(Term.hole "_")])]
              "⟩")]
            "⟩")])])
       "="
       (GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.«term∞» "∞"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.«term∞» "∞")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.«term∞»', expected 'GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.term∞._@.Algebra.Category.GroupCat.EpiMono._hyg.1797'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  τ_symm_apply_from_coset
  : Equiv.symm τ from_coset ⟨ f . range . carrier , ⟨ 1 , one_left_coset _ ⟩ ⟩ = ∞
  := by rw [ tau , Equiv.symm_swap , Equiv.swap_apply_left ]
#align
  Group.surjective_of_epi_auxs.τ_symm_apply_from_coset GroupCat.SurjectiveOfEpiAuxs.τ_symm_apply_from_coset

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `τ_symm_apply_infinity [])
      (Command.declSig
       []
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app
          (Term.app
           `Equiv.symm
           [(GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.termτ "τ")])
          [(GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.«term∞» "∞")])
         "="
         (Term.app
          `from_coset
          [(Term.anonymousCtor
            "⟨"
            [(Term.proj (Term.proj `f "." `range) "." `carrier)
             ","
             (Term.anonymousCtor
              "⟨"
              [(num "1") "," (Term.app `one_left_coset [(Term.hole "_")])]
              "⟩")]
            "⟩")]))))
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
             [(Tactic.rwRule [] `tau)
              ","
              (Tactic.rwRule [] `Equiv.symm_swap)
              ","
              (Tactic.rwRule [] `Equiv.swap_apply_right)]
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
            [(Tactic.rwRule [] `tau)
             ","
             (Tactic.rwRule [] `Equiv.symm_swap)
             ","
             (Tactic.rwRule [] `Equiv.swap_apply_right)]
            "]")
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `tau)
         ","
         (Tactic.rwRule [] `Equiv.symm_swap)
         ","
         (Tactic.rwRule [] `Equiv.swap_apply_right)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Equiv.swap_apply_right
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Equiv.symm_swap
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `tau
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app
        (Term.app
         `Equiv.symm
         [(GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.termτ "τ")])
        [(GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.«term∞» "∞")])
       "="
       (Term.app
        `from_coset
        [(Term.anonymousCtor
          "⟨"
          [(Term.proj (Term.proj `f "." `range) "." `carrier)
           ","
           (Term.anonymousCtor
            "⟨"
            [(num "1") "," (Term.app `one_left_coset [(Term.hole "_")])]
            "⟩")]
          "⟩")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `from_coset
       [(Term.anonymousCtor
         "⟨"
         [(Term.proj (Term.proj `f "." `range) "." `carrier)
          ","
          (Term.anonymousCtor "⟨" [(num "1") "," (Term.app `one_left_coset [(Term.hole "_")])] "⟩")]
         "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.proj (Term.proj `f "." `range) "." `carrier)
        ","
        (Term.anonymousCtor "⟨" [(num "1") "," (Term.app `one_left_coset [(Term.hole "_")])] "⟩")]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [(num "1") "," (Term.app `one_left_coset [(Term.hole "_")])] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `one_left_coset [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `one_left_coset
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.proj `f "." `range) "." `carrier)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj `f "." `range)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `from_coset
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app
       (Term.app
        `Equiv.symm
        [(GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.termτ "τ")])
       [(GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.«term∞» "∞")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.«term∞»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.«term∞»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.«term∞» "∞")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.«term∞»', expected 'GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.term∞._@.Algebra.Category.GroupCat.EpiMono._hyg.1797'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  τ_symm_apply_infinity
  : Equiv.symm τ ∞ = from_coset ⟨ f . range . carrier , ⟨ 1 , one_left_coset _ ⟩ ⟩
  := by rw [ tau , Equiv.symm_swap , Equiv.swap_apply_right ]
#align
  Group.surjective_of_epi_auxs.τ_symm_apply_infinity GroupCat.SurjectiveOfEpiAuxs.τ_symm_apply_infinity

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "Let `g : B ⟶ S(X')` be defined as such that, for any `β : B`, `g(β)` is the function sending\npoint at infinity to point at infinity and sending coset `y` to `β *l y`.\n-/")]
      []
      []
      []
      []
      [])
     (Command.def
      "def"
      (Command.declId `g [])
      (Command.optDeclSig
       []
       [(Term.typeSpec
         ":"
         (Algebra.Hom.Group.«term_→*_»
          `B
          " →* "
          (GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.termSX' "SX'")))])
      (Command.whereStructInst
       "where"
       [(Command.whereStructField
         (Term.letDecl
          (Term.letIdDecl
           `toFun
           [`β]
           []
           ":="
           (Term.structInst
            "{"
            []
            [(Term.structInstField
              (Term.structInstLVal `toFun [])
              ":="
              (Term.fun
               "fun"
               (Term.basicFun [`x] [] "=>" (Algebra.Group.Defs.«term_•_» `β " • " `x))))
             []
             (Term.structInstField
              (Term.structInstLVal `invFun [])
              ":="
              (Term.fun
               "fun"
               (Term.basicFun
                [`x]
                []
                "=>"
                (Algebra.Group.Defs.«term_•_» («term_⁻¹» `β "⁻¹") " • " `x))))
             []
             (Term.structInstField
              (Term.structInstLVal `left_inv [])
              ":="
              (Term.fun
               "fun"
               (Term.basicFun
                [`x]
                []
                "=>"
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(Tactic.dsimp "dsimp" [] [] ["only"] [] [])
                    []
                    (Tactic.rwSeq
                     "rw"
                     []
                     (Tactic.rwRuleSeq
                      "["
                      [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `mul_smul)
                       ","
                       (Tactic.rwRule [] `mul_left_inv)
                       ","
                       (Tactic.rwRule [] `one_smul)]
                      "]")
                     [])]))))))
             []
             (Term.structInstField
              (Term.structInstLVal `right_inv [])
              ":="
              (Term.fun
               "fun"
               (Term.basicFun
                [`x]
                []
                "=>"
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(Tactic.dsimp "dsimp" [] [] ["only"] [] [])
                    []
                    (Tactic.rwSeq
                     "rw"
                     []
                     (Tactic.rwRuleSeq
                      "["
                      [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `mul_smul)
                       ","
                       (Tactic.rwRule [] `mul_right_inv)
                       ","
                       (Tactic.rwRule [] `one_smul)]
                      "]")
                     [])]))))))]
            (Term.optEllipsis [])
            []
            "}"))))
        []
        (Command.whereStructField
         (Term.letDecl
          (Term.letIdDecl
           `map_one'
           []
           []
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
                []
                ["[" [(Tactic.simpLemma [] [] `one_smul)] "]"]
                [])]))))))
        []
        (Command.whereStructField
         (Term.letDecl
          (Term.letIdDecl
           `map_mul'
           [`b1 `b2]
           []
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
                []
                ["[" [(Tactic.simpLemma [] [] `mul_smul)] "]"]
                [])]))))))]
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.whereStructInst', expected 'Lean.Parser.Command.declValSimple'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.whereStructInst', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Std.Tactic.Ext.«tacticExt___:_» "ext" [] [])
          []
          (Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `mul_smul)] "]"] [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `mul_smul)] "]"] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_smul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Ext.«tacticExt___:_» "ext" [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Std.Tactic.Ext.«tacticExt___:_» "ext" [] [])
          []
          (Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `one_smul)] "]"] [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `one_smul)] "]"] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `one_smul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Ext.«tacticExt___:_» "ext" [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.structInst
       "{"
       []
       [(Term.structInstField
         (Term.structInstLVal `toFun [])
         ":="
         (Term.fun "fun" (Term.basicFun [`x] [] "=>" (Algebra.Group.Defs.«term_•_» `β " • " `x))))
        []
        (Term.structInstField
         (Term.structInstLVal `invFun [])
         ":="
         (Term.fun
          "fun"
          (Term.basicFun [`x] [] "=>" (Algebra.Group.Defs.«term_•_» («term_⁻¹» `β "⁻¹") " • " `x))))
        []
        (Term.structInstField
         (Term.structInstLVal `left_inv [])
         ":="
         (Term.fun
          "fun"
          (Term.basicFun
           [`x]
           []
           "=>"
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.dsimp "dsimp" [] [] ["only"] [] [])
               []
               (Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `mul_smul)
                  ","
                  (Tactic.rwRule [] `mul_left_inv)
                  ","
                  (Tactic.rwRule [] `one_smul)]
                 "]")
                [])]))))))
        []
        (Term.structInstField
         (Term.structInstLVal `right_inv [])
         ":="
         (Term.fun
          "fun"
          (Term.basicFun
           [`x]
           []
           "=>"
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.dsimp "dsimp" [] [] ["only"] [] [])
               []
               (Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `mul_smul)
                  ","
                  (Tactic.rwRule [] `mul_right_inv)
                  ","
                  (Tactic.rwRule [] `one_smul)]
                 "]")
                [])]))))))]
       (Term.optEllipsis [])
       []
       "}")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`x]
        []
        "=>"
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Tactic.dsimp "dsimp" [] [] ["only"] [] [])
            []
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `mul_smul)
               ","
               (Tactic.rwRule [] `mul_right_inv)
               ","
               (Tactic.rwRule [] `one_smul)]
              "]")
             [])])))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.dsimp "dsimp" [] [] ["only"] [] [])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `mul_smul)
             ","
             (Tactic.rwRule [] `mul_right_inv)
             ","
             (Tactic.rwRule [] `one_smul)]
            "]")
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `mul_smul)
         ","
         (Tactic.rwRule [] `mul_right_inv)
         ","
         (Tactic.rwRule [] `one_smul)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `one_smul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_right_inv
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_smul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.dsimp "dsimp" [] [] ["only"] [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`x]
        []
        "=>"
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Tactic.dsimp "dsimp" [] [] ["only"] [] [])
            []
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `mul_smul)
               ","
               (Tactic.rwRule [] `mul_left_inv)
               ","
               (Tactic.rwRule [] `one_smul)]
              "]")
             [])])))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.dsimp "dsimp" [] [] ["only"] [] [])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `mul_smul)
             ","
             (Tactic.rwRule [] `mul_left_inv)
             ","
             (Tactic.rwRule [] `one_smul)]
            "]")
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `mul_smul)
         ","
         (Tactic.rwRule [] `mul_left_inv)
         ","
         (Tactic.rwRule [] `one_smul)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `one_smul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_left_inv
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_smul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.dsimp "dsimp" [] [] ["only"] [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun [`x] [] "=>" (Algebra.Group.Defs.«term_•_» («term_⁻¹» `β "⁻¹") " • " `x)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Algebra.Group.Defs.«term_•_» («term_⁻¹» `β "⁻¹") " • " `x)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 73 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 73, term))
      («term_⁻¹» `β "⁻¹")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `β
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 74 >? 1024, (none, [anonymous]) <=? (some 73, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 73, (some 73, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun "fun" (Term.basicFun [`x] [] "=>" (Algebra.Group.Defs.«term_•_» `β " • " `x)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Algebra.Group.Defs.«term_•_» `β " • " `x)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 73 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 73, term))
      `β
[PrettyPrinter.parenthesize] ...precedences are 74 >? 1024, (none, [anonymous]) <=? (some 73, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 73, (some 73, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Algebra.Hom.Group.«term_→*_»
       `B
       " →* "
       (GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.termSX' "SX'"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.termSX' "SX'")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.termSX'', expected 'GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.termSX'._@.Algebra.Category.GroupCat.EpiMono._hyg.2128'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    Let `g : B ⟶ S(X')` be defined as such that, for any `β : B`, `g(β)` is the function sending
    point at infinity to point at infinity and sending coset `y` to `β *l y`.
    -/
  def
    g
    : B →* SX'
    where
      toFun
          β
          :=
          {
            toFun := fun x => β • x
              invFun := fun x => β ⁻¹ • x
              left_inv := fun x => by dsimp only rw [ ← mul_smul , mul_left_inv , one_smul ]
              right_inv := fun x => by dsimp only rw [ ← mul_smul , mul_right_inv , one_smul ]
            }
        map_one' := by ext simp [ one_smul ]
        map_mul' b1 b2 := by ext simp [ mul_smul ]
#align Group.surjective_of_epi_auxs.G GroupCat.SurjectiveOfEpiAuxs.g

-- mathport name: exprg
local notation "g" => g f

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment "/--" "Define `h : B ⟶ S(X')` to be `τ g τ⁻¹`\n-/")]
      []
      []
      []
      []
      [])
     (Command.def
      "def"
      (Command.declId `h [])
      (Command.optDeclSig
       []
       [(Term.typeSpec
         ":"
         (Algebra.Hom.Group.«term_→*_»
          `B
          " →* "
          (GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.termSX' "SX'")))])
      (Command.whereStructInst
       "where"
       [(Command.whereStructField
         (Term.letDecl
          (Term.letIdDecl
           `toFun
           [`β]
           []
           ":="
           (Term.app
            (Term.proj
             (Term.app
              (Term.proj
               (Term.proj
                (GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.termτ "τ")
                "."
                `symm)
               "."
               `trans)
              [(Term.app
                (GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.termg "g")
                [`β])])
             "."
             `trans)
            [(GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.termτ "τ")]))))
        []
        (Command.whereStructField
         (Term.letDecl
          (Term.letIdDecl
           `map_one'
           []
           []
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Std.Tactic.Ext.«tacticExt___:_» "ext" [] [])
               []
               (Tactic.simp "simp" [] [] [] [] [])]))))))
        []
        (Command.whereStructField
         (Term.letDecl
          (Term.letIdDecl
           `map_mul'
           [`b1 `b2]
           []
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Std.Tactic.Ext.«tacticExt___:_» "ext" [] [])
               []
               (Tactic.simp "simp" [] [] [] [] [])]))))))]
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.whereStructInst', expected 'Lean.Parser.Command.declValSimple'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.whereStructInst', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Std.Tactic.Ext.«tacticExt___:_» "ext" [] []) [] (Tactic.simp "simp" [] [] [] [] [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] [] [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Ext.«tacticExt___:_» "ext" [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Std.Tactic.Ext.«tacticExt___:_» "ext" [] []) [] (Tactic.simp "simp" [] [] [] [] [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] [] [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Ext.«tacticExt___:_» "ext" [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (Term.app
         (Term.proj
          (Term.proj
           (GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.termτ "τ")
           "."
           `symm)
          "."
          `trans)
         [(Term.app
           (GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.termg "g")
           [`β])])
        "."
        `trans)
       [(GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.termτ "τ")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.termτ', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.termτ', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.termτ "τ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.termτ', expected 'GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.termτ._@.Algebra.Category.GroupCat.EpiMono._hyg.2658'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letIdDecl', expected 'Lean.Parser.Term.letPatDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letIdDecl', expected 'Lean.Parser.Term.letEqnsDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    Define `h : B ⟶ S(X')` to be `τ g τ⁻¹`
    -/
  def
    h
    : B →* SX'
    where
      toFun β := τ . symm . trans g β . trans τ
        map_one' := by ext simp
        map_mul' b1 b2 := by ext simp
#align Group.surjective_of_epi_auxs.H GroupCat.SurjectiveOfEpiAuxs.h

-- mathport name: exprh
local notation "h" => h f

/-!
The strategy is the following: assuming `epi f`
* prove that `f.range = {x | h x = g x}`;
* thus `f ≫ h = f ≫ g` so that `h = g`;
* but if `f` is not surjective, then some `x ∉ f.range`, then `h x ≠ g x` at the coset `f.range`.
-/


/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `g_apply_from_coset [])
      (Command.declSig
       [(Term.explicitBinder "(" [`x] [":" `B] [] ")")
        (Term.explicitBinder
         "("
         [`y]
         [":" (GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.termX "X")]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app
          (Term.app (GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.termg "g") [`x])
          [(Term.app `from_coset [`y])])
         "="
         (Term.app
          `from_coset
          [(Term.anonymousCtor
            "⟨"
            [(Coset.GroupTheory.Coset.left_coset `x " *l " `y)
             ","
             (Term.byTactic
              "by"
              (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tidy "tidy" [])])))]
            "⟩")]))))
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
        (Term.app (GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.termg "g") [`x])
        [(Term.app `from_coset [`y])])
       "="
       (Term.app
        `from_coset
        [(Term.anonymousCtor
          "⟨"
          [(Coset.GroupTheory.Coset.left_coset `x " *l " `y)
           ","
           (Term.byTactic
            "by"
            (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tidy "tidy" [])])))]
          "⟩")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `from_coset
       [(Term.anonymousCtor
         "⟨"
         [(Coset.GroupTheory.Coset.left_coset `x " *l " `y)
          ","
          (Term.byTactic
           "by"
           (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tidy "tidy" [])])))]
         "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Coset.GroupTheory.Coset.left_coset `x " *l " `y)
        ","
        (Term.byTactic
         "by"
         (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tidy "tidy" [])])))]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tidy "tidy" [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tidy "tidy" [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Coset.GroupTheory.Coset.left_coset `x " *l " `y)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `from_coset
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app
       (Term.app (GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.termg "g") [`x])
       [(Term.app `from_coset [`y])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `from_coset [`y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `from_coset
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `from_coset [`y]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.app (GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.termg "g") [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.termg "g")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.termg', expected 'GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.termg._@.Algebra.Category.GroupCat.EpiMono._hyg.3172'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  g_apply_from_coset
  ( x : B ) ( y : X ) : g x from_coset y = from_coset ⟨ x *l y , by tidy ⟩
  := rfl
#align
  Group.surjective_of_epi_auxs.g_apply_from_coset GroupCat.SurjectiveOfEpiAuxs.g_apply_from_coset

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `g_apply_infinity [])
      (Command.declSig
       [(Term.explicitBinder "(" [`x] [":" `B] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app
          (Term.app (GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.termg "g") [`x])
          [(GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.«term∞» "∞")])
         "="
         (GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.«term∞» "∞"))))
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
        (Term.app (GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.termg "g") [`x])
        [(GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.«term∞» "∞")])
       "="
       (GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.«term∞» "∞"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.«term∞» "∞")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.«term∞»', expected 'GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.term∞._@.Algebra.Category.GroupCat.EpiMono._hyg.1797'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem g_apply_infinity ( x : B ) : g x ∞ = ∞ := rfl
#align Group.surjective_of_epi_auxs.g_apply_infinity GroupCat.SurjectiveOfEpiAuxs.g_apply_infinity

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `h_apply_infinity [])
      (Command.declSig
       [(Term.explicitBinder "(" [`x] [":" `B] [] ")")
        (Term.explicitBinder "(" [`hx] [":" («term_∈_» `x "∈" (Term.proj `f "." `range))] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app
          (Term.app (GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.termh "h") [`x])
          [(GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.«term∞» "∞")])
         "="
         (GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.«term∞» "∞"))))
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
            ["["
             [(Tactic.simpLemma [] [] `H)
              ","
              (Tactic.simpLemma [] [] `MonoidHom.coe_mk)
              ","
              (Tactic.simpLemma [] [] `Equiv.toFun_as_coe)
              ","
              (Tactic.simpLemma [] [] `Equiv.coe_trans)
              ","
              (Tactic.simpLemma [] [] `Function.comp_apply)]
             "]"]
            [])
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [] `τ_symm_apply_infinity) "," (Tactic.rwRule [] `g_apply_from_coset)]
             "]")
            [])
           []
           (Std.Tactic.Simpa.simpa
            "simpa"
            []
            []
            (Std.Tactic.Simpa.simpaArgsRest
             []
             []
             ["only"]
             [(Tactic.simpArgs
               "["
               [(Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `Subtype.val_eq_coe)]
               "]")]
             ["using" (Term.app `τ_apply_from_coset' [`f `x `hx])]))])))
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
           ["["
            [(Tactic.simpLemma [] [] `H)
             ","
             (Tactic.simpLemma [] [] `MonoidHom.coe_mk)
             ","
             (Tactic.simpLemma [] [] `Equiv.toFun_as_coe)
             ","
             (Tactic.simpLemma [] [] `Equiv.coe_trans)
             ","
             (Tactic.simpLemma [] [] `Function.comp_apply)]
            "]"]
           [])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `τ_symm_apply_infinity) "," (Tactic.rwRule [] `g_apply_from_coset)]
            "]")
           [])
          []
          (Std.Tactic.Simpa.simpa
           "simpa"
           []
           []
           (Std.Tactic.Simpa.simpaArgsRest
            []
            []
            ["only"]
            [(Tactic.simpArgs
              "["
              [(Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `Subtype.val_eq_coe)]
              "]")]
            ["using" (Term.app `τ_apply_from_coset' [`f `x `hx])]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Simpa.simpa
       "simpa"
       []
       []
       (Std.Tactic.Simpa.simpaArgsRest
        []
        []
        ["only"]
        [(Tactic.simpArgs
          "["
          [(Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `Subtype.val_eq_coe)]
          "]")]
        ["using" (Term.app `τ_apply_from_coset' [`f `x `hx])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `τ_apply_from_coset' [`f `x `hx])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hx
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `τ_apply_from_coset'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Subtype.val_eq_coe
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `τ_symm_apply_infinity) "," (Tactic.rwRule [] `g_apply_from_coset)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g_apply_from_coset
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `τ_symm_apply_infinity
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["["
        [(Tactic.simpLemma [] [] `H)
         ","
         (Tactic.simpLemma [] [] `MonoidHom.coe_mk)
         ","
         (Tactic.simpLemma [] [] `Equiv.toFun_as_coe)
         ","
         (Tactic.simpLemma [] [] `Equiv.coe_trans)
         ","
         (Tactic.simpLemma [] [] `Function.comp_apply)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Function.comp_apply
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Equiv.coe_trans
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Equiv.toFun_as_coe
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `MonoidHom.coe_mk
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `H
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app
        (Term.app (GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.termh "h") [`x])
        [(GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.«term∞» "∞")])
       "="
       (GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.«term∞» "∞"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.«term∞» "∞")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.«term∞»', expected 'GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.term∞._@.Algebra.Category.GroupCat.EpiMono._hyg.1797'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  h_apply_infinity
  ( x : B ) ( hx : x ∈ f . range ) : h x ∞ = ∞
  :=
    by
      simp
          only
          [ H , MonoidHom.coe_mk , Equiv.toFun_as_coe , Equiv.coe_trans , Function.comp_apply ]
        rw [ τ_symm_apply_infinity , g_apply_from_coset ]
        simpa only [ ← Subtype.val_eq_coe ] using τ_apply_from_coset' f x hx
#align Group.surjective_of_epi_auxs.h_apply_infinity GroupCat.SurjectiveOfEpiAuxs.h_apply_infinity

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `h_apply_from_coset [])
      (Command.declSig
       [(Term.explicitBinder "(" [`x] [":" `B] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app
          (Term.app (GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.termh "h") [`x])
          [(Term.app
            `from_coset
            [(Term.anonymousCtor
              "⟨"
              [(Term.proj (Term.proj `f "." `range) "." `carrier)
               ","
               (Term.anonymousCtor
                "⟨"
                [(num "1") "," (Term.app `one_left_coset [(Term.hole "_")])]
                "⟩")]
              "⟩")])])
         "="
         (Term.app
          `from_coset
          [(Term.anonymousCtor
            "⟨"
            [(Term.proj (Term.proj `f "." `range) "." `carrier)
             ","
             (Term.anonymousCtor
              "⟨"
              [(num "1") "," (Term.app `one_left_coset [(Term.hole "_")])]
              "⟩")]
            "⟩")]))))
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
            []
            ["["
             [(Tactic.simpLemma [] [] `H)
              ","
              (Tactic.simpLemma [] [] `τ_symm_apply_from_coset)
              ","
              (Tactic.simpLemma [] [] `g_apply_infinity)
              ","
              (Tactic.simpLemma [] [] `τ_apply_infinity)]
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
         [(Tactic.simp
           "simp"
           []
           []
           []
           ["["
            [(Tactic.simpLemma [] [] `H)
             ","
             (Tactic.simpLemma [] [] `τ_symm_apply_from_coset)
             ","
             (Tactic.simpLemma [] [] `g_apply_infinity)
             ","
             (Tactic.simpLemma [] [] `τ_apply_infinity)]
            "]"]
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       []
       ["["
        [(Tactic.simpLemma [] [] `H)
         ","
         (Tactic.simpLemma [] [] `τ_symm_apply_from_coset)
         ","
         (Tactic.simpLemma [] [] `g_apply_infinity)
         ","
         (Tactic.simpLemma [] [] `τ_apply_infinity)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `τ_apply_infinity
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g_apply_infinity
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `τ_symm_apply_from_coset
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `H
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app
        (Term.app (GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.termh "h") [`x])
        [(Term.app
          `from_coset
          [(Term.anonymousCtor
            "⟨"
            [(Term.proj (Term.proj `f "." `range) "." `carrier)
             ","
             (Term.anonymousCtor
              "⟨"
              [(num "1") "," (Term.app `one_left_coset [(Term.hole "_")])]
              "⟩")]
            "⟩")])])
       "="
       (Term.app
        `from_coset
        [(Term.anonymousCtor
          "⟨"
          [(Term.proj (Term.proj `f "." `range) "." `carrier)
           ","
           (Term.anonymousCtor
            "⟨"
            [(num "1") "," (Term.app `one_left_coset [(Term.hole "_")])]
            "⟩")]
          "⟩")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `from_coset
       [(Term.anonymousCtor
         "⟨"
         [(Term.proj (Term.proj `f "." `range) "." `carrier)
          ","
          (Term.anonymousCtor "⟨" [(num "1") "," (Term.app `one_left_coset [(Term.hole "_")])] "⟩")]
         "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.proj (Term.proj `f "." `range) "." `carrier)
        ","
        (Term.anonymousCtor "⟨" [(num "1") "," (Term.app `one_left_coset [(Term.hole "_")])] "⟩")]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [(num "1") "," (Term.app `one_left_coset [(Term.hole "_")])] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `one_left_coset [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `one_left_coset
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.proj `f "." `range) "." `carrier)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj `f "." `range)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `from_coset
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app
       (Term.app (GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.termh "h") [`x])
       [(Term.app
         `from_coset
         [(Term.anonymousCtor
           "⟨"
           [(Term.proj (Term.proj `f "." `range) "." `carrier)
            ","
            (Term.anonymousCtor
             "⟨"
             [(num "1") "," (Term.app `one_left_coset [(Term.hole "_")])]
             "⟩")]
           "⟩")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `from_coset
       [(Term.anonymousCtor
         "⟨"
         [(Term.proj (Term.proj `f "." `range) "." `carrier)
          ","
          (Term.anonymousCtor "⟨" [(num "1") "," (Term.app `one_left_coset [(Term.hole "_")])] "⟩")]
         "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.proj (Term.proj `f "." `range) "." `carrier)
        ","
        (Term.anonymousCtor "⟨" [(num "1") "," (Term.app `one_left_coset [(Term.hole "_")])] "⟩")]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [(num "1") "," (Term.app `one_left_coset [(Term.hole "_")])] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `one_left_coset [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `one_left_coset
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.proj `f "." `range) "." `carrier)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj `f "." `range)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `from_coset
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `from_coset
      [(Term.anonymousCtor
        "⟨"
        [(Term.proj (Term.proj `f "." `range) "." `carrier)
         ","
         (Term.anonymousCtor "⟨" [(num "1") "," (Term.app `one_left_coset [(Term.hole "_")])] "⟩")]
        "⟩")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.app (GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.termh "h") [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.termh "h")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.termh', expected 'GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.termh._@.Algebra.Category.GroupCat.EpiMono._hyg.3686'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  h_apply_from_coset
  ( x : B )
    :
      h x from_coset ⟨ f . range . carrier , ⟨ 1 , one_left_coset _ ⟩ ⟩
        =
        from_coset ⟨ f . range . carrier , ⟨ 1 , one_left_coset _ ⟩ ⟩
  := by simp [ H , τ_symm_apply_from_coset , g_apply_infinity , τ_apply_infinity ]
#align
  Group.surjective_of_epi_auxs.h_apply_from_coset GroupCat.SurjectiveOfEpiAuxs.h_apply_from_coset

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `h_apply_from_coset' [])
      (Command.declSig
       [(Term.explicitBinder "(" [`x] [":" `B] [] ")")
        (Term.explicitBinder "(" [`b] [":" `B] [] ")")
        (Term.explicitBinder "(" [`hb] [":" («term_∈_» `b "∈" (Term.proj `f "." `range))] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app
          (Term.app (GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.termh "h") [`x])
          [(Term.app
            `from_coset
            [(Term.anonymousCtor
              "⟨"
              [(Coset.GroupTheory.Coset.left_coset
                `b
                " *l "
                (Term.proj (Term.proj `f "." `range) "." `carrier))
               ","
               (Term.anonymousCtor "⟨" [`b "," `rfl] "⟩")]
              "⟩")])])
         "="
         (Term.app
          `from_coset
          [(Term.anonymousCtor
            "⟨"
            [(Coset.GroupTheory.Coset.left_coset
              `b
              " *l "
              (Term.proj (Term.proj `f "." `range) "." `carrier))
             ","
             (Term.anonymousCtor "⟨" [`b "," `rfl] "⟩")]
            "⟩")]))))
      (Command.declValSimple
       ":="
       (Term.subst
        (Term.proj (Term.app `from_coset_eq_of_mem_range [(Term.hole "_") `hb]) "." `symm)
        "▸"
        [(Term.app `h_apply_from_coset [`f `x])])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.subst
       (Term.proj (Term.app `from_coset_eq_of_mem_range [(Term.hole "_") `hb]) "." `symm)
       "▸"
       [(Term.app `h_apply_from_coset [`f `x])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `h_apply_from_coset [`f `x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `h_apply_from_coset
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 75 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 75, term))
      (Term.proj (Term.app `from_coset_eq_of_mem_range [(Term.hole "_") `hb]) "." `symm)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `from_coset_eq_of_mem_range [(Term.hole "_") `hb])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hb
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `from_coset_eq_of_mem_range
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `from_coset_eq_of_mem_range [(Term.hole "_") `hb])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 75, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 75, (some 75, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app
        (Term.app (GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.termh "h") [`x])
        [(Term.app
          `from_coset
          [(Term.anonymousCtor
            "⟨"
            [(Coset.GroupTheory.Coset.left_coset
              `b
              " *l "
              (Term.proj (Term.proj `f "." `range) "." `carrier))
             ","
             (Term.anonymousCtor "⟨" [`b "," `rfl] "⟩")]
            "⟩")])])
       "="
       (Term.app
        `from_coset
        [(Term.anonymousCtor
          "⟨"
          [(Coset.GroupTheory.Coset.left_coset
            `b
            " *l "
            (Term.proj (Term.proj `f "." `range) "." `carrier))
           ","
           (Term.anonymousCtor "⟨" [`b "," `rfl] "⟩")]
          "⟩")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `from_coset
       [(Term.anonymousCtor
         "⟨"
         [(Coset.GroupTheory.Coset.left_coset
           `b
           " *l "
           (Term.proj (Term.proj `f "." `range) "." `carrier))
          ","
          (Term.anonymousCtor "⟨" [`b "," `rfl] "⟩")]
         "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Coset.GroupTheory.Coset.left_coset
         `b
         " *l "
         (Term.proj (Term.proj `f "." `range) "." `carrier))
        ","
        (Term.anonymousCtor "⟨" [`b "," `rfl] "⟩")]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [`b "," `rfl] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rfl
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `b
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Coset.GroupTheory.Coset.left_coset
       `b
       " *l "
       (Term.proj (Term.proj `f "." `range) "." `carrier))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.proj `f "." `range) "." `carrier)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj `f "." `range)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `b
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `from_coset
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app
       (Term.app (GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.termh "h") [`x])
       [(Term.app
         `from_coset
         [(Term.anonymousCtor
           "⟨"
           [(Coset.GroupTheory.Coset.left_coset
             `b
             " *l "
             (Term.proj (Term.proj `f "." `range) "." `carrier))
            ","
            (Term.anonymousCtor "⟨" [`b "," `rfl] "⟩")]
           "⟩")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `from_coset
       [(Term.anonymousCtor
         "⟨"
         [(Coset.GroupTheory.Coset.left_coset
           `b
           " *l "
           (Term.proj (Term.proj `f "." `range) "." `carrier))
          ","
          (Term.anonymousCtor "⟨" [`b "," `rfl] "⟩")]
         "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Coset.GroupTheory.Coset.left_coset
         `b
         " *l "
         (Term.proj (Term.proj `f "." `range) "." `carrier))
        ","
        (Term.anonymousCtor "⟨" [`b "," `rfl] "⟩")]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [`b "," `rfl] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rfl
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `b
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Coset.GroupTheory.Coset.left_coset
       `b
       " *l "
       (Term.proj (Term.proj `f "." `range) "." `carrier))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.proj `f "." `range) "." `carrier)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj `f "." `range)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `b
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `from_coset
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `from_coset
      [(Term.anonymousCtor
        "⟨"
        [(Coset.GroupTheory.Coset.left_coset
          `b
          " *l "
          (Term.proj (Term.proj `f "." `range) "." `carrier))
         ","
         (Term.anonymousCtor "⟨" [`b "," `rfl] "⟩")]
        "⟩")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.app (GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.termh "h") [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.termh "h")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.termh', expected 'GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.termh._@.Algebra.Category.GroupCat.EpiMono._hyg.3686'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  h_apply_from_coset'
  ( x : B ) ( b : B ) ( hb : b ∈ f . range )
    :
      h x from_coset ⟨ b *l f . range . carrier , ⟨ b , rfl ⟩ ⟩
        =
        from_coset ⟨ b *l f . range . carrier , ⟨ b , rfl ⟩ ⟩
  := from_coset_eq_of_mem_range _ hb . symm ▸ h_apply_from_coset f x
#align
  Group.surjective_of_epi_auxs.h_apply_from_coset' GroupCat.SurjectiveOfEpiAuxs.h_apply_from_coset'

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `h_apply_from_coset_nin_range [])
      (Command.declSig
       [(Term.explicitBinder "(" [`x] [":" `B] [] ")")
        (Term.explicitBinder "(" [`hx] [":" («term_∈_» `x "∈" (Term.proj `f "." `range))] [] ")")
        (Term.explicitBinder "(" [`b] [":" `B] [] ")")
        (Term.explicitBinder "(" [`hb] [":" («term_∉_» `b "∉" (Term.proj `f "." `range))] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app
          (Term.app (GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.termh "h") [`x])
          [(Term.app
            `from_coset
            [(Term.anonymousCtor
              "⟨"
              [(Coset.GroupTheory.Coset.left_coset
                `b
                " *l "
                (Term.proj (Term.proj `f "." `range) "." `carrier))
               ","
               (Term.anonymousCtor "⟨" [`b "," `rfl] "⟩")]
              "⟩")])])
         "="
         (Term.app
          `from_coset
          [(Term.anonymousCtor
            "⟨"
            [(Coset.GroupTheory.Coset.left_coset
              («term_*_» `x "*" `b)
              " *l "
              (Term.proj (Term.proj `f "." `range) "." `carrier))
             ","
             (Term.anonymousCtor "⟨" [(«term_*_» `x "*" `b) "," `rfl] "⟩")]
            "⟩")]))))
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
            ["["
             [(Tactic.simpLemma [] [] `H)
              ","
              (Tactic.simpLemma [] [] `tau)
              ","
              (Tactic.simpLemma [] [] `MonoidHom.coe_mk)
              ","
              (Tactic.simpLemma [] [] `Equiv.toFun_as_coe)
              ","
              (Tactic.simpLemma [] [] `Equiv.coe_trans)
              ","
              (Tactic.simpLemma [] [] `Function.comp_apply)]
             "]"]
            [])
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [] `Equiv.symm_swap)
              ","
              (Tactic.rwRule
               []
               (Term.app
                (Term.explicit "@" `Equiv.swap_apply_of_ne_of_ne)
                [(GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.termX' "X'")
                 (Term.hole "_")
                 (Term.app
                  `from_coset
                  [(Term.anonymousCtor
                    "⟨"
                    [`f.range.carrier
                     ","
                     (Term.anonymousCtor
                      "⟨"
                      [(num "1") "," (Term.app `one_left_coset [(Term.hole "_")])]
                      "⟩")]
                    "⟩")])
                 (GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.«term∞» "∞")
                 (Term.app
                  `from_coset
                  [(Term.anonymousCtor
                    "⟨"
                    [(Coset.GroupTheory.Coset.left_coset `b " *l " `f.range.carrier)
                     ","
                     (Term.anonymousCtor "⟨" [`b "," `rfl] "⟩")]
                    "⟩")])
                 (Term.app `from_coset_ne_of_nin_range [(Term.hole "_") `hb])
                 (Term.byTactic
                  "by"
                  (Tactic.tacticSeq
                   (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])])))]))]
             "]")
            [])
           []
           (Tactic.simp
            "simp"
            []
            []
            ["only"]
            ["["
             [(Tactic.simpLemma [] [] `g_apply_from_coset)
              ","
              (Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `Subtype.val_eq_coe)
              ","
              (Tactic.simpLemma [] [] `left_coset_assoc)]
             "]"]
            [])
           []
           (Tactic.refine'
            "refine'"
            (Term.app
             `Equiv.swap_apply_of_ne_of_ne
             [(Term.app
               `from_coset_ne_of_nin_range
               [(Term.hole "_")
                (Term.fun "fun" (Term.basicFun [`r] [] "=>" (Term.app `hb [(Term.hole "_")])))])
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])])))]))
           []
           (convert
            "convert"
            []
            (Term.app
             `Subgroup.mul_mem
             [(Term.hole "_") (Term.app `Subgroup.inv_mem [(Term.hole "_") `hx]) `r])
            [])
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `mul_assoc)
              ","
              (Tactic.rwRule [] `mul_left_inv)
              ","
              (Tactic.rwRule [] `one_mul)]
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
         [(Tactic.simp
           "simp"
           []
           []
           ["only"]
           ["["
            [(Tactic.simpLemma [] [] `H)
             ","
             (Tactic.simpLemma [] [] `tau)
             ","
             (Tactic.simpLemma [] [] `MonoidHom.coe_mk)
             ","
             (Tactic.simpLemma [] [] `Equiv.toFun_as_coe)
             ","
             (Tactic.simpLemma [] [] `Equiv.coe_trans)
             ","
             (Tactic.simpLemma [] [] `Function.comp_apply)]
            "]"]
           [])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `Equiv.symm_swap)
             ","
             (Tactic.rwRule
              []
              (Term.app
               (Term.explicit "@" `Equiv.swap_apply_of_ne_of_ne)
               [(GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.termX' "X'")
                (Term.hole "_")
                (Term.app
                 `from_coset
                 [(Term.anonymousCtor
                   "⟨"
                   [`f.range.carrier
                    ","
                    (Term.anonymousCtor
                     "⟨"
                     [(num "1") "," (Term.app `one_left_coset [(Term.hole "_")])]
                     "⟩")]
                   "⟩")])
                (GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.«term∞» "∞")
                (Term.app
                 `from_coset
                 [(Term.anonymousCtor
                   "⟨"
                   [(Coset.GroupTheory.Coset.left_coset `b " *l " `f.range.carrier)
                    ","
                    (Term.anonymousCtor "⟨" [`b "," `rfl] "⟩")]
                   "⟩")])
                (Term.app `from_coset_ne_of_nin_range [(Term.hole "_") `hb])
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])])))]))]
            "]")
           [])
          []
          (Tactic.simp
           "simp"
           []
           []
           ["only"]
           ["["
            [(Tactic.simpLemma [] [] `g_apply_from_coset)
             ","
             (Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `Subtype.val_eq_coe)
             ","
             (Tactic.simpLemma [] [] `left_coset_assoc)]
            "]"]
           [])
          []
          (Tactic.refine'
           "refine'"
           (Term.app
            `Equiv.swap_apply_of_ne_of_ne
            [(Term.app
              `from_coset_ne_of_nin_range
              [(Term.hole "_")
               (Term.fun "fun" (Term.basicFun [`r] [] "=>" (Term.app `hb [(Term.hole "_")])))])
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])])))]))
          []
          (convert
           "convert"
           []
           (Term.app
            `Subgroup.mul_mem
            [(Term.hole "_") (Term.app `Subgroup.inv_mem [(Term.hole "_") `hx]) `r])
           [])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `mul_assoc)
             ","
             (Tactic.rwRule [] `mul_left_inv)
             ","
             (Tactic.rwRule [] `one_mul)]
            "]")
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `mul_assoc)
         ","
         (Tactic.rwRule [] `mul_left_inv)
         ","
         (Tactic.rwRule [] `one_mul)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `one_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_left_inv
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_assoc
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (convert
       "convert"
       []
       (Term.app
        `Subgroup.mul_mem
        [(Term.hole "_") (Term.app `Subgroup.inv_mem [(Term.hole "_") `hx]) `r])
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Subgroup.mul_mem
       [(Term.hole "_") (Term.app `Subgroup.inv_mem [(Term.hole "_") `hx]) `r])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `r
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `Subgroup.inv_mem [(Term.hole "_") `hx])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hx
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Subgroup.inv_mem
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `Subgroup.inv_mem [(Term.hole "_") `hx])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Subgroup.mul_mem
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine'
       "refine'"
       (Term.app
        `Equiv.swap_apply_of_ne_of_ne
        [(Term.app
          `from_coset_ne_of_nin_range
          [(Term.hole "_")
           (Term.fun "fun" (Term.basicFun [`r] [] "=>" (Term.app `hb [(Term.hole "_")])))])
         (Term.byTactic
          "by"
          (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])])))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Equiv.swap_apply_of_ne_of_ne
       [(Term.app
         `from_coset_ne_of_nin_range
         [(Term.hole "_")
          (Term.fun "fun" (Term.basicFun [`r] [] "=>" (Term.app `hb [(Term.hole "_")])))])
        (Term.byTactic
         "by"
         (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] [] [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0,
     tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.byTactic
      "by"
      (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])])))
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       `from_coset_ne_of_nin_range
       [(Term.hole "_")
        (Term.fun "fun" (Term.basicFun [`r] [] "=>" (Term.app `hb [(Term.hole "_")])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun "fun" (Term.basicFun [`r] [] "=>" (Term.app `hb [(Term.hole "_")])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `hb [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `hb
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `r
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `from_coset_ne_of_nin_range
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `from_coset_ne_of_nin_range
      [(Term.hole "_")
       (Term.fun "fun" (Term.basicFun [`r] [] "=>" (Term.app `hb [(Term.hole "_")])))])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Equiv.swap_apply_of_ne_of_ne
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["["
        [(Tactic.simpLemma [] [] `g_apply_from_coset)
         ","
         (Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `Subtype.val_eq_coe)
         ","
         (Tactic.simpLemma [] [] `left_coset_assoc)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `left_coset_assoc
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Subtype.val_eq_coe
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g_apply_from_coset
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `Equiv.symm_swap)
         ","
         (Tactic.rwRule
          []
          (Term.app
           (Term.explicit "@" `Equiv.swap_apply_of_ne_of_ne)
           [(GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.termX' "X'")
            (Term.hole "_")
            (Term.app
             `from_coset
             [(Term.anonymousCtor
               "⟨"
               [`f.range.carrier
                ","
                (Term.anonymousCtor
                 "⟨"
                 [(num "1") "," (Term.app `one_left_coset [(Term.hole "_")])]
                 "⟩")]
               "⟩")])
            (GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.«term∞» "∞")
            (Term.app
             `from_coset
             [(Term.anonymousCtor
               "⟨"
               [(Coset.GroupTheory.Coset.left_coset `b " *l " `f.range.carrier)
                ","
                (Term.anonymousCtor "⟨" [`b "," `rfl] "⟩")]
               "⟩")])
            (Term.app `from_coset_ne_of_nin_range [(Term.hole "_") `hb])
            (Term.byTactic
             "by"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])])))]))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.explicit "@" `Equiv.swap_apply_of_ne_of_ne)
       [(GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.termX' "X'")
        (Term.hole "_")
        (Term.app
         `from_coset
         [(Term.anonymousCtor
           "⟨"
           [`f.range.carrier
            ","
            (Term.anonymousCtor
             "⟨"
             [(num "1") "," (Term.app `one_left_coset [(Term.hole "_")])]
             "⟩")]
           "⟩")])
        (GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.«term∞» "∞")
        (Term.app
         `from_coset
         [(Term.anonymousCtor
           "⟨"
           [(Coset.GroupTheory.Coset.left_coset `b " *l " `f.range.carrier)
            ","
            (Term.anonymousCtor "⟨" [`b "," `rfl] "⟩")]
           "⟩")])
        (Term.app `from_coset_ne_of_nin_range [(Term.hole "_") `hb])
        (Term.byTactic
         "by"
         (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] [] [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0,
     tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.byTactic
      "by"
      (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])])))
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `from_coset_ne_of_nin_range [(Term.hole "_") `hb])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hb
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `from_coset_ne_of_nin_range
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `from_coset_ne_of_nin_range [(Term.hole "_") `hb])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       `from_coset
       [(Term.anonymousCtor
         "⟨"
         [(Coset.GroupTheory.Coset.left_coset `b " *l " `f.range.carrier)
          ","
          (Term.anonymousCtor "⟨" [`b "," `rfl] "⟩")]
         "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Coset.GroupTheory.Coset.left_coset `b " *l " `f.range.carrier)
        ","
        (Term.anonymousCtor "⟨" [`b "," `rfl] "⟩")]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [`b "," `rfl] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rfl
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `b
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Coset.GroupTheory.Coset.left_coset `b " *l " `f.range.carrier)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f.range.carrier
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `b
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `from_coset
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `from_coset
      [(Term.anonymousCtor
        "⟨"
        [(Coset.GroupTheory.Coset.left_coset `b " *l " `f.range.carrier)
         ","
         (Term.anonymousCtor "⟨" [`b "," `rfl] "⟩")]
        "⟩")])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.«term∞»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.«term∞»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.«term∞» "∞")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.«term∞»', expected 'GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.term∞._@.Algebra.Category.GroupCat.EpiMono._hyg.1797'
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
  h_apply_from_coset_nin_range
  ( x : B ) ( hx : x ∈ f . range ) ( b : B ) ( hb : b ∉ f . range )
    :
      h x from_coset ⟨ b *l f . range . carrier , ⟨ b , rfl ⟩ ⟩
        =
        from_coset ⟨ x * b *l f . range . carrier , ⟨ x * b , rfl ⟩ ⟩
  :=
    by
      simp
          only
          [
            H , tau , MonoidHom.coe_mk , Equiv.toFun_as_coe , Equiv.coe_trans , Function.comp_apply
            ]
        rw
          [
            Equiv.symm_swap
              ,
              @ Equiv.swap_apply_of_ne_of_ne
                X'
                  _
                  from_coset ⟨ f.range.carrier , ⟨ 1 , one_left_coset _ ⟩ ⟩
                  ∞
                  from_coset ⟨ b *l f.range.carrier , ⟨ b , rfl ⟩ ⟩
                  from_coset_ne_of_nin_range _ hb
                  by simp
            ]
        simp only [ g_apply_from_coset , ← Subtype.val_eq_coe , left_coset_assoc ]
        refine' Equiv.swap_apply_of_ne_of_ne from_coset_ne_of_nin_range _ fun r => hb _ by simp
        convert Subgroup.mul_mem _ Subgroup.inv_mem _ hx r
        rw [ ← mul_assoc , mul_left_inv , one_mul ]
#align
  Group.surjective_of_epi_auxs.h_apply_from_coset_nin_range GroupCat.SurjectiveOfEpiAuxs.h_apply_from_coset_nin_range

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `agree [])
      (Command.declSig
       []
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.proj (Term.proj `f "." `range) "." `carrier)
         "="
         (Set.«term{_|_}»
          "{"
          (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) [])
          "|"
          («term_=_»
           (Term.app
            (GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.termh "h")
            [`x])
           "="
           (Term.app
            (GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.termg "g")
            [`x]))
          "}"))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.refine'
            "refine'"
            (Term.app
             `Set.ext
             [(Term.fun
               "fun"
               (Term.basicFun
                [`b]
                []
                "=>"
                (Term.anonymousCtor
                 "⟨"
                 [(Term.hole "_")
                  ","
                  (Term.fun
                   "fun"
                   (Term.basicFun
                    [`hb]
                    [(Term.typeSpec
                      ":"
                      («term_=_»
                       (Term.app
                        (GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.termh "h")
                        [`b])
                       "="
                       (Term.app
                        (GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.termg "g")
                        [`b])))]
                    "=>"
                    (Term.app
                     `by_contradiction
                     [(Term.fun "fun" (Term.basicFun [`r] [] "=>" (Term.hole "_")))])))]
                 "⟩")))]))
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Std.Tactic.rintro
              "rintro"
              [(Std.Tactic.RCases.rintroPat.one
                (Std.Tactic.RCases.rcasesPat.tuple
                 "⟨"
                 [(Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `a)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                   [])]
                 "⟩"))]
              [])
             []
             (Tactic.change
              "change"
              («term_=_»
               (Term.app
                (GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.termh "h")
                [(Term.app `f [`a])])
               "="
               (Term.app
                (GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.termg "g")
                [(Term.app `f [`a])]))
              [])
             []
             (Std.Tactic.Ext.«tacticExt___:_»
              "ext"
              [(Std.Tactic.RCases.rintroPat.one
                (Std.Tactic.RCases.rcasesPat.tuple
                 "⟨"
                 [(Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed
                    [(Std.Tactic.RCases.rcasesPat.tuple
                      "⟨"
                      [(Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.ignore "_")])
                        [])
                       ","
                       (Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed
                         [(Std.Tactic.RCases.rcasesPat.tuple
                           "⟨"
                           [(Std.Tactic.RCases.rcasesPatLo
                             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `y)])
                             [])
                            ","
                            (Std.Tactic.RCases.rcasesPatLo
                             (Std.Tactic.RCases.rcasesPatMed
                              [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                             [])]
                           "⟩")])
                        [])]
                      "⟩")])
                   [])]
                 "⟩"))]
              [])
             []
             (tactic__
              (cdotTk (patternIgnore (token.«· » "·")))
              [(Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `g_apply_from_coset)] "]")
                [])
               []
               (Classical.«tacticBy_cases_:_» "by_cases" [`m ":"] («term_∈_» `y "∈" `f.range))
               []
               (tactic__
                (cdotTk (patternIgnore (token.«· » "·")))
                [(Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule
                     []
                     (Term.app
                      `h_apply_from_coset'
                      [(Term.hole "_") (Term.hole "_") (Term.hole "_") `m]))
                    ","
                    (Tactic.rwRule [] (Term.app `from_coset_eq_of_mem_range [(Term.hole "_") `m]))]
                   "]")
                  [])
                 []
                 (Tactic.change
                  "change"
                  («term_=_»
                   (Term.app `from_coset [(Term.hole "_")])
                   "="
                   (Term.app
                    `from_coset
                    [(Term.anonymousCtor
                      "⟨"
                      [(Coset.GroupTheory.Coset.left_coset
                        (Term.app `f [`a])
                        " *l "
                        (Coset.GroupTheory.Coset.left_coset `y " *l " (Term.hole "_")))
                       ","
                       (Term.hole "_")]
                      "⟩")]))
                  [])
                 []
                 (Std.Tactic.Simpa.simpa
                  "simpa"
                  []
                  []
                  (Std.Tactic.Simpa.simpaArgsRest
                   []
                   []
                   ["only"]
                   [(Tactic.simpArgs
                     "["
                     [(Tactic.simpLemma
                       []
                       [(patternIgnore (token.«← » "←"))]
                       (Term.app
                        `from_coset_eq_of_mem_range
                        [(Term.hole "_")
                         (Term.app
                          `Subgroup.mul_mem
                          [(Term.hole "_") (Term.anonymousCtor "⟨" [`a "," `rfl] "⟩") `m])]))
                      ","
                      (Tactic.simpLemma [] [] `left_coset_assoc)]
                     "]")]
                   []))])
               []
               (tactic__
                (cdotTk (patternIgnore (token.«· » "·")))
                [(Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule
                     []
                     (Term.app
                      `h_apply_from_coset_nin_range
                      [(Term.hole "_")
                       (Term.hole "_")
                       (Term.anonymousCtor "⟨" [(Term.hole "_") "," `rfl] "⟩")
                       (Term.hole "_")
                       `m]))]
                   "]")
                  [])
                 []
                 (Std.Tactic.Simpa.simpa
                  "simpa"
                  []
                  []
                  (Std.Tactic.Simpa.simpaArgsRest
                   []
                   []
                   ["only"]
                   [(Tactic.simpArgs
                     "["
                     [(Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `Subtype.val_eq_coe)
                      ","
                      (Tactic.simpLemma [] [] `left_coset_assoc)]
                     "]")]
                   []))])])
             []
             (tactic__
              (cdotTk (patternIgnore (token.«· » "·")))
              [(Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule [] `g_apply_infinity)
                  ","
                  (Tactic.rwRule
                   []
                   (Term.app
                    `h_apply_infinity
                    [(Term.hole "_")
                     (Term.hole "_")
                     (Term.anonymousCtor "⟨" [(Term.hole "_") "," `rfl] "⟩")]))]
                 "]")
                [])])])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                [`eq1 []]
                [(Term.typeSpec
                  ":"
                  («term_=_»
                   (Term.app
                    (Term.app
                     (GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.termh "h")
                     [`b])
                    [(Term.app
                      `from_coset
                      [(Term.anonymousCtor
                        "⟨"
                        [`f.range.carrier
                         ","
                         (Term.anonymousCtor
                          "⟨"
                          [(num "1") "," (Term.app `one_left_coset [(Term.hole "_")])]
                          "⟩")]
                        "⟩")])])
                   "="
                   (Term.app
                    `from_coset
                    [(Term.anonymousCtor
                      "⟨"
                      [`f.range.carrier
                       ","
                       (Term.anonymousCtor
                        "⟨"
                        [(num "1") "," (Term.app `one_left_coset [(Term.hole "_")])]
                        "⟩")]
                      "⟩")])))]
                ":="
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(Tactic.simp
                     "simp"
                     []
                     []
                     []
                     ["["
                      [(Tactic.simpLemma [] [] `H)
                       ","
                       (Tactic.simpLemma [] [] `tau)
                       ","
                       (Tactic.simpLemma [] [] `g_apply_infinity)]
                      "]"]
                     [])]))))))
             []
             (Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                [`eq2 []]
                [(Term.typeSpec
                  ":"
                  («term_=_»
                   (Term.app
                    (Term.app
                     (GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.termg "g")
                     [`b])
                    [(Term.app
                      `from_coset
                      [(Term.anonymousCtor
                        "⟨"
                        [`f.range.carrier
                         ","
                         (Term.anonymousCtor
                          "⟨"
                          [(num "1") "," (Term.app `one_left_coset [(Term.hole "_")])]
                          "⟩")]
                        "⟩")])])
                   "="
                   (Term.app
                    `from_coset
                    [(Term.anonymousCtor
                      "⟨"
                      [(Coset.GroupTheory.Coset.left_coset `b " *l " `f.range.carrier)
                       ","
                       (Term.anonymousCtor "⟨" [`b "," `rfl] "⟩")]
                      "⟩")])))]
                ":="
                `rfl)))
             []
             (Tactic.exact
              "exact"
              (Term.app
               (Term.proj (Term.app `from_coset_ne_of_nin_range [(Term.hole "_") `r]) "." `symm)
               [(Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(Tactic.rwSeq
                     "rw"
                     []
                     (Tactic.rwRuleSeq
                      "["
                      [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `eq1)
                       ","
                       (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `eq2)
                       ","
                       (Tactic.rwRule [] (Term.app `FunLike.congr_fun [`hb]))]
                      "]")
                     [])])))]))])])))
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
            `Set.ext
            [(Term.fun
              "fun"
              (Term.basicFun
               [`b]
               []
               "=>"
               (Term.anonymousCtor
                "⟨"
                [(Term.hole "_")
                 ","
                 (Term.fun
                  "fun"
                  (Term.basicFun
                   [`hb]
                   [(Term.typeSpec
                     ":"
                     («term_=_»
                      (Term.app
                       (GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.termh "h")
                       [`b])
                      "="
                      (Term.app
                       (GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.termg "g")
                       [`b])))]
                   "=>"
                   (Term.app
                    `by_contradiction
                    [(Term.fun "fun" (Term.basicFun [`r] [] "=>" (Term.hole "_")))])))]
                "⟩")))]))
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Std.Tactic.rintro
             "rintro"
             [(Std.Tactic.RCases.rintroPat.one
               (Std.Tactic.RCases.rcasesPat.tuple
                "⟨"
                [(Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `a)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                  [])]
                "⟩"))]
             [])
            []
            (Tactic.change
             "change"
             («term_=_»
              (Term.app
               (GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.termh "h")
               [(Term.app `f [`a])])
              "="
              (Term.app
               (GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.termg "g")
               [(Term.app `f [`a])]))
             [])
            []
            (Std.Tactic.Ext.«tacticExt___:_»
             "ext"
             [(Std.Tactic.RCases.rintroPat.one
               (Std.Tactic.RCases.rcasesPat.tuple
                "⟨"
                [(Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed
                   [(Std.Tactic.RCases.rcasesPat.tuple
                     "⟨"
                     [(Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.ignore "_")])
                       [])
                      ","
                      (Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed
                        [(Std.Tactic.RCases.rcasesPat.tuple
                          "⟨"
                          [(Std.Tactic.RCases.rcasesPatLo
                            (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `y)])
                            [])
                           ","
                           (Std.Tactic.RCases.rcasesPatLo
                            (Std.Tactic.RCases.rcasesPatMed
                             [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                            [])]
                          "⟩")])
                       [])]
                     "⟩")])
                  [])]
                "⟩"))]
             [])
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(Tactic.rwSeq
               "rw"
               []
               (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `g_apply_from_coset)] "]")
               [])
              []
              (Classical.«tacticBy_cases_:_» "by_cases" [`m ":"] («term_∈_» `y "∈" `f.range))
              []
              (tactic__
               (cdotTk (patternIgnore (token.«· » "·")))
               [(Tactic.rwSeq
                 "rw"
                 []
                 (Tactic.rwRuleSeq
                  "["
                  [(Tactic.rwRule
                    []
                    (Term.app
                     `h_apply_from_coset'
                     [(Term.hole "_") (Term.hole "_") (Term.hole "_") `m]))
                   ","
                   (Tactic.rwRule [] (Term.app `from_coset_eq_of_mem_range [(Term.hole "_") `m]))]
                  "]")
                 [])
                []
                (Tactic.change
                 "change"
                 («term_=_»
                  (Term.app `from_coset [(Term.hole "_")])
                  "="
                  (Term.app
                   `from_coset
                   [(Term.anonymousCtor
                     "⟨"
                     [(Coset.GroupTheory.Coset.left_coset
                       (Term.app `f [`a])
                       " *l "
                       (Coset.GroupTheory.Coset.left_coset `y " *l " (Term.hole "_")))
                      ","
                      (Term.hole "_")]
                     "⟩")]))
                 [])
                []
                (Std.Tactic.Simpa.simpa
                 "simpa"
                 []
                 []
                 (Std.Tactic.Simpa.simpaArgsRest
                  []
                  []
                  ["only"]
                  [(Tactic.simpArgs
                    "["
                    [(Tactic.simpLemma
                      []
                      [(patternIgnore (token.«← » "←"))]
                      (Term.app
                       `from_coset_eq_of_mem_range
                       [(Term.hole "_")
                        (Term.app
                         `Subgroup.mul_mem
                         [(Term.hole "_") (Term.anonymousCtor "⟨" [`a "," `rfl] "⟩") `m])]))
                     ","
                     (Tactic.simpLemma [] [] `left_coset_assoc)]
                    "]")]
                  []))])
              []
              (tactic__
               (cdotTk (patternIgnore (token.«· » "·")))
               [(Tactic.rwSeq
                 "rw"
                 []
                 (Tactic.rwRuleSeq
                  "["
                  [(Tactic.rwRule
                    []
                    (Term.app
                     `h_apply_from_coset_nin_range
                     [(Term.hole "_")
                      (Term.hole "_")
                      (Term.anonymousCtor "⟨" [(Term.hole "_") "," `rfl] "⟩")
                      (Term.hole "_")
                      `m]))]
                  "]")
                 [])
                []
                (Std.Tactic.Simpa.simpa
                 "simpa"
                 []
                 []
                 (Std.Tactic.Simpa.simpaArgsRest
                  []
                  []
                  ["only"]
                  [(Tactic.simpArgs
                    "["
                    [(Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `Subtype.val_eq_coe)
                     ","
                     (Tactic.simpLemma [] [] `left_coset_assoc)]
                    "]")]
                  []))])])
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(Tactic.rwSeq
               "rw"
               []
               (Tactic.rwRuleSeq
                "["
                [(Tactic.rwRule [] `g_apply_infinity)
                 ","
                 (Tactic.rwRule
                  []
                  (Term.app
                   `h_apply_infinity
                   [(Term.hole "_")
                    (Term.hole "_")
                    (Term.anonymousCtor "⟨" [(Term.hole "_") "," `rfl] "⟩")]))]
                "]")
               [])])])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               [`eq1 []]
               [(Term.typeSpec
                 ":"
                 («term_=_»
                  (Term.app
                   (Term.app
                    (GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.termh "h")
                    [`b])
                   [(Term.app
                     `from_coset
                     [(Term.anonymousCtor
                       "⟨"
                       [`f.range.carrier
                        ","
                        (Term.anonymousCtor
                         "⟨"
                         [(num "1") "," (Term.app `one_left_coset [(Term.hole "_")])]
                         "⟩")]
                       "⟩")])])
                  "="
                  (Term.app
                   `from_coset
                   [(Term.anonymousCtor
                     "⟨"
                     [`f.range.carrier
                      ","
                      (Term.anonymousCtor
                       "⟨"
                       [(num "1") "," (Term.app `one_left_coset [(Term.hole "_")])]
                       "⟩")]
                     "⟩")])))]
               ":="
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(Tactic.simp
                    "simp"
                    []
                    []
                    []
                    ["["
                     [(Tactic.simpLemma [] [] `H)
                      ","
                      (Tactic.simpLemma [] [] `tau)
                      ","
                      (Tactic.simpLemma [] [] `g_apply_infinity)]
                     "]"]
                    [])]))))))
            []
            (Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               [`eq2 []]
               [(Term.typeSpec
                 ":"
                 («term_=_»
                  (Term.app
                   (Term.app
                    (GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.termg "g")
                    [`b])
                   [(Term.app
                     `from_coset
                     [(Term.anonymousCtor
                       "⟨"
                       [`f.range.carrier
                        ","
                        (Term.anonymousCtor
                         "⟨"
                         [(num "1") "," (Term.app `one_left_coset [(Term.hole "_")])]
                         "⟩")]
                       "⟩")])])
                  "="
                  (Term.app
                   `from_coset
                   [(Term.anonymousCtor
                     "⟨"
                     [(Coset.GroupTheory.Coset.left_coset `b " *l " `f.range.carrier)
                      ","
                      (Term.anonymousCtor "⟨" [`b "," `rfl] "⟩")]
                     "⟩")])))]
               ":="
               `rfl)))
            []
            (Tactic.exact
             "exact"
             (Term.app
              (Term.proj (Term.app `from_coset_ne_of_nin_range [(Term.hole "_") `r]) "." `symm)
              [(Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(Tactic.rwSeq
                    "rw"
                    []
                    (Tactic.rwRuleSeq
                     "["
                     [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `eq1)
                      ","
                      (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `eq2)
                      ","
                      (Tactic.rwRule [] (Term.app `FunLike.congr_fun [`hb]))]
                     "]")
                    [])])))]))])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`eq1 []]
           [(Term.typeSpec
             ":"
             («term_=_»
              (Term.app
               (Term.app
                (GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.termh "h")
                [`b])
               [(Term.app
                 `from_coset
                 [(Term.anonymousCtor
                   "⟨"
                   [`f.range.carrier
                    ","
                    (Term.anonymousCtor
                     "⟨"
                     [(num "1") "," (Term.app `one_left_coset [(Term.hole "_")])]
                     "⟩")]
                   "⟩")])])
              "="
              (Term.app
               `from_coset
               [(Term.anonymousCtor
                 "⟨"
                 [`f.range.carrier
                  ","
                  (Term.anonymousCtor
                   "⟨"
                   [(num "1") "," (Term.app `one_left_coset [(Term.hole "_")])]
                   "⟩")]
                 "⟩")])))]
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.simp
                "simp"
                []
                []
                []
                ["["
                 [(Tactic.simpLemma [] [] `H)
                  ","
                  (Tactic.simpLemma [] [] `tau)
                  ","
                  (Tactic.simpLemma [] [] `g_apply_infinity)]
                 "]"]
                [])]))))))
        []
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`eq2 []]
           [(Term.typeSpec
             ":"
             («term_=_»
              (Term.app
               (Term.app
                (GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.termg "g")
                [`b])
               [(Term.app
                 `from_coset
                 [(Term.anonymousCtor
                   "⟨"
                   [`f.range.carrier
                    ","
                    (Term.anonymousCtor
                     "⟨"
                     [(num "1") "," (Term.app `one_left_coset [(Term.hole "_")])]
                     "⟩")]
                   "⟩")])])
              "="
              (Term.app
               `from_coset
               [(Term.anonymousCtor
                 "⟨"
                 [(Coset.GroupTheory.Coset.left_coset `b " *l " `f.range.carrier)
                  ","
                  (Term.anonymousCtor "⟨" [`b "," `rfl] "⟩")]
                 "⟩")])))]
           ":="
           `rfl)))
        []
        (Tactic.exact
         "exact"
         (Term.app
          (Term.proj (Term.app `from_coset_ne_of_nin_range [(Term.hole "_") `r]) "." `symm)
          [(Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `eq1)
                  ","
                  (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `eq2)
                  ","
                  (Tactic.rwRule [] (Term.app `FunLike.congr_fun [`hb]))]
                 "]")
                [])])))]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.app
        (Term.proj (Term.app `from_coset_ne_of_nin_range [(Term.hole "_") `r]) "." `symm)
        [(Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `eq1)
                ","
                (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `eq2)
                ","
                (Tactic.rwRule [] (Term.app `FunLike.congr_fun [`hb]))]
               "]")
              [])])))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj (Term.app `from_coset_ne_of_nin_range [(Term.hole "_") `r]) "." `symm)
       [(Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `eq1)
               ","
               (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `eq2)
               ","
               (Tactic.rwRule [] (Term.app `FunLike.congr_fun [`hb]))]
              "]")
             [])])))])
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
            [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `eq1)
             ","
             (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `eq2)
             ","
             (Tactic.rwRule [] (Term.app `FunLike.congr_fun [`hb]))]
            "]")
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `eq1)
         ","
         (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `eq2)
         ","
         (Tactic.rwRule [] (Term.app `FunLike.congr_fun [`hb]))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `FunLike.congr_fun [`hb])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hb
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `FunLike.congr_fun
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `eq2
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `eq1
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
        [(Tactic.rwSeq
          "rw"
          []
          (Tactic.rwRuleSeq
           "["
           [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `eq1)
            ","
            (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `eq2)
            ","
            (Tactic.rwRule [] (Term.app `FunLike.congr_fun [`hb]))]
           "]")
          [])])))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app `from_coset_ne_of_nin_range [(Term.hole "_") `r]) "." `symm)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `from_coset_ne_of_nin_range [(Term.hole "_") `r])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `r
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `from_coset_ne_of_nin_range
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `from_coset_ne_of_nin_range [(Term.hole "_") `r])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`eq2 []]
         [(Term.typeSpec
           ":"
           («term_=_»
            (Term.app
             (Term.app
              (GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.termg "g")
              [`b])
             [(Term.app
               `from_coset
               [(Term.anonymousCtor
                 "⟨"
                 [`f.range.carrier
                  ","
                  (Term.anonymousCtor
                   "⟨"
                   [(num "1") "," (Term.app `one_left_coset [(Term.hole "_")])]
                   "⟩")]
                 "⟩")])])
            "="
            (Term.app
             `from_coset
             [(Term.anonymousCtor
               "⟨"
               [(Coset.GroupTheory.Coset.left_coset `b " *l " `f.range.carrier)
                ","
                (Term.anonymousCtor "⟨" [`b "," `rfl] "⟩")]
               "⟩")])))]
         ":="
         `rfl)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rfl
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Term.app
        (Term.app (GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.termg "g") [`b])
        [(Term.app
          `from_coset
          [(Term.anonymousCtor
            "⟨"
            [`f.range.carrier
             ","
             (Term.anonymousCtor
              "⟨"
              [(num "1") "," (Term.app `one_left_coset [(Term.hole "_")])]
              "⟩")]
            "⟩")])])
       "="
       (Term.app
        `from_coset
        [(Term.anonymousCtor
          "⟨"
          [(Coset.GroupTheory.Coset.left_coset `b " *l " `f.range.carrier)
           ","
           (Term.anonymousCtor "⟨" [`b "," `rfl] "⟩")]
          "⟩")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `from_coset
       [(Term.anonymousCtor
         "⟨"
         [(Coset.GroupTheory.Coset.left_coset `b " *l " `f.range.carrier)
          ","
          (Term.anonymousCtor "⟨" [`b "," `rfl] "⟩")]
         "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Coset.GroupTheory.Coset.left_coset `b " *l " `f.range.carrier)
        ","
        (Term.anonymousCtor "⟨" [`b "," `rfl] "⟩")]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [`b "," `rfl] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rfl
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `b
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Coset.GroupTheory.Coset.left_coset `b " *l " `f.range.carrier)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f.range.carrier
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `b
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `from_coset
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app
       (Term.app (GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.termg "g") [`b])
       [(Term.app
         `from_coset
         [(Term.anonymousCtor
           "⟨"
           [`f.range.carrier
            ","
            (Term.anonymousCtor
             "⟨"
             [(num "1") "," (Term.app `one_left_coset [(Term.hole "_")])]
             "⟩")]
           "⟩")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `from_coset
       [(Term.anonymousCtor
         "⟨"
         [`f.range.carrier
          ","
          (Term.anonymousCtor "⟨" [(num "1") "," (Term.app `one_left_coset [(Term.hole "_")])] "⟩")]
         "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [`f.range.carrier
        ","
        (Term.anonymousCtor "⟨" [(num "1") "," (Term.app `one_left_coset [(Term.hole "_")])] "⟩")]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [(num "1") "," (Term.app `one_left_coset [(Term.hole "_")])] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `one_left_coset [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `one_left_coset
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f.range.carrier
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `from_coset
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `from_coset
      [(Term.anonymousCtor
        "⟨"
        [`f.range.carrier
         ","
         (Term.anonymousCtor "⟨" [(num "1") "," (Term.app `one_left_coset [(Term.hole "_")])] "⟩")]
        "⟩")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.app (GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.termg "g") [`b])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `b
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.termg "g")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.termg', expected 'GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.termg._@.Algebra.Category.GroupCat.EpiMono._hyg.3172'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.letPatDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveEqnsDecl'
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
  agree
  : f . range . carrier = { x | h x = g x }
  :=
    by
      refine' Set.ext fun b => ⟨ _ , fun hb : h b = g b => by_contradiction fun r => _ ⟩
        ·
          rintro ⟨ a , rfl ⟩
            change h f a = g f a
            ext ⟨ ⟨ _ , ⟨ y , rfl ⟩ ⟩ ⟩
            ·
              rw [ g_apply_from_coset ]
                by_cases m : y ∈ f.range
                ·
                  rw [ h_apply_from_coset' _ _ _ m , from_coset_eq_of_mem_range _ m ]
                    change from_coset _ = from_coset ⟨ f a *l y *l _ , _ ⟩
                    simpa
                      only
                        [
                          ← from_coset_eq_of_mem_range _ Subgroup.mul_mem _ ⟨ a , rfl ⟩ m
                            ,
                            left_coset_assoc
                          ]
                ·
                  rw [ h_apply_from_coset_nin_range _ _ ⟨ _ , rfl ⟩ _ m ]
                    simpa only [ ← Subtype.val_eq_coe , left_coset_assoc ]
            · rw [ g_apply_infinity , h_apply_infinity _ _ ⟨ _ , rfl ⟩ ]
        ·
          have
              eq1
                :
                  h b from_coset ⟨ f.range.carrier , ⟨ 1 , one_left_coset _ ⟩ ⟩
                    =
                    from_coset ⟨ f.range.carrier , ⟨ 1 , one_left_coset _ ⟩ ⟩
                :=
                by simp [ H , tau , g_apply_infinity ]
            have
              eq2
                :
                  g b from_coset ⟨ f.range.carrier , ⟨ 1 , one_left_coset _ ⟩ ⟩
                    =
                    from_coset ⟨ b *l f.range.carrier , ⟨ b , rfl ⟩ ⟩
                :=
                rfl
            exact
              from_coset_ne_of_nin_range _ r . symm by rw [ ← eq1 , ← eq2 , FunLike.congr_fun hb ]
#align Group.surjective_of_epi_auxs.agree GroupCat.SurjectiveOfEpiAuxs.agree

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `comp_eq [])
      (Command.declSig
       []
       (Term.typeSpec
        ":"
        («term_=_»
         (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
          `f
          " ≫ "
          (Term.show
           "show"
           (Combinatorics.Quiver.Basic.«term_⟶_»
            `B
            " ⟶ "
            (Term.app
             `GroupCat.of
             [(GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.termSX' "SX'")]))
           (Term.fromTerm
            "from"
            (GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.termg "g"))))
         "="
         (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
          `f
          " ≫ "
          (GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.termh "h")))))
      (Command.declValSimple
       ":="
       (Term.app
        (Term.app `FunLike.ext [(Term.hole "_") (Term.hole "_")])
        [(Term.fun
          "fun"
          (Term.basicFun
           [`a]
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
                ["only"]
                ["["
                 [(Tactic.simpLemma [] [] `comp_apply)
                  ","
                  (Tactic.simpLemma
                   []
                   []
                   (Term.show
                    "show"
                    («term_=_»
                     (Term.app
                      (GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.termh "h")
                      [(Term.app `f [`a])])
                     "="
                     (Term.hole "_"))
                    (Term.fromTerm
                     "from"
                     (Term.typeAscription
                      "("
                      (Term.byTactic
                       "by"
                       (Tactic.tacticSeq
                        (Tactic.tacticSeq1Indented
                         [(Tactic.simp
                           "simp"
                           []
                           []
                           []
                           ["["
                            [(Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `agree)]
                            "]"]
                           [])])))
                      ":"
                      [(«term_∈_»
                        (Term.app `f [`a])
                        "∈"
                        (Set.«term{_|_}»
                         "{"
                         (Std.ExtendedBinder.extBinder (Lean.binderIdent `b) [])
                         "|"
                         («term_=_»
                          (Term.app
                           (GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.termh
                            "h")
                           [`b])
                          "="
                          (Term.app
                           (GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.termg
                            "g")
                           [`b]))
                         "}"))]
                      ")"))))]
                 "]"]
                [])])))))])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.app `FunLike.ext [(Term.hole "_") (Term.hole "_")])
       [(Term.fun
         "fun"
         (Term.basicFun
          [`a]
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
               ["only"]
               ["["
                [(Tactic.simpLemma [] [] `comp_apply)
                 ","
                 (Tactic.simpLemma
                  []
                  []
                  (Term.show
                   "show"
                   («term_=_»
                    (Term.app
                     (GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.termh "h")
                     [(Term.app `f [`a])])
                    "="
                    (Term.hole "_"))
                   (Term.fromTerm
                    "from"
                    (Term.typeAscription
                     "("
                     (Term.byTactic
                      "by"
                      (Tactic.tacticSeq
                       (Tactic.tacticSeq1Indented
                        [(Tactic.simp
                          "simp"
                          []
                          []
                          []
                          ["["
                           [(Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `agree)]
                           "]"]
                          [])])))
                     ":"
                     [(«term_∈_»
                       (Term.app `f [`a])
                       "∈"
                       (Set.«term{_|_}»
                        "{"
                        (Std.ExtendedBinder.extBinder (Lean.binderIdent `b) [])
                        "|"
                        («term_=_»
                         (Term.app
                          (GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.termh "h")
                          [`b])
                         "="
                         (Term.app
                          (GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.termg "g")
                          [`b]))
                        "}"))]
                     ")"))))]
                "]"]
               [])])))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`a]
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
             ["only"]
             ["["
              [(Tactic.simpLemma [] [] `comp_apply)
               ","
               (Tactic.simpLemma
                []
                []
                (Term.show
                 "show"
                 («term_=_»
                  (Term.app
                   (GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.termh "h")
                   [(Term.app `f [`a])])
                  "="
                  (Term.hole "_"))
                 (Term.fromTerm
                  "from"
                  (Term.typeAscription
                   "("
                   (Term.byTactic
                    "by"
                    (Tactic.tacticSeq
                     (Tactic.tacticSeq1Indented
                      [(Tactic.simp
                        "simp"
                        []
                        []
                        []
                        ["[" [(Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `agree)] "]"]
                        [])])))
                   ":"
                   [(«term_∈_»
                     (Term.app `f [`a])
                     "∈"
                     (Set.«term{_|_}»
                      "{"
                      (Std.ExtendedBinder.extBinder (Lean.binderIdent `b) [])
                      "|"
                      («term_=_»
                       (Term.app
                        (GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.termh "h")
                        [`b])
                       "="
                       (Term.app
                        (GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.termg "g")
                        [`b]))
                      "}"))]
                   ")"))))]
              "]"]
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
           ["only"]
           ["["
            [(Tactic.simpLemma [] [] `comp_apply)
             ","
             (Tactic.simpLemma
              []
              []
              (Term.show
               "show"
               («term_=_»
                (Term.app
                 (GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.termh "h")
                 [(Term.app `f [`a])])
                "="
                (Term.hole "_"))
               (Term.fromTerm
                "from"
                (Term.typeAscription
                 "("
                 (Term.byTactic
                  "by"
                  (Tactic.tacticSeq
                   (Tactic.tacticSeq1Indented
                    [(Tactic.simp
                      "simp"
                      []
                      []
                      []
                      ["[" [(Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `agree)] "]"]
                      [])])))
                 ":"
                 [(«term_∈_»
                   (Term.app `f [`a])
                   "∈"
                   (Set.«term{_|_}»
                    "{"
                    (Std.ExtendedBinder.extBinder (Lean.binderIdent `b) [])
                    "|"
                    («term_=_»
                     (Term.app
                      (GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.termh "h")
                      [`b])
                     "="
                     (Term.app
                      (GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.termg "g")
                      [`b]))
                    "}"))]
                 ")"))))]
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
        [(Tactic.simpLemma [] [] `comp_apply)
         ","
         (Tactic.simpLemma
          []
          []
          (Term.show
           "show"
           («term_=_»
            (Term.app
             (GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.termh "h")
             [(Term.app `f [`a])])
            "="
            (Term.hole "_"))
           (Term.fromTerm
            "from"
            (Term.typeAscription
             "("
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.simp
                  "simp"
                  []
                  []
                  []
                  ["[" [(Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `agree)] "]"]
                  [])])))
             ":"
             [(«term_∈_»
               (Term.app `f [`a])
               "∈"
               (Set.«term{_|_}»
                "{"
                (Std.ExtendedBinder.extBinder (Lean.binderIdent `b) [])
                "|"
                («term_=_»
                 (Term.app
                  (GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.termh "h")
                  [`b])
                 "="
                 (Term.app
                  (GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.termg "g")
                  [`b]))
                "}"))]
             ")"))))]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.show
       "show"
       («term_=_»
        (Term.app
         (GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.termh "h")
         [(Term.app `f [`a])])
        "="
        (Term.hole "_"))
       (Term.fromTerm
        "from"
        (Term.typeAscription
         "("
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.simp
              "simp"
              []
              []
              []
              ["[" [(Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `agree)] "]"]
              [])])))
         ":"
         [(«term_∈_»
           (Term.app `f [`a])
           "∈"
           (Set.«term{_|_}»
            "{"
            (Std.ExtendedBinder.extBinder (Lean.binderIdent `b) [])
            "|"
            («term_=_»
             (Term.app
              (GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.termh "h")
              [`b])
             "="
             (Term.app
              (GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.termg "g")
              [`b]))
            "}"))]
         ")")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription
       "("
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.simp
            "simp"
            []
            []
            []
            ["[" [(Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `agree)] "]"]
            [])])))
       ":"
       [(«term_∈_»
         (Term.app `f [`a])
         "∈"
         (Set.«term{_|_}»
          "{"
          (Std.ExtendedBinder.extBinder (Lean.binderIdent `b) [])
          "|"
          («term_=_»
           (Term.app
            (GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.termh "h")
            [`b])
           "="
           (Term.app
            (GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.termg "g")
            [`b]))
          "}"))]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∈_»
       (Term.app `f [`a])
       "∈"
       (Set.«term{_|_}»
        "{"
        (Std.ExtendedBinder.extBinder (Lean.binderIdent `b) [])
        "|"
        («term_=_»
         (Term.app (GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.termh "h") [`b])
         "="
         (Term.app (GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.termg "g") [`b]))
        "}"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Set.«term{_|_}»
       "{"
       (Std.ExtendedBinder.extBinder (Lean.binderIdent `b) [])
       "|"
       («term_=_»
        (Term.app (GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.termh "h") [`b])
        "="
        (Term.app (GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.termg "g") [`b]))
       "}")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Term.app (GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.termh "h") [`b])
       "="
       (Term.app (GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.termg "g") [`b]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.termg "g") [`b])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `b
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.termg "g")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.termg', expected 'GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.termg._@.Algebra.Category.GroupCat.EpiMono._hyg.3172'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fromTerm', expected 'Lean.Parser.Term.byTactic''
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts'
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
  comp_eq
  : f ≫ show B ⟶ GroupCat.of SX' from g = f ≫ h
  :=
    FunLike.ext _ _
      fun
        a
          =>
          by
            simp
              only
              [ comp_apply , show h f a = _ from ( by simp [ ← agree ] : f a ∈ { b | h b = g b } ) ]
#align Group.surjective_of_epi_auxs.comp_eq GroupCat.SurjectiveOfEpiAuxs.comp_eq

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `g_ne_h [])
      (Command.declSig
       [(Term.explicitBinder "(" [`x] [":" `B] [] ")")
        (Term.explicitBinder "(" [`hx] [":" («term_∉_» `x "∉" (Term.proj `f "." `range))] [] ")")]
       (Term.typeSpec
        ":"
        («term_≠_»
         (GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.termg "g")
         "≠"
         (GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.termh "h"))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.intro "intro" [`r])
           []
           (Mathlib.Tactic.tacticReplace_
            "replace"
            (Term.haveDecl
             (Term.haveIdDecl
              [`r []]
              []
              ":="
              (Term.app
               `FunLike.congr_fun
               [(Term.app `FunLike.congr_fun [`r `x])
                (Term.app
                 `from_coset
                 [(Term.anonymousCtor
                   "⟨"
                   [`f.range
                    ","
                    (Term.anonymousCtor
                     "⟨"
                     [(num "1") "," (Term.app `one_left_coset [(Term.hole "_")])]
                     "⟩")]
                   "⟩")])]))))
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [] `H)
              ","
              (Tactic.rwRule [] `g_apply_from_coset)
              ","
              (Tactic.rwRule [] `MonoidHom.coe_mk)
              ","
              (Tactic.rwRule [] `tau)]
             "]")
            [(Tactic.location "at" (Tactic.locationHyp [`r] []))])
           []
           (Tactic.simp
            "simp"
            []
            []
            ["only"]
            ["["
             [(Tactic.simpLemma [] [] `MonoidHom.coe_range)
              ","
              (Tactic.simpLemma [] [] `Subtype.coe_mk)
              ","
              (Tactic.simpLemma [] [] `Equiv.symm_swap)
              ","
              (Tactic.simpLemma [] [] `Equiv.toFun_as_coe)
              ","
              (Tactic.simpLemma [] [] `Equiv.coe_trans)
              ","
              (Tactic.simpLemma [] [] `Function.comp_apply)]
             "]"]
            [(Tactic.location "at" (Tactic.locationHyp [`r] []))])
           []
           (Tactic.tacticErw__
            "erw"
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [] `Equiv.swap_apply_left)
              ","
              (Tactic.rwRule [] `g_apply_infinity)
              ","
              (Tactic.rwRule [] `Equiv.swap_apply_right)]
             "]")
            [(Tactic.location "at" (Tactic.locationHyp [`r] []))])
           []
           (Tactic.exact
            "exact"
            (Term.app `from_coset_ne_of_nin_range [(Term.hole "_") `hx `r]))])))
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
         [(Tactic.intro "intro" [`r])
          []
          (Mathlib.Tactic.tacticReplace_
           "replace"
           (Term.haveDecl
            (Term.haveIdDecl
             [`r []]
             []
             ":="
             (Term.app
              `FunLike.congr_fun
              [(Term.app `FunLike.congr_fun [`r `x])
               (Term.app
                `from_coset
                [(Term.anonymousCtor
                  "⟨"
                  [`f.range
                   ","
                   (Term.anonymousCtor
                    "⟨"
                    [(num "1") "," (Term.app `one_left_coset [(Term.hole "_")])]
                    "⟩")]
                  "⟩")])]))))
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `H)
             ","
             (Tactic.rwRule [] `g_apply_from_coset)
             ","
             (Tactic.rwRule [] `MonoidHom.coe_mk)
             ","
             (Tactic.rwRule [] `tau)]
            "]")
           [(Tactic.location "at" (Tactic.locationHyp [`r] []))])
          []
          (Tactic.simp
           "simp"
           []
           []
           ["only"]
           ["["
            [(Tactic.simpLemma [] [] `MonoidHom.coe_range)
             ","
             (Tactic.simpLemma [] [] `Subtype.coe_mk)
             ","
             (Tactic.simpLemma [] [] `Equiv.symm_swap)
             ","
             (Tactic.simpLemma [] [] `Equiv.toFun_as_coe)
             ","
             (Tactic.simpLemma [] [] `Equiv.coe_trans)
             ","
             (Tactic.simpLemma [] [] `Function.comp_apply)]
            "]"]
           [(Tactic.location "at" (Tactic.locationHyp [`r] []))])
          []
          (Tactic.tacticErw__
           "erw"
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `Equiv.swap_apply_left)
             ","
             (Tactic.rwRule [] `g_apply_infinity)
             ","
             (Tactic.rwRule [] `Equiv.swap_apply_right)]
            "]")
           [(Tactic.location "at" (Tactic.locationHyp [`r] []))])
          []
          (Tactic.exact "exact" (Term.app `from_coset_ne_of_nin_range [(Term.hole "_") `hx `r]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" (Term.app `from_coset_ne_of_nin_range [(Term.hole "_") `hx `r]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `from_coset_ne_of_nin_range [(Term.hole "_") `hx `r])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `r
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hx
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `from_coset_ne_of_nin_range
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticErw__
       "erw"
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `Equiv.swap_apply_left)
         ","
         (Tactic.rwRule [] `g_apply_infinity)
         ","
         (Tactic.rwRule [] `Equiv.swap_apply_right)]
        "]")
       [(Tactic.location "at" (Tactic.locationHyp [`r] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `r
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Equiv.swap_apply_right
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g_apply_infinity
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Equiv.swap_apply_left
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["["
        [(Tactic.simpLemma [] [] `MonoidHom.coe_range)
         ","
         (Tactic.simpLemma [] [] `Subtype.coe_mk)
         ","
         (Tactic.simpLemma [] [] `Equiv.symm_swap)
         ","
         (Tactic.simpLemma [] [] `Equiv.toFun_as_coe)
         ","
         (Tactic.simpLemma [] [] `Equiv.coe_trans)
         ","
         (Tactic.simpLemma [] [] `Function.comp_apply)]
        "]"]
       [(Tactic.location "at" (Tactic.locationHyp [`r] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `r
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Function.comp_apply
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Equiv.coe_trans
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Equiv.toFun_as_coe
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Equiv.symm_swap
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Subtype.coe_mk
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `MonoidHom.coe_range
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `H)
         ","
         (Tactic.rwRule [] `g_apply_from_coset)
         ","
         (Tactic.rwRule [] `MonoidHom.coe_mk)
         ","
         (Tactic.rwRule [] `tau)]
        "]")
       [(Tactic.location "at" (Tactic.locationHyp [`r] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `r
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `tau
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `MonoidHom.coe_mk
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g_apply_from_coset
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `H
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.tacticReplace_
       "replace"
       (Term.haveDecl
        (Term.haveIdDecl
         [`r []]
         []
         ":="
         (Term.app
          `FunLike.congr_fun
          [(Term.app `FunLike.congr_fun [`r `x])
           (Term.app
            `from_coset
            [(Term.anonymousCtor
              "⟨"
              [`f.range
               ","
               (Term.anonymousCtor
                "⟨"
                [(num "1") "," (Term.app `one_left_coset [(Term.hole "_")])]
                "⟩")]
              "⟩")])]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `FunLike.congr_fun
       [(Term.app `FunLike.congr_fun [`r `x])
        (Term.app
         `from_coset
         [(Term.anonymousCtor
           "⟨"
           [`f.range
            ","
            (Term.anonymousCtor
             "⟨"
             [(num "1") "," (Term.app `one_left_coset [(Term.hole "_")])]
             "⟩")]
           "⟩")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `from_coset
       [(Term.anonymousCtor
         "⟨"
         [`f.range
          ","
          (Term.anonymousCtor "⟨" [(num "1") "," (Term.app `one_left_coset [(Term.hole "_")])] "⟩")]
         "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [`f.range
        ","
        (Term.anonymousCtor "⟨" [(num "1") "," (Term.app `one_left_coset [(Term.hole "_")])] "⟩")]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [(num "1") "," (Term.app `one_left_coset [(Term.hole "_")])] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `one_left_coset [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `one_left_coset
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f.range
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `from_coset
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `from_coset
      [(Term.anonymousCtor
        "⟨"
        [`f.range
         ","
         (Term.anonymousCtor "⟨" [(num "1") "," (Term.app `one_left_coset [(Term.hole "_")])] "⟩")]
        "⟩")])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `FunLike.congr_fun [`r `x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `r
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `FunLike.congr_fun
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `FunLike.congr_fun [`r `x])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `FunLike.congr_fun
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.intro "intro" [`r])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `r
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_≠_»
       (GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.termg "g")
       "≠"
       (GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.termh "h"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.termh "h")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.termh', expected 'GroupCat.SurjectiveOfEpiAuxs.Algebra.Category.GroupCat.EpiMono.termh._@.Algebra.Category.GroupCat.EpiMono._hyg.3686'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  g_ne_h
  ( x : B ) ( hx : x ∉ f . range ) : g ≠ h
  :=
    by
      intro r
        replace
          r
            :=
            FunLike.congr_fun
              FunLike.congr_fun r x from_coset ⟨ f.range , ⟨ 1 , one_left_coset _ ⟩ ⟩
        rw [ H , g_apply_from_coset , MonoidHom.coe_mk , tau ] at r
        simp
          only
          [
            MonoidHom.coe_range
              ,
              Subtype.coe_mk
              ,
              Equiv.symm_swap
              ,
              Equiv.toFun_as_coe
              ,
              Equiv.coe_trans
              ,
              Function.comp_apply
            ]
          at r
        erw [ Equiv.swap_apply_left , g_apply_infinity , Equiv.swap_apply_right ] at r
        exact from_coset_ne_of_nin_range _ hx r
#align Group.surjective_of_epi_auxs.g_ne_h GroupCat.SurjectiveOfEpiAuxs.g_ne_h

end SurjectiveOfEpiAuxs

theorem surjective_of_epi [Epi f] : Function.Surjective f :=
  by
  by_contra r
  push_neg  at r
  rcases r with ⟨b, hb⟩
  exact
    surjective_of_epi_auxs.g_ne_h f b (fun ⟨c, hc⟩ => hb _ hc)
      ((cancel_epi f).1 (surjective_of_epi_auxs.comp_eq f))
#align Group.surjective_of_epi GroupCat.surjective_of_epi

theorem epi_iff_surjective : Epi f ↔ Function.Surjective f :=
  ⟨fun h => @surjective_of_epi f h, ConcreteCategory.epi_of_surjective _⟩
#align Group.epi_iff_surjective GroupCat.epi_iff_surjective

theorem epi_iff_range_eq_top : Epi f ↔ f.range = ⊤ :=
  Iff.trans (epi_iff_surjective _) (Subgroup.eq_top_iff' f.range).symm
#align Group.epi_iff_range_eq_top GroupCat.epi_iff_range_eq_top

end GroupCat

namespace AddGroupCat

variable {A B : AddGroupCat.{u}} (f : A ⟶ B)

theorem epi_iff_surjective : Epi f ↔ Function.Surjective f :=
  by
  have i1 : epi f ↔ epi (Group_AddGroup_equivalence.inverse.map f) :=
    by
    refine' ⟨_, Group_AddGroup_equivalence.inverse.epi_of_epi_map⟩
    intro e'
    apply Group_AddGroup_equivalence.inverse.map_epi
  rwa [GroupCat.epi_iff_surjective] at i1
#align AddGroup.epi_iff_surjective AddGroupCat.epi_iff_surjective

theorem epi_iff_range_eq_top : Epi f ↔ f.range = ⊤ :=
  Iff.trans (epi_iff_surjective _) (AddSubgroup.eq_top_iff' f.range).symm
#align AddGroup.epi_iff_range_eq_top AddGroupCat.epi_iff_range_eq_top

end AddGroupCat

namespace GroupCat

variable {A B : GroupCat.{u}} (f : A ⟶ B)

@[to_additive]
instance forget_Group_preserves_mono : (forget GroupCat).PreservesMonomorphisms
    where preserves X Y f e := by rwa [mono_iff_injective, ← CategoryTheory.mono_iff_injective] at e
#align Group.forget_Group_preserves_mono GroupCat.forget_Group_preserves_mono

@[to_additive]
instance forget_Group_preserves_epi : (forget GroupCat).PreservesEpimorphisms
    where preserves X Y f e := by rwa [epi_iff_surjective, ← CategoryTheory.epi_iff_surjective] at e
#align Group.forget_Group_preserves_epi GroupCat.forget_Group_preserves_epi

end GroupCat

namespace CommGroupCat

variable {A B : CommGroupCat.{u}} (f : A ⟶ B)

@[to_additive AddCommGroupCat.ker_eq_bot_of_mono]
theorem ker_eq_bot_of_mono [Mono f] : f.ker = ⊥ :=
  MonoidHom.ker_eq_bot_of_cancel fun u v =>
    (@cancel_mono _ _ _ _ _ f _ (show CommGroupCat.of f.ker ⟶ A from u) _).1
#align CommGroup.ker_eq_bot_of_mono CommGroupCat.ker_eq_bot_of_mono

@[to_additive AddCommGroupCat.mono_iff_ker_eq_bot]
theorem mono_iff_ker_eq_bot : Mono f ↔ f.ker = ⊥ :=
  ⟨fun h => @ker_eq_bot_of_mono f h, fun h =>
    ConcreteCategory.mono_of_injective _ <| (MonoidHom.ker_eq_bot_iff f).1 h⟩
#align CommGroup.mono_iff_ker_eq_bot CommGroupCat.mono_iff_ker_eq_bot

@[to_additive AddCommGroupCat.mono_iff_injective]
theorem mono_iff_injective : Mono f ↔ Function.Injective f :=
  Iff.trans (mono_iff_ker_eq_bot f) <| MonoidHom.ker_eq_bot_iff f
#align CommGroup.mono_iff_injective CommGroupCat.mono_iff_injective

@[to_additive]
theorem range_eq_top_of_epi [Epi f] : f.range = ⊤ :=
  MonoidHom.range_eq_top_of_cancel fun u v h =>
    (@cancel_epi _ _ _ _ _ f _ (show B ⟶ ⟨B ⧸ MonoidHom.range f⟩ from u) v).1 h
#align CommGroup.range_eq_top_of_epi CommGroupCat.range_eq_top_of_epi

@[to_additive]
theorem epi_iff_range_eq_top : Epi f ↔ f.range = ⊤ :=
  ⟨fun hf => range_eq_top_of_epi _, fun hf =>
    ConcreteCategory.epi_of_surjective _ <| MonoidHom.range_top_iff_surjective.mp hf⟩
#align CommGroup.epi_iff_range_eq_top CommGroupCat.epi_iff_range_eq_top

@[to_additive]
theorem epi_iff_surjective : Epi f ↔ Function.Surjective f := by
  rw [epi_iff_range_eq_top, MonoidHom.range_top_iff_surjective]
#align CommGroup.epi_iff_surjective CommGroupCat.epi_iff_surjective

@[to_additive]
instance forget_CommGroup_preserves_mono : (forget CommGroupCat).PreservesMonomorphisms
    where preserves X Y f e := by rwa [mono_iff_injective, ← CategoryTheory.mono_iff_injective] at e
#align CommGroup.forget_CommGroup_preserves_mono CommGroupCat.forget_CommGroup_preserves_mono

@[to_additive]
instance forget_CommGroup_preserves_epi : (forget CommGroupCat).PreservesEpimorphisms
    where preserves X Y f e := by rwa [epi_iff_surjective, ← CategoryTheory.epi_iff_surjective] at e
#align CommGroup.forget_CommGroup_preserves_epi CommGroupCat.forget_CommGroup_preserves_epi

end CommGroupCat

end

