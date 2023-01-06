/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel

! This file was ported from Lean 3 source module topology.metric_space.gromov_hausdorff
! leanprover-community/mathlib commit 26f081a2fb920140ed5bc5cc5344e84bcc7cb2b2
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.SetTheory.Cardinal.Basic
import Mathbin.Topology.MetricSpace.Closeds
import Mathbin.Topology.MetricSpace.Completion
import Mathbin.Topology.MetricSpace.GromovHausdorffRealized
import Mathbin.Topology.MetricSpace.Kuratowski

/-!
# Gromov-Hausdorff distance

This file defines the Gromov-Hausdorff distance on the space of nonempty compact metric spaces
up to isometry.

We introduce the space of all nonempty compact metric spaces, up to isometry,
called `GH_space`, and endow it with a metric space structure. The distance,
known as the Gromov-Hausdorff distance, is defined as follows: given two
nonempty compact spaces `X` and `Y`, their distance is the minimum Hausdorff distance
between all possible isometric embeddings of `X` and `Y` in all metric spaces.
To define properly the Gromov-Hausdorff space, we consider the non-empty
compact subsets of `ℓ^∞(ℝ)` up to isometry, which is a well-defined type,
and define the distance as the infimum of the Hausdorff distance over all
embeddings in `ℓ^∞(ℝ)`. We prove that this coincides with the previous description,
as all separable metric spaces embed isometrically into `ℓ^∞(ℝ)`, through an
embedding called the Kuratowski embedding.
To prove that we have a distance, we should show that if spaces can be coupled
to be arbitrarily close, then they are isometric. More generally, the Gromov-Hausdorff
distance is realized, i.e., there is a coupling for which the Hausdorff distance
is exactly the Gromov-Hausdorff distance. This follows from a compactness
argument, essentially following from Arzela-Ascoli.

## Main results

We prove the most important properties of the Gromov-Hausdorff space: it is a polish space,
i.e., it is complete and second countable. We also prove the Gromov compactness criterion.

-/


noncomputable section

open Classical TopologicalSpace Ennreal

-- mathport name: exprℓ_infty_ℝ
local notation "ℓ_infty_ℝ" => lp (fun n : ℕ => ℝ) ∞

universe u v w

open Classical Set Function TopologicalSpace Filter Metric Quotient

open BoundedContinuousFunction Nat Int kuratowskiEmbedding

open Sum (inl inr)

attribute [local instance] metric_space_sum

namespace GromovHausdorff

section GHSpace

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "Equivalence relation identifying two nonempty compact sets which are isometric -/")]
      []
      [(Command.private "private")]
      []
      []
      [])
     (Command.def
      "def"
      (Command.declId `isometry_rel [])
      (Command.optDeclSig
       []
       [(Term.typeSpec
         ":"
         (Term.arrow
          (Term.app
           `NonemptyCompacts
           [(Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ "ℓ_infty_ℝ")])
          "→"
          (Term.arrow
           (Term.app
            `NonemptyCompacts
            [(Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ "ℓ_infty_ℝ")])
           "→"
           (Term.prop "Prop"))))])
      (Command.declValSimple
       ":="
       (Term.fun
        "fun"
        (Term.basicFun
         [`x `y]
         []
         "=>"
         (Term.app `Nonempty [(Topology.MetricSpace.Isometry.«term_≃ᵢ_» `x " ≃ᵢ " `y)])))
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`x `y]
        []
        "=>"
        (Term.app `Nonempty [(Topology.MetricSpace.Isometry.«term_≃ᵢ_» `x " ≃ᵢ " `y)])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Nonempty [(Topology.MetricSpace.Isometry.«term_≃ᵢ_» `x " ≃ᵢ " `y)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Topology.MetricSpace.Isometry.«term_≃ᵢ_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Topology.MetricSpace.Isometry.«term_≃ᵢ_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Topology.MetricSpace.Isometry.«term_≃ᵢ_» `x " ≃ᵢ " `y)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 26 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 25 >? 1024, (none, [anonymous]) <=? (some 25, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 25, (some 26, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Topology.MetricSpace.Isometry.«term_≃ᵢ_» `x " ≃ᵢ " `y)
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Nonempty
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.arrow
       (Term.app
        `NonemptyCompacts
        [(Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ "ℓ_infty_ℝ")])
       "→"
       (Term.arrow
        (Term.app
         `NonemptyCompacts
         [(Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ "ℓ_infty_ℝ")])
        "→"
        (Term.prop "Prop")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.arrow
       (Term.app
        `NonemptyCompacts
        [(Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ "ℓ_infty_ℝ")])
       "→"
       (Term.prop "Prop"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.prop "Prop")
[PrettyPrinter.parenthesize] ...precedences are 25 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
      (Term.app
       `NonemptyCompacts
       [(Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ "ℓ_infty_ℝ")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ "ℓ_infty_ℝ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ', expected 'Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ._@.Topology.MetricSpace.GromovHausdorff._hyg.5'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/-- Equivalence relation identifying two nonempty compact sets which are isometric -/ private
  def
    isometry_rel
    : NonemptyCompacts ℓ_infty_ℝ → NonemptyCompacts ℓ_infty_ℝ → Prop
    := fun x y => Nonempty x ≃ᵢ y
#align Gromov_Hausdorff.isometry_rel Gromov_Hausdorff.isometry_rel

/-- This is indeed an equivalence relation -/
private theorem is_equivalence_isometry_rel : Equivalence IsometryRel :=
  ⟨fun x => ⟨Isometric.refl _⟩, fun x y ⟨e⟩ => ⟨e.symm⟩, fun x y z ⟨e⟩ ⟨f⟩ => ⟨e.trans f⟩⟩
#align Gromov_Hausdorff.is_equivalence_isometry_rel Gromov_Hausdorff.is_equivalence_isometry_rel

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "setoid instance identifying two isometric nonempty compact subspaces of ℓ^∞(ℝ) -/")]
      []
      []
      []
      []
      [])
     (Command.instance
      (Term.attrKind [])
      "instance"
      []
      [(Command.declId `IsometryRel.setoid [])]
      (Command.declSig
       []
       (Term.typeSpec
        ":"
        (Term.app
         `Setoid
         [(Term.app
           `NonemptyCompacts
           [(Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ "ℓ_infty_ℝ")])])))
      (Command.declValSimple
       ":="
       (Term.app `Setoid.mk [`IsometryRel `is_equivalence_isometry_rel])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Setoid.mk [`IsometryRel `is_equivalence_isometry_rel])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `is_equivalence_isometry_rel
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `IsometryRel
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Setoid.mk
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app
       `Setoid
       [(Term.app
         `NonemptyCompacts
         [(Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ "ℓ_infty_ℝ")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `NonemptyCompacts
       [(Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ "ℓ_infty_ℝ")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ "ℓ_infty_ℝ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ', expected 'Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ._@.Topology.MetricSpace.GromovHausdorff._hyg.5'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/-- setoid instance identifying two isometric nonempty compact subspaces of ℓ^∞(ℝ) -/
  instance
    IsometryRel.setoid
    : Setoid NonemptyCompacts ℓ_infty_ℝ
    := Setoid.mk IsometryRel is_equivalence_isometry_rel
#align Gromov_Hausdorff.isometry_rel.setoid GromovHausdorff.IsometryRel.setoid

/-- The Gromov-Hausdorff space -/
def GHSpace : Type :=
  Quotient IsometryRel.setoid
#align Gromov_Hausdorff.GH_space GromovHausdorff.GHSpace

/-- Map any nonempty compact type to `GH_space` -/
def toGHSpace (X : Type u) [MetricSpace X] [CompactSpace X] [Nonempty X] : GHSpace :=
  ⟦NonemptyCompacts.kuratowskiEmbedding X⟧
#align Gromov_Hausdorff.to_GH_space GromovHausdorff.toGHSpace

instance : Inhabited GHSpace :=
  ⟨Quot.mk _ ⟨⟨{0}, is_compact_singleton⟩, singleton_nonempty _⟩⟩

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "A metric space representative of any abstract point in `GH_space` -/")]
      [(Term.attributes
        "@["
        [(Term.attrInstance
          (Term.attrKind [])
          (Std.Tactic.Lint.nolint "nolint" [`has_nonempty_instance]))]
        "]")]
      []
      []
      []
      [])
     (Command.def
      "def"
      (Command.declId `GHSpace.Rep [])
      (Command.optDeclSig
       [(Term.explicitBinder "(" [`p] [":" `GHSpace] [] ")")]
       [(Term.typeSpec ":" (Term.type "Type" []))])
      (Command.declValSimple
       ":="
       (Term.typeAscription
        "("
        (Term.app `Quotient.out [`p])
        ":"
        [(Term.app
          `NonemptyCompacts
          [(Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ "ℓ_infty_ℝ")])]
        ")")
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription
       "("
       (Term.app `Quotient.out [`p])
       ":"
       [(Term.app
         `NonemptyCompacts
         [(Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ "ℓ_infty_ℝ")])]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `NonemptyCompacts
       [(Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ "ℓ_infty_ℝ")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ "ℓ_infty_ℝ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ', expected 'Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ._@.Topology.MetricSpace.GromovHausdorff._hyg.5'
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
/-- A metric space representative of any abstract point in `GH_space` -/
    @[ nolint has_nonempty_instance ]
  def GHSpace.Rep ( p : GHSpace ) : Type := ( Quotient.out p : NonemptyCompacts ℓ_infty_ℝ )
#align Gromov_Hausdorff.GH_space.rep GromovHausdorff.GHSpace.Rep

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `eq_to_GH_space_iff [])
      (Command.declSig
       [(Term.implicitBinder "{" [`X] [":" (Term.type "Type" [`u])] "}")
        (Term.instBinder "[" [] (Term.app `MetricSpace [`X]) "]")
        (Term.instBinder "[" [] (Term.app `CompactSpace [`X]) "]")
        (Term.instBinder "[" [] (Term.app `Nonempty [`X]) "]")
        (Term.implicitBinder
         "{"
         [`p]
         [":"
          (Term.app
           `NonemptyCompacts
           [(Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ "ℓ_infty_ℝ")])]
         "}")]
       (Term.typeSpec
        ":"
        («term_↔_»
         («term_=_» (Quotient.Init.Data.Quot.«term⟦_⟧» "⟦" `p "⟧") "=" (Term.app `toGHSpace [`X]))
         "↔"
         («term∃_,_»
          "∃"
          (Lean.explicitBinders
           (Lean.unbracketedExplicitBinders
            [(Lean.binderIdent `Ψ)]
            [":"
             (Term.arrow `X "→" (Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ "ℓ_infty_ℝ"))]))
          ","
          («term_∧_» (Term.app `Isometry [`Ψ]) "∧" («term_=_» (Term.app `range [`Ψ]) "=" `p))))))
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
             [(Tactic.simpLemma [] [] `to_GH_space) "," (Tactic.simpLemma [] [] `Quotient.eq)]
             "]"]
            [])
           []
           (Tactic.refine'
            "refine'"
            (Term.anonymousCtor
             "⟨"
             [(Term.fun "fun" (Term.basicFun [`h] [] "=>" (Term.hole "_"))) "," (Term.hole "_")]
             "⟩"))
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Std.Tactic.rcases
              "rcases"
              [(Tactic.casesTarget [] (Term.app `Setoid.symm [`h]))]
              ["with"
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed
                 [(Std.Tactic.RCases.rcasesPat.tuple
                   "⟨"
                   [(Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `e)])
                     [])]
                   "⟩")])
                [])])
             []
             (Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                [`f []]
                []
                ":="
                (Term.app
                 (Term.proj
                  (Term.proj (Term.app `kuratowskiEmbedding.isometry [`X]) "." `isometricOnRange)
                  "."
                  `trans)
                 [`e]))))
             []
             (Mathlib.Tactic.«tacticUse_,,»
              "use"
              [(Term.fun "fun" (Term.basicFun [`x] [] "=>" (Term.app `f [`x])))
               ","
               (Term.app `isometry_subtype_coe.comp [`f.isometry])])
             []
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [] `range_comp)
                ","
                (Tactic.rwRule [] `f.range_eq_univ)
                ","
                (Tactic.rwRule [] `Set.image_univ)
                ","
                (Tactic.rwRule [] `Subtype.range_coe)]
               "]")
              [])
             []
             (Tactic.tacticRfl "rfl")])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Std.Tactic.rintro
              "rintro"
              [(Std.Tactic.RCases.rintroPat.one
                (Std.Tactic.RCases.rcasesPat.tuple
                 "⟨"
                 [(Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `Ψ)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed
                    [(Std.Tactic.RCases.rcasesPat.tuple
                      "⟨"
                      [(Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `isomΨ)])
                        [])
                       ","
                       (Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rangeΨ)])
                        [])]
                      "⟩")])
                   [])]
                 "⟩"))]
              [])
             []
             (Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                [`f []]
                []
                ":="
                (Term.proj
                 (Term.app
                  (Term.proj
                   (Term.proj
                    (Term.proj (Term.app `kuratowskiEmbedding.isometry [`X]) "." `isometricOnRange)
                    "."
                    `symm)
                   "."
                   `trans)
                  [`isomΨ.isometric_on_range])
                 "."
                 `symm))))
             []
             (Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                [`E []]
                [(Term.typeSpec
                  ":"
                  («term_=_»
                   (Topology.MetricSpace.Isometry.«term_≃ᵢ_»
                    (Term.app `range [`Ψ])
                    " ≃ᵢ "
                    (Term.app `NonemptyCompacts.kuratowskiEmbedding [`X]))
                   "="
                   (Topology.MetricSpace.Isometry.«term_≃ᵢ_»
                    `p
                    " ≃ᵢ "
                    (Term.app `range [(Term.app `kuratowskiEmbedding [`X])]))))]
                ":="
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(Tactic.dsimp
                     "dsimp"
                     []
                     []
                     ["only"]
                     ["[" [(Tactic.simpLemma [] [] `NonemptyCompacts.kuratowskiEmbedding)] "]"]
                     [])
                    []
                    (Tactic.«tactic_<;>_»
                     (Tactic.rwSeq
                      "rw"
                      []
                      (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `rangeΨ)] "]")
                      [])
                     "<;>"
                     (Tactic.tacticRfl "rfl"))]))))))
             []
             (Tactic.exact "exact" (Term.anonymousCtor "⟨" [(Term.app `cast [`E `f])] "⟩"))])])))
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
            [(Tactic.simpLemma [] [] `to_GH_space) "," (Tactic.simpLemma [] [] `Quotient.eq)]
            "]"]
           [])
          []
          (Tactic.refine'
           "refine'"
           (Term.anonymousCtor
            "⟨"
            [(Term.fun "fun" (Term.basicFun [`h] [] "=>" (Term.hole "_"))) "," (Term.hole "_")]
            "⟩"))
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Std.Tactic.rcases
             "rcases"
             [(Tactic.casesTarget [] (Term.app `Setoid.symm [`h]))]
             ["with"
              (Std.Tactic.RCases.rcasesPatLo
               (Std.Tactic.RCases.rcasesPatMed
                [(Std.Tactic.RCases.rcasesPat.tuple
                  "⟨"
                  [(Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `e)])
                    [])]
                  "⟩")])
               [])])
            []
            (Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               [`f []]
               []
               ":="
               (Term.app
                (Term.proj
                 (Term.proj (Term.app `kuratowskiEmbedding.isometry [`X]) "." `isometricOnRange)
                 "."
                 `trans)
                [`e]))))
            []
            (Mathlib.Tactic.«tacticUse_,,»
             "use"
             [(Term.fun "fun" (Term.basicFun [`x] [] "=>" (Term.app `f [`x])))
              ","
              (Term.app `isometry_subtype_coe.comp [`f.isometry])])
            []
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] `range_comp)
               ","
               (Tactic.rwRule [] `f.range_eq_univ)
               ","
               (Tactic.rwRule [] `Set.image_univ)
               ","
               (Tactic.rwRule [] `Subtype.range_coe)]
              "]")
             [])
            []
            (Tactic.tacticRfl "rfl")])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Std.Tactic.rintro
             "rintro"
             [(Std.Tactic.RCases.rintroPat.one
               (Std.Tactic.RCases.rcasesPat.tuple
                "⟨"
                [(Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `Ψ)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed
                   [(Std.Tactic.RCases.rcasesPat.tuple
                     "⟨"
                     [(Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `isomΨ)])
                       [])
                      ","
                      (Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rangeΨ)])
                       [])]
                     "⟩")])
                  [])]
                "⟩"))]
             [])
            []
            (Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               [`f []]
               []
               ":="
               (Term.proj
                (Term.app
                 (Term.proj
                  (Term.proj
                   (Term.proj (Term.app `kuratowskiEmbedding.isometry [`X]) "." `isometricOnRange)
                   "."
                   `symm)
                  "."
                  `trans)
                 [`isomΨ.isometric_on_range])
                "."
                `symm))))
            []
            (Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               [`E []]
               [(Term.typeSpec
                 ":"
                 («term_=_»
                  (Topology.MetricSpace.Isometry.«term_≃ᵢ_»
                   (Term.app `range [`Ψ])
                   " ≃ᵢ "
                   (Term.app `NonemptyCompacts.kuratowskiEmbedding [`X]))
                  "="
                  (Topology.MetricSpace.Isometry.«term_≃ᵢ_»
                   `p
                   " ≃ᵢ "
                   (Term.app `range [(Term.app `kuratowskiEmbedding [`X])]))))]
               ":="
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(Tactic.dsimp
                    "dsimp"
                    []
                    []
                    ["only"]
                    ["[" [(Tactic.simpLemma [] [] `NonemptyCompacts.kuratowskiEmbedding)] "]"]
                    [])
                   []
                   (Tactic.«tactic_<;>_»
                    (Tactic.rwSeq
                     "rw"
                     []
                     (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `rangeΨ)] "]")
                     [])
                    "<;>"
                    (Tactic.tacticRfl "rfl"))]))))))
            []
            (Tactic.exact "exact" (Term.anonymousCtor "⟨" [(Term.app `cast [`E `f])] "⟩"))])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Std.Tactic.rintro
         "rintro"
         [(Std.Tactic.RCases.rintroPat.one
           (Std.Tactic.RCases.rcasesPat.tuple
            "⟨"
            [(Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `Ψ)])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed
               [(Std.Tactic.RCases.rcasesPat.tuple
                 "⟨"
                 [(Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `isomΨ)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rangeΨ)])
                   [])]
                 "⟩")])
              [])]
            "⟩"))]
         [])
        []
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`f []]
           []
           ":="
           (Term.proj
            (Term.app
             (Term.proj
              (Term.proj
               (Term.proj (Term.app `kuratowskiEmbedding.isometry [`X]) "." `isometricOnRange)
               "."
               `symm)
              "."
              `trans)
             [`isomΨ.isometric_on_range])
            "."
            `symm))))
        []
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`E []]
           [(Term.typeSpec
             ":"
             («term_=_»
              (Topology.MetricSpace.Isometry.«term_≃ᵢ_»
               (Term.app `range [`Ψ])
               " ≃ᵢ "
               (Term.app `NonemptyCompacts.kuratowskiEmbedding [`X]))
              "="
              (Topology.MetricSpace.Isometry.«term_≃ᵢ_»
               `p
               " ≃ᵢ "
               (Term.app `range [(Term.app `kuratowskiEmbedding [`X])]))))]
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.dsimp
                "dsimp"
                []
                []
                ["only"]
                ["[" [(Tactic.simpLemma [] [] `NonemptyCompacts.kuratowskiEmbedding)] "]"]
                [])
               []
               (Tactic.«tactic_<;>_»
                (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `rangeΨ)] "]") [])
                "<;>"
                (Tactic.tacticRfl "rfl"))]))))))
        []
        (Tactic.exact "exact" (Term.anonymousCtor "⟨" [(Term.app `cast [`E `f])] "⟩"))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" (Term.anonymousCtor "⟨" [(Term.app `cast [`E `f])] "⟩"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [(Term.app `cast [`E `f])] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `cast [`E `f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `E
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `cast
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`E []]
         [(Term.typeSpec
           ":"
           («term_=_»
            (Topology.MetricSpace.Isometry.«term_≃ᵢ_»
             (Term.app `range [`Ψ])
             " ≃ᵢ "
             (Term.app `NonemptyCompacts.kuratowskiEmbedding [`X]))
            "="
            (Topology.MetricSpace.Isometry.«term_≃ᵢ_»
             `p
             " ≃ᵢ "
             (Term.app `range [(Term.app `kuratowskiEmbedding [`X])]))))]
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.dsimp
              "dsimp"
              []
              []
              ["only"]
              ["[" [(Tactic.simpLemma [] [] `NonemptyCompacts.kuratowskiEmbedding)] "]"]
              [])
             []
             (Tactic.«tactic_<;>_»
              (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `rangeΨ)] "]") [])
              "<;>"
              (Tactic.tacticRfl "rfl"))]))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.dsimp
           "dsimp"
           []
           []
           ["only"]
           ["[" [(Tactic.simpLemma [] [] `NonemptyCompacts.kuratowskiEmbedding)] "]"]
           [])
          []
          (Tactic.«tactic_<;>_»
           (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `rangeΨ)] "]") [])
           "<;>"
           (Tactic.tacticRfl "rfl"))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.«tactic_<;>_»
       (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `rangeΨ)] "]") [])
       "<;>"
       (Tactic.tacticRfl "rfl"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticRfl "rfl")
[PrettyPrinter.parenthesize] ...precedences are 2 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
      (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `rangeΨ)] "]") [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rangeΨ
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.dsimp
       "dsimp"
       []
       []
       ["only"]
       ["[" [(Tactic.simpLemma [] [] `NonemptyCompacts.kuratowskiEmbedding)] "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `NonemptyCompacts.kuratowskiEmbedding
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Topology.MetricSpace.Isometry.«term_≃ᵢ_»
        (Term.app `range [`Ψ])
        " ≃ᵢ "
        (Term.app `NonemptyCompacts.kuratowskiEmbedding [`X]))
       "="
       (Topology.MetricSpace.Isometry.«term_≃ᵢ_»
        `p
        " ≃ᵢ "
        (Term.app `range [(Term.app `kuratowskiEmbedding [`X])])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Topology.MetricSpace.Isometry.«term_≃ᵢ_»
       `p
       " ≃ᵢ "
       (Term.app `range [(Term.app `kuratowskiEmbedding [`X])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `range [(Term.app `kuratowskiEmbedding [`X])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `kuratowskiEmbedding [`X])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `X
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `kuratowskiEmbedding
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `kuratowskiEmbedding [`X])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `range
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 26 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 25 >? 1024, (none, [anonymous]) <=? (some 25, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 25, (some 26, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Topology.MetricSpace.Isometry.«term_≃ᵢ_»
      `p
      " ≃ᵢ "
      (Term.app `range [(Term.paren "(" (Term.app `kuratowskiEmbedding [`X]) ")")]))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Topology.MetricSpace.Isometry.«term_≃ᵢ_»
       (Term.app `range [`Ψ])
       " ≃ᵢ "
       (Term.app `NonemptyCompacts.kuratowskiEmbedding [`X]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `NonemptyCompacts.kuratowskiEmbedding [`X])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `X
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `NonemptyCompacts.kuratowskiEmbedding
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 26 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
      (Term.app `range [`Ψ])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Ψ
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `range
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 25 >? 1022, (some 1023, term) <=? (some 25, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 25, (some 26, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Topology.MetricSpace.Isometry.«term_≃ᵢ_»
      (Term.app `range [`Ψ])
      " ≃ᵢ "
      (Term.app `NonemptyCompacts.kuratowskiEmbedding [`X]))
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`f []]
         []
         ":="
         (Term.proj
          (Term.app
           (Term.proj
            (Term.proj
             (Term.proj (Term.app `kuratowskiEmbedding.isometry [`X]) "." `isometricOnRange)
             "."
             `symm)
            "."
            `trans)
           [`isomΨ.isometric_on_range])
          "."
          `symm))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj
       (Term.app
        (Term.proj
         (Term.proj
          (Term.proj (Term.app `kuratowskiEmbedding.isometry [`X]) "." `isometricOnRange)
          "."
          `symm)
         "."
         `trans)
        [`isomΨ.isometric_on_range])
       "."
       `symm)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       (Term.proj
        (Term.proj
         (Term.proj (Term.app `kuratowskiEmbedding.isometry [`X]) "." `isometricOnRange)
         "."
         `symm)
        "."
        `trans)
       [`isomΨ.isometric_on_range])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `isomΨ.isometric_on_range
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (Term.proj
        (Term.proj (Term.app `kuratowskiEmbedding.isometry [`X]) "." `isometricOnRange)
        "."
        `symm)
       "."
       `trans)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj
       (Term.proj (Term.app `kuratowskiEmbedding.isometry [`X]) "." `isometricOnRange)
       "."
       `symm)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj (Term.app `kuratowskiEmbedding.isometry [`X]) "." `isometricOnRange)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `kuratowskiEmbedding.isometry [`X])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `X
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `kuratowskiEmbedding.isometry
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `kuratowskiEmbedding.isometry [`X])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      (Term.proj
       (Term.proj
        (Term.proj
         (Term.paren "(" (Term.app `kuratowskiEmbedding.isometry [`X]) ")")
         "."
         `isometricOnRange)
        "."
        `symm)
       "."
       `trans)
      [`isomΨ.isometric_on_range])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.rintro
       "rintro"
       [(Std.Tactic.RCases.rintroPat.one
         (Std.Tactic.RCases.rcasesPat.tuple
          "⟨"
          [(Std.Tactic.RCases.rcasesPatLo
            (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `Ψ)])
            [])
           ","
           (Std.Tactic.RCases.rcasesPatLo
            (Std.Tactic.RCases.rcasesPatMed
             [(Std.Tactic.RCases.rcasesPat.tuple
               "⟨"
               [(Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `isomΨ)])
                 [])
                ","
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rangeΨ)])
                 [])]
               "⟩")])
            [])]
          "⟩"))]
       [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Std.Tactic.rcases
         "rcases"
         [(Tactic.casesTarget [] (Term.app `Setoid.symm [`h]))]
         ["with"
          (Std.Tactic.RCases.rcasesPatLo
           (Std.Tactic.RCases.rcasesPatMed
            [(Std.Tactic.RCases.rcasesPat.tuple
              "⟨"
              [(Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `e)])
                [])]
              "⟩")])
           [])])
        []
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`f []]
           []
           ":="
           (Term.app
            (Term.proj
             (Term.proj (Term.app `kuratowskiEmbedding.isometry [`X]) "." `isometricOnRange)
             "."
             `trans)
            [`e]))))
        []
        (Mathlib.Tactic.«tacticUse_,,»
         "use"
         [(Term.fun "fun" (Term.basicFun [`x] [] "=>" (Term.app `f [`x])))
          ","
          (Term.app `isometry_subtype_coe.comp [`f.isometry])])
        []
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule [] `range_comp)
           ","
           (Tactic.rwRule [] `f.range_eq_univ)
           ","
           (Tactic.rwRule [] `Set.image_univ)
           ","
           (Tactic.rwRule [] `Subtype.range_coe)]
          "]")
         [])
        []
        (Tactic.tacticRfl "rfl")])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticRfl "rfl")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `range_comp)
         ","
         (Tactic.rwRule [] `f.range_eq_univ)
         ","
         (Tactic.rwRule [] `Set.image_univ)
         ","
         (Tactic.rwRule [] `Subtype.range_coe)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Subtype.range_coe
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Set.image_univ
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f.range_eq_univ
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `range_comp
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.«tacticUse_,,»
       "use"
       [(Term.fun "fun" (Term.basicFun [`x] [] "=>" (Term.app `f [`x])))
        ","
        (Term.app `isometry_subtype_coe.comp [`f.isometry])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `isometry_subtype_coe.comp [`f.isometry])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f.isometry
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `isometry_subtype_coe.comp
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun "fun" (Term.basicFun [`x] [] "=>" (Term.app `f [`x])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `f [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`f []]
         []
         ":="
         (Term.app
          (Term.proj
           (Term.proj (Term.app `kuratowskiEmbedding.isometry [`X]) "." `isometricOnRange)
           "."
           `trans)
          [`e]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (Term.proj (Term.app `kuratowskiEmbedding.isometry [`X]) "." `isometricOnRange)
        "."
        `trans)
       [`e])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `e
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (Term.proj (Term.app `kuratowskiEmbedding.isometry [`X]) "." `isometricOnRange)
       "."
       `trans)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj (Term.app `kuratowskiEmbedding.isometry [`X]) "." `isometricOnRange)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `kuratowskiEmbedding.isometry [`X])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `X
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `kuratowskiEmbedding.isometry
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `kuratowskiEmbedding.isometry [`X])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.rcases
       "rcases"
       [(Tactic.casesTarget [] (Term.app `Setoid.symm [`h]))]
       ["with"
        (Std.Tactic.RCases.rcasesPatLo
         (Std.Tactic.RCases.rcasesPatMed
          [(Std.Tactic.RCases.rcasesPat.tuple
            "⟨"
            [(Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `e)])
              [])]
            "⟩")])
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Setoid.symm [`h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Setoid.symm
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine'
       "refine'"
       (Term.anonymousCtor
        "⟨"
        [(Term.fun "fun" (Term.basicFun [`h] [] "=>" (Term.hole "_"))) "," (Term.hole "_")]
        "⟩"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.fun "fun" (Term.basicFun [`h] [] "=>" (Term.hole "_"))) "," (Term.hole "_")]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun "fun" (Term.basicFun [`h] [] "=>" (Term.hole "_")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["[" [(Tactic.simpLemma [] [] `to_GH_space) "," (Tactic.simpLemma [] [] `Quotient.eq)] "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Quotient.eq
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `to_GH_space
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_↔_»
       («term_=_» (Quotient.Init.Data.Quot.«term⟦_⟧» "⟦" `p "⟧") "=" (Term.app `toGHSpace [`X]))
       "↔"
       («term∃_,_»
        "∃"
        (Lean.explicitBinders
         (Lean.unbracketedExplicitBinders
          [(Lean.binderIdent `Ψ)]
          [":"
           (Term.arrow `X "→" (Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ "ℓ_infty_ℝ"))]))
        ","
        («term_∧_» (Term.app `Isometry [`Ψ]) "∧" («term_=_» (Term.app `range [`Ψ]) "=" `p))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term∃_,_»
       "∃"
       (Lean.explicitBinders
        (Lean.unbracketedExplicitBinders
         [(Lean.binderIdent `Ψ)]
         [":"
          (Term.arrow `X "→" (Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ "ℓ_infty_ℝ"))]))
       ","
       («term_∧_» (Term.app `Isometry [`Ψ]) "∧" («term_=_» (Term.app `range [`Ψ]) "=" `p)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∧_» (Term.app `Isometry [`Ψ]) "∧" («term_=_» (Term.app `range [`Ψ]) "=" `p))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_» (Term.app `range [`Ψ]) "=" `p)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app `range [`Ψ])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Ψ
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `range
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 35 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 35, term))
      (Term.app `Isometry [`Ψ])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Ψ
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Isometry
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 36 >? 1022, (some 1023, term) <=? (some 35, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 35, (some 35, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'Lean.bracketedExplicitBinders'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.arrow `X "→" (Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ "ℓ_infty_ℝ"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ "ℓ_infty_ℝ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ', expected 'Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ._@.Topology.MetricSpace.GromovHausdorff._hyg.5'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  eq_to_GH_space_iff
  { X : Type u }
      [ MetricSpace X ]
      [ CompactSpace X ]
      [ Nonempty X ]
      { p : NonemptyCompacts ℓ_infty_ℝ }
    : ⟦ p ⟧ = toGHSpace X ↔ ∃ Ψ : X → ℓ_infty_ℝ , Isometry Ψ ∧ range Ψ = p
  :=
    by
      simp only [ to_GH_space , Quotient.eq ]
        refine' ⟨ fun h => _ , _ ⟩
        ·
          rcases Setoid.symm h with ⟨ e ⟩
            have f := kuratowskiEmbedding.isometry X . isometricOnRange . trans e
            use fun x => f x , isometry_subtype_coe.comp f.isometry
            rw [ range_comp , f.range_eq_univ , Set.image_univ , Subtype.range_coe ]
            rfl
        ·
          rintro ⟨ Ψ , ⟨ isomΨ , rangeΨ ⟩ ⟩
            have
              f
                :=
                kuratowskiEmbedding.isometry X . isometricOnRange . symm . trans
                    isomΨ.isometric_on_range
                  .
                  symm
            have
              E
                :
                  range Ψ ≃ᵢ NonemptyCompacts.kuratowskiEmbedding X
                    =
                    p ≃ᵢ range kuratowskiEmbedding X
                :=
                by dsimp only [ NonemptyCompacts.kuratowskiEmbedding ] rw [ rangeΨ ] <;> rfl
            exact ⟨ cast E f ⟩
#align Gromov_Hausdorff.eq_to_GH_space_iff GromovHausdorff.eq_to_GH_space_iff

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `eq_to_GH_space [])
      (Command.declSig
       [(Term.implicitBinder
         "{"
         [`p]
         [":"
          (Term.app
           `NonemptyCompacts
           [(Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ "ℓ_infty_ℝ")])]
         "}")]
       (Term.typeSpec
        ":"
        («term_=_» (Quotient.Init.Data.Quot.«term⟦_⟧» "⟦" `p "⟧") "=" (Term.app `toGHSpace [`p]))))
      (Command.declValSimple
       ":="
       (Term.app
        (Term.proj `eq_to_GH_space_iff "." (fieldIdx "2"))
        [(Term.anonymousCtor
          "⟨"
          [(Term.fun "fun" (Term.basicFun [`x] [] "=>" `x))
           ","
           `isometry_subtype_coe
           ","
           `Subtype.range_coe]
          "⟩")])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj `eq_to_GH_space_iff "." (fieldIdx "2"))
       [(Term.anonymousCtor
         "⟨"
         [(Term.fun "fun" (Term.basicFun [`x] [] "=>" `x))
          ","
          `isometry_subtype_coe
          ","
          `Subtype.range_coe]
         "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.fun "fun" (Term.basicFun [`x] [] "=>" `x))
        ","
        `isometry_subtype_coe
        ","
        `Subtype.range_coe]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Subtype.range_coe
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `isometry_subtype_coe
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun "fun" (Term.basicFun [`x] [] "=>" `x))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `eq_to_GH_space_iff "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `eq_to_GH_space_iff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_» (Quotient.Init.Data.Quot.«term⟦_⟧» "⟦" `p "⟧") "=" (Term.app `toGHSpace [`p]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `toGHSpace [`p])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `toGHSpace
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Quotient.Init.Data.Quot.«term⟦_⟧» "⟦" `p "⟧")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1023, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.implicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.implicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.implicitBinder', expected 'Lean.Parser.Term.explicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.implicitBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `NonemptyCompacts
       [(Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ "ℓ_infty_ℝ")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ "ℓ_infty_ℝ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ', expected 'Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ._@.Topology.MetricSpace.GromovHausdorff._hyg.5'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.implicitBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  eq_to_GH_space
  { p : NonemptyCompacts ℓ_infty_ℝ } : ⟦ p ⟧ = toGHSpace p
  := eq_to_GH_space_iff . 2 ⟨ fun x => x , isometry_subtype_coe , Subtype.range_coe ⟩
#align Gromov_Hausdorff.eq_to_GH_space GromovHausdorff.eq_to_GH_space

section

attribute [local reducible] GH_space.rep

instance repGHSpaceMetricSpace {p : GHSpace} : MetricSpace p.rep := by infer_instance
#align Gromov_Hausdorff.rep_GH_space_metric_space GromovHausdorff.repGHSpaceMetricSpace

instance rep_GH_space_compact_space {p : GHSpace} : CompactSpace p.rep := by infer_instance
#align Gromov_Hausdorff.rep_GH_space_compact_space GromovHausdorff.rep_GH_space_compact_space

instance rep_GH_space_nonempty {p : GHSpace} : Nonempty p.rep := by infer_instance
#align Gromov_Hausdorff.rep_GH_space_nonempty GromovHausdorff.rep_GH_space_nonempty

end

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `GHSpace.to_GH_space_rep [])
      (Command.declSig
       [(Term.explicitBinder "(" [`p] [":" `GHSpace] [] ")")]
       (Term.typeSpec ":" («term_=_» (Term.app `toGHSpace [(Term.proj `p "." `rep)]) "=" `p)))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.change
            "change"
            («term_=_»
             (Term.app
              `to_GH_space
              [(Term.typeAscription
                "("
                (Term.app `Quot.out [`p])
                ":"
                [(Term.app
                  `nonempty_compacts
                  [(Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ "ℓ_infty_ℝ")])]
                ")")])
             "="
             `p)
            [])
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `eq_to_GH_space)]
             "]")
            [])
           []
           (Tactic.exact "exact" (Term.app `Quot.out_eq [`p]))])))
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
         [(Tactic.change
           "change"
           («term_=_»
            (Term.app
             `to_GH_space
             [(Term.typeAscription
               "("
               (Term.app `Quot.out [`p])
               ":"
               [(Term.app
                 `nonempty_compacts
                 [(Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ "ℓ_infty_ℝ")])]
               ")")])
            "="
            `p)
           [])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `eq_to_GH_space)]
            "]")
           [])
          []
          (Tactic.exact "exact" (Term.app `Quot.out_eq [`p]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" (Term.app `Quot.out_eq [`p]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Quot.out_eq [`p])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Quot.out_eq
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
        [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `eq_to_GH_space)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `eq_to_GH_space
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.change
       "change"
       («term_=_»
        (Term.app
         `to_GH_space
         [(Term.typeAscription
           "("
           (Term.app `Quot.out [`p])
           ":"
           [(Term.app
             `nonempty_compacts
             [(Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ "ℓ_infty_ℝ")])]
           ")")])
        "="
        `p)
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Term.app
        `to_GH_space
        [(Term.typeAscription
          "("
          (Term.app `Quot.out [`p])
          ":"
          [(Term.app
            `nonempty_compacts
            [(Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ "ℓ_infty_ℝ")])]
          ")")])
       "="
       `p)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app
       `to_GH_space
       [(Term.typeAscription
         "("
         (Term.app `Quot.out [`p])
         ":"
         [(Term.app
           `nonempty_compacts
           [(Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ "ℓ_infty_ℝ")])]
         ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription
       "("
       (Term.app `Quot.out [`p])
       ":"
       [(Term.app
         `nonempty_compacts
         [(Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ "ℓ_infty_ℝ")])]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `nonempty_compacts
       [(Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ "ℓ_infty_ℝ")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ "ℓ_infty_ℝ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ', expected 'Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ._@.Topology.MetricSpace.GromovHausdorff._hyg.5'
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
  GHSpace.to_GH_space_rep
  ( p : GHSpace ) : toGHSpace p . rep = p
  :=
    by
      change to_GH_space ( Quot.out p : nonempty_compacts ℓ_infty_ℝ ) = p
        rw [ ← eq_to_GH_space ]
        exact Quot.out_eq p
#align Gromov_Hausdorff.GH_space.to_GH_space_rep GromovHausdorff.GHSpace.to_GH_space_rep

/-- Two nonempty compact spaces have the same image in `GH_space` if and only if they are
isometric. -/
theorem to_GH_space_eq_to_GH_space_iff_isometric {X : Type u} [MetricSpace X] [CompactSpace X]
    [Nonempty X] {Y : Type v} [MetricSpace Y] [CompactSpace Y] [Nonempty Y] :
    toGHSpace X = toGHSpace Y ↔ Nonempty (X ≃ᵢ Y) :=
  ⟨by
    simp only [to_GH_space, Quotient.eq]
    rintro ⟨e⟩
    have I :
      (NonemptyCompacts.kuratowskiEmbedding X ≃ᵢ NonemptyCompacts.kuratowskiEmbedding Y) =
        (range (kuratowskiEmbedding X) ≃ᵢ range (kuratowskiEmbedding Y)) :=
      by
      dsimp only [NonemptyCompacts.kuratowskiEmbedding]
      rfl
    have f := (kuratowskiEmbedding.isometry X).isometricOnRange
    have g := (kuratowskiEmbedding.isometry Y).isometricOnRange.symm
    exact ⟨f.trans <| (cast I e).trans g⟩, by
    rintro ⟨e⟩
    simp only [to_GH_space, Quotient.eq]
    have f := (kuratowskiEmbedding.isometry X).isometricOnRange.symm
    have g := (kuratowskiEmbedding.isometry Y).isometricOnRange
    have I :
      (range (kuratowskiEmbedding X) ≃ᵢ range (kuratowskiEmbedding Y)) =
        (NonemptyCompacts.kuratowskiEmbedding X ≃ᵢ NonemptyCompacts.kuratowskiEmbedding Y) :=
      by
      dsimp only [NonemptyCompacts.kuratowskiEmbedding]
      rfl
    exact ⟨cast I ((f.trans e).trans g)⟩⟩
#align
  Gromov_Hausdorff.to_GH_space_eq_to_GH_space_iff_isometric GromovHausdorff.to_GH_space_eq_to_GH_space_iff_isometric

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "Distance on `GH_space`: the distance between two nonempty compact spaces is the infimum\nHausdorff distance between isometric copies of the two spaces in a metric space. For the definition,\nwe only consider embeddings in `ℓ^∞(ℝ)`, but we will prove below that it works for all spaces. -/")]
      []
      []
      []
      []
      [])
     (Command.instance
      (Term.attrKind [])
      "instance"
      []
      []
      (Command.declSig [] (Term.typeSpec ":" (Term.app `HasDist [`GHSpace])))
      (Command.whereStructInst
       "where"
       [(Command.whereStructField
         (Term.letDecl
          (Term.letIdDecl
           `dist
           [`x `y]
           []
           ":="
           («term_<|_»
            `Inf
            "<|"
            (Set.Data.Set.Image.term_''_
             (Term.fun
              "fun"
              (Term.basicFun
               [`p]
               [(Term.typeSpec
                 ":"
                 («term_×_»
                  (Term.app
                   `NonemptyCompacts
                   [(Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ "ℓ_infty_ℝ")])
                  "×"
                  (Term.app
                   `NonemptyCompacts
                   [(Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ "ℓ_infty_ℝ")])))]
               "=>"
               (Term.app
                `hausdorffDist
                [(Term.typeAscription
                  "("
                  (Term.proj `p "." (fieldIdx "1"))
                  ":"
                  [(Term.app
                    `Set
                    [(Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ "ℓ_infty_ℝ")])]
                  ")")
                 (Term.proj `p "." (fieldIdx "2"))])))
             " '' "
             (LowerSet.Order.UpperLower.lower_set.prod
              (Set.«term{_|_}»
               "{"
               (Std.ExtendedBinder.extBinder (Lean.binderIdent `a) [])
               "|"
               («term_=_» (Quotient.Init.Data.Quot.«term⟦_⟧» "⟦" `a "⟧") "=" `x)
               "}")
              " ×ˢ "
              (Set.«term{_|_}»
               "{"
               (Std.ExtendedBinder.extBinder (Lean.binderIdent `b) [])
               "|"
               («term_=_» (Quotient.Init.Data.Quot.«term⟦_⟧» "⟦" `b "⟧") "=" `y)
               "}")))))))]
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
      («term_<|_»
       `Inf
       "<|"
       (Set.Data.Set.Image.term_''_
        (Term.fun
         "fun"
         (Term.basicFun
          [`p]
          [(Term.typeSpec
            ":"
            («term_×_»
             (Term.app
              `NonemptyCompacts
              [(Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ "ℓ_infty_ℝ")])
             "×"
             (Term.app
              `NonemptyCompacts
              [(Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ "ℓ_infty_ℝ")])))]
          "=>"
          (Term.app
           `hausdorffDist
           [(Term.typeAscription
             "("
             (Term.proj `p "." (fieldIdx "1"))
             ":"
             [(Term.app `Set [(Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ "ℓ_infty_ℝ")])]
             ")")
            (Term.proj `p "." (fieldIdx "2"))])))
        " '' "
        (LowerSet.Order.UpperLower.lower_set.prod
         (Set.«term{_|_}»
          "{"
          (Std.ExtendedBinder.extBinder (Lean.binderIdent `a) [])
          "|"
          («term_=_» (Quotient.Init.Data.Quot.«term⟦_⟧» "⟦" `a "⟧") "=" `x)
          "}")
         " ×ˢ "
         (Set.«term{_|_}»
          "{"
          (Std.ExtendedBinder.extBinder (Lean.binderIdent `b) [])
          "|"
          («term_=_» (Quotient.Init.Data.Quot.«term⟦_⟧» "⟦" `b "⟧") "=" `y)
          "}"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Set.Data.Set.Image.term_''_
       (Term.fun
        "fun"
        (Term.basicFun
         [`p]
         [(Term.typeSpec
           ":"
           («term_×_»
            (Term.app
             `NonemptyCompacts
             [(Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ "ℓ_infty_ℝ")])
            "×"
            (Term.app
             `NonemptyCompacts
             [(Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ "ℓ_infty_ℝ")])))]
         "=>"
         (Term.app
          `hausdorffDist
          [(Term.typeAscription
            "("
            (Term.proj `p "." (fieldIdx "1"))
            ":"
            [(Term.app `Set [(Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ "ℓ_infty_ℝ")])]
            ")")
           (Term.proj `p "." (fieldIdx "2"))])))
       " '' "
       (LowerSet.Order.UpperLower.lower_set.prod
        (Set.«term{_|_}»
         "{"
         (Std.ExtendedBinder.extBinder (Lean.binderIdent `a) [])
         "|"
         («term_=_» (Quotient.Init.Data.Quot.«term⟦_⟧» "⟦" `a "⟧") "=" `x)
         "}")
        " ×ˢ "
        (Set.«term{_|_}»
         "{"
         (Std.ExtendedBinder.extBinder (Lean.binderIdent `b) [])
         "|"
         («term_=_» (Quotient.Init.Data.Quot.«term⟦_⟧» "⟦" `b "⟧") "=" `y)
         "}")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (LowerSet.Order.UpperLower.lower_set.prod
       (Set.«term{_|_}»
        "{"
        (Std.ExtendedBinder.extBinder (Lean.binderIdent `a) [])
        "|"
        («term_=_» (Quotient.Init.Data.Quot.«term⟦_⟧» "⟦" `a "⟧") "=" `x)
        "}")
       " ×ˢ "
       (Set.«term{_|_}»
        "{"
        (Std.ExtendedBinder.extBinder (Lean.binderIdent `b) [])
        "|"
        («term_=_» (Quotient.Init.Data.Quot.«term⟦_⟧» "⟦" `b "⟧") "=" `y)
        "}"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Set.«term{_|_}»
       "{"
       (Std.ExtendedBinder.extBinder (Lean.binderIdent `b) [])
       "|"
       («term_=_» (Quotient.Init.Data.Quot.«term⟦_⟧» "⟦" `b "⟧") "=" `y)
       "}")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_» (Quotient.Init.Data.Quot.«term⟦_⟧» "⟦" `b "⟧") "=" `y)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Quotient.Init.Data.Quot.«term⟦_⟧» "⟦" `b "⟧")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `b
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1023, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 82 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 82, term))
      (Set.«term{_|_}»
       "{"
       (Std.ExtendedBinder.extBinder (Lean.binderIdent `a) [])
       "|"
       («term_=_» (Quotient.Init.Data.Quot.«term⟦_⟧» "⟦" `a "⟧") "=" `x)
       "}")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_» (Quotient.Init.Data.Quot.«term⟦_⟧» "⟦" `a "⟧") "=" `x)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Quotient.Init.Data.Quot.«term⟦_⟧» "⟦" `a "⟧")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1023, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 83 >? 1024, (none, [anonymous]) <=? (some 82, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 82, (some 82, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Term.fun
       "fun"
       (Term.basicFun
        [`p]
        [(Term.typeSpec
          ":"
          («term_×_»
           (Term.app
            `NonemptyCompacts
            [(Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ "ℓ_infty_ℝ")])
           "×"
           (Term.app
            `NonemptyCompacts
            [(Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ "ℓ_infty_ℝ")])))]
        "=>"
        (Term.app
         `hausdorffDist
         [(Term.typeAscription
           "("
           (Term.proj `p "." (fieldIdx "1"))
           ":"
           [(Term.app `Set [(Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ "ℓ_infty_ℝ")])]
           ")")
          (Term.proj `p "." (fieldIdx "2"))])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `hausdorffDist
       [(Term.typeAscription
         "("
         (Term.proj `p "." (fieldIdx "1"))
         ":"
         [(Term.app `Set [(Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ "ℓ_infty_ℝ")])]
         ")")
        (Term.proj `p "." (fieldIdx "2"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `p "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.typeAscription
       "("
       (Term.proj `p "." (fieldIdx "1"))
       ":"
       [(Term.app `Set [(Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ "ℓ_infty_ℝ")])]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Set [(Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ "ℓ_infty_ℝ")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ "ℓ_infty_ℝ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ', expected 'Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ._@.Topology.MetricSpace.GromovHausdorff._hyg.5'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letIdDecl', expected 'Lean.Parser.Term.letPatDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letIdDecl', expected 'Lean.Parser.Term.letEqnsDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    Distance on `GH_space`: the distance between two nonempty compact spaces is the infimum
    Hausdorff distance between isometric copies of the two spaces in a metric space. For the definition,
    we only consider embeddings in `ℓ^∞(ℝ)`, but we will prove below that it works for all spaces. -/
  instance
    : HasDist GHSpace
    where
      dist
        x y
        :=
        Inf
          <|
          fun
              p
                : NonemptyCompacts ℓ_infty_ℝ × NonemptyCompacts ℓ_infty_ℝ
                =>
                hausdorffDist ( p . 1 : Set ℓ_infty_ℝ ) p . 2
            ''
            { a | ⟦ a ⟧ = x } ×ˢ { b | ⟦ b ⟧ = y }

/-- The Gromov-Hausdorff distance between two nonempty compact metric spaces, equal by definition to
the distance of the equivalence classes of these spaces in the Gromov-Hausdorff space. -/
def gHDist (X : Type u) (Y : Type v) [MetricSpace X] [Nonempty X] [CompactSpace X] [MetricSpace Y]
    [Nonempty Y] [CompactSpace Y] : ℝ :=
  dist (toGHSpace X) (toGHSpace Y)
#align Gromov_Hausdorff.GH_dist GromovHausdorff.gHDist

theorem dist_GH_dist (p q : GHSpace) : dist p q = gHDist p.rep q.rep := by
  rw [GH_dist, p.to_GH_space_rep, q.to_GH_space_rep]
#align Gromov_Hausdorff.dist_GH_dist GromovHausdorff.dist_GH_dist

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "The Gromov-Hausdorff distance between two spaces is bounded by the Hausdorff distance\nof isometric copies of the spaces, in any metric space. -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `GH_dist_le_Hausdorff_dist [])
      (Command.declSig
       [(Term.implicitBinder "{" [`X] [":" (Term.type "Type" [`u])] "}")
        (Term.instBinder "[" [] (Term.app `MetricSpace [`X]) "]")
        (Term.instBinder "[" [] (Term.app `CompactSpace [`X]) "]")
        (Term.instBinder "[" [] (Term.app `Nonempty [`X]) "]")
        (Term.implicitBinder "{" [`Y] [":" (Term.type "Type" [`v])] "}")
        (Term.instBinder "[" [] (Term.app `MetricSpace [`Y]) "]")
        (Term.instBinder "[" [] (Term.app `CompactSpace [`Y]) "]")
        (Term.instBinder "[" [] (Term.app `Nonempty [`Y]) "]")
        (Term.implicitBinder "{" [`γ] [":" (Term.type "Type" [`w])] "}")
        (Term.instBinder "[" [] (Term.app `MetricSpace [`γ]) "]")
        (Term.implicitBinder "{" [`Φ] [":" (Term.arrow `X "→" `γ)] "}")
        (Term.implicitBinder "{" [`Ψ] [":" (Term.arrow `Y "→" `γ)] "}")
        (Term.explicitBinder "(" [`ha] [":" (Term.app `Isometry [`Φ])] [] ")")
        (Term.explicitBinder "(" [`hb] [":" (Term.app `Isometry [`Ψ])] [] ")")]
       (Term.typeSpec
        ":"
        («term_≤_»
         (Term.app `gHDist [`X `Y])
         "≤"
         (Term.app `hausdorffDist [(Term.app `range [`Φ]) (Term.app `range [`Ψ])]))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Std.Tactic.rcases
            "rcases"
            [(Tactic.casesTarget [] (Term.app `exists_mem_of_nonempty [`X]))]
            ["with"
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed
               [(Std.Tactic.RCases.rcasesPat.tuple
                 "⟨"
                 [(Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `xX)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.ignore "_")])
                   [])]
                 "⟩")])
              [])])
           []
           (Tactic.tacticLet_
            "let"
            (Term.letDecl
             (Term.letIdDecl
              `s
              []
              [(Term.typeSpec ":" (Term.app `Set [`γ]))]
              ":="
              («term_∪_» (Term.app `range [`Φ]) "∪" (Term.app `range [`Ψ])))))
           []
           (Tactic.tacticLet_
            "let"
            (Term.letDecl
             (Term.letIdDecl
              `Φ'
              []
              [(Term.typeSpec ":" (Term.arrow `X "→" (Term.app `Subtype [`s])))]
              ":="
              (Term.fun
               "fun"
               (Term.basicFun
                [`y]
                []
                "=>"
                (Term.anonymousCtor
                 "⟨"
                 [(Term.app `Φ [`y])
                  ","
                  (Term.app
                   `mem_union_left
                   [(Term.hole "_") (Term.app `mem_range_self [(Term.hole "_")])])]
                 "⟩"))))))
           []
           (Tactic.tacticLet_
            "let"
            (Term.letDecl
             (Term.letIdDecl
              `Ψ'
              []
              [(Term.typeSpec ":" (Term.arrow `Y "→" (Term.app `Subtype [`s])))]
              ":="
              (Term.fun
               "fun"
               (Term.basicFun
                [`y]
                []
                "=>"
                (Term.anonymousCtor
                 "⟨"
                 [(Term.app `Ψ [`y])
                  ","
                  (Term.app
                   `mem_union_right
                   [(Term.hole "_") (Term.app `mem_range_self [(Term.hole "_")])])]
                 "⟩"))))))
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`IΦ' []]
              [(Term.typeSpec ":" (Term.app `Isometry [`Φ']))]
              ":="
              (Term.fun "fun" (Term.basicFun [`x `y] [] "=>" (Term.app `ha [`x `y]))))))
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`IΨ' []]
              [(Term.typeSpec ":" (Term.app `Isometry [`Ψ']))]
              ":="
              (Term.fun "fun" (Term.basicFun [`x `y] [] "=>" (Term.app `hb [`x `y]))))))
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              []
              [(Term.typeSpec ":" (Term.app `IsCompact [`s]))]
              ":="
              (Term.app
               (Term.proj (Term.app `is_compact_range [`ha.continuous]) "." `union)
               [(Term.app `is_compact_range [`hb.continuous])]))))
           []
           (Std.Tactic.tacticLetI_
            "letI"
            (Term.haveDecl
             (Term.haveIdDecl
              []
              [(Term.typeSpec ":" (Term.app `MetricSpace [(Term.app `Subtype [`s])]))]
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented [(Tactic.tacticInfer_instance "infer_instance")]))))))
           []
           (Std.Tactic.tacticHaveI_
            "haveI"
            (Term.haveDecl
             (Term.haveIdDecl
              []
              [(Term.typeSpec ":" (Term.app `CompactSpace [(Term.app `Subtype [`s])]))]
              ":="
              (Term.anonymousCtor
               "⟨"
               [(Term.app
                 (Term.proj `is_compact_iff_is_compact_univ "." (fieldIdx "1"))
                 [(«term‹_›» "‹" (Term.app `IsCompact [`s]) "›")])]
               "⟩"))))
           []
           (Std.Tactic.tacticHaveI_
            "haveI"
            (Term.haveDecl
             (Term.haveIdDecl
              []
              [(Term.typeSpec ":" (Term.app `Nonempty [(Term.app `Subtype [`s])]))]
              ":="
              (Term.anonymousCtor "⟨" [(Term.app `Φ' [`xX])] "⟩"))))
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`ΦΦ' []]
              [(Term.typeSpec ":" («term_=_» `Φ "=" («term_∘_» `Subtype.val "∘" `Φ')))]
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(tacticFunext__ "funext" []) [] (Tactic.tacticRfl "rfl")]))))))
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`ΨΨ' []]
              [(Term.typeSpec ":" («term_=_» `Ψ "=" («term_∘_» `Subtype.val "∘" `Ψ')))]
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(tacticFunext__ "funext" []) [] (Tactic.tacticRfl "rfl")]))))))
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              []
              [(Term.typeSpec
                ":"
                («term_=_»
                 (Term.app `Hausdorff_dist [(Term.app `range [`Φ]) (Term.app `range [`Ψ])])
                 "="
                 (Term.app `Hausdorff_dist [(Term.app `range [`Φ']) (Term.app `range [`Ψ'])])))]
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
                    [(Tactic.rwRule [] `ΦΦ')
                     ","
                     (Tactic.rwRule [] `ΨΨ')
                     ","
                     (Tactic.rwRule [] `range_comp)
                     ","
                     (Tactic.rwRule [] `range_comp)]
                    "]")
                   [])
                  []
                  (Tactic.exact
                   "exact"
                   (Term.app `Hausdorff_dist_image [`isometry_subtype_coe]))]))))))
           []
           (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `this)] "]") [])
           []
           (Tactic.tacticLet_
            "let"
            (Term.letDecl
             (Term.letIdDecl
              `F
              []
              []
              ":="
              (Term.app `kuratowskiEmbedding [(Term.app `Subtype [`s])]))))
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              []
              [(Term.typeSpec
                ":"
                («term_=_»
                 (Term.app
                  `Hausdorff_dist
                  [(Set.Data.Set.Image.term_''_ `F " '' " (Term.app `range [`Φ']))
                   (Set.Data.Set.Image.term_''_ `F " '' " (Term.app `range [`Ψ']))])
                 "="
                 (Term.app `Hausdorff_dist [(Term.app `range [`Φ']) (Term.app `range [`Ψ'])])))]
              ":="
              (Term.app
               `Hausdorff_dist_image
               [(Term.app `kuratowskiEmbedding.isometry [(Term.hole "_")])]))))
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq "[" [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `this)] "]")
            [])
           []
           (Tactic.tacticLet_
            "let"
            (Term.letDecl
             (Term.letIdDecl
              `A
              []
              [(Term.typeSpec
                ":"
                (Term.app
                 `nonempty_compacts
                 [(Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ "ℓ_infty_ℝ")]))]
              ":="
              (Term.anonymousCtor
               "⟨"
               [(Term.anonymousCtor
                 "⟨"
                 [(Set.Data.Set.Image.term_''_ `F " '' " (Term.app `range [`Φ']))
                  ","
                  (Term.app
                   (Term.proj (Term.app `is_compact_range [`IΦ'.continuous]) "." `image)
                   [(Term.proj
                     (Term.app `kuratowskiEmbedding.isometry [(Term.hole "_")])
                     "."
                     `Continuous)])]
                 "⟩")
                ","
                (Term.app
                 (Term.proj (Term.app `range_nonempty [(Term.hole "_")]) "." `image)
                 [(Term.hole "_")])]
               "⟩"))))
           []
           (Tactic.tacticLet_
            "let"
            (Term.letDecl
             (Term.letIdDecl
              `B
              []
              [(Term.typeSpec
                ":"
                (Term.app
                 `nonempty_compacts
                 [(Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ "ℓ_infty_ℝ")]))]
              ":="
              (Term.anonymousCtor
               "⟨"
               [(Term.anonymousCtor
                 "⟨"
                 [(Set.Data.Set.Image.term_''_ `F " '' " (Term.app `range [`Ψ']))
                  ","
                  (Term.app
                   (Term.proj (Term.app `is_compact_range [`IΨ'.continuous]) "." `image)
                   [(Term.proj
                     (Term.app `kuratowskiEmbedding.isometry [(Term.hole "_")])
                     "."
                     `Continuous)])]
                 "⟩")
                ","
                (Term.app
                 (Term.proj (Term.app `range_nonempty [(Term.hole "_")]) "." `image)
                 [(Term.hole "_")])]
               "⟩"))))
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`AX []]
              [(Term.typeSpec
                ":"
                («term_=_»
                 (Quotient.Init.Data.Quot.«term⟦_⟧» "⟦" `A "⟧")
                 "="
                 (Term.app `to_GH_space [`X])))]
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Tactic.rwSeq
                   "rw"
                   []
                   (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `eq_to_GH_space_iff)] "]")
                   [])
                  []
                  (Tactic.exact
                   "exact"
                   (Term.anonymousCtor
                    "⟨"
                    [(Term.fun
                      "fun"
                      (Term.basicFun [`x] [] "=>" (Term.app `F [(Term.app `Φ' [`x])])))
                     ","
                     (Term.app
                      (Term.proj
                       (Term.app `kuratowskiEmbedding.isometry [(Term.hole "_")])
                       "."
                       `comp)
                      [`IΦ'])
                     ","
                     (Term.app `range_comp [(Term.hole "_") (Term.hole "_")])]
                    "⟩"))]))))))
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`BY []]
              [(Term.typeSpec
                ":"
                («term_=_»
                 (Quotient.Init.Data.Quot.«term⟦_⟧» "⟦" `B "⟧")
                 "="
                 (Term.app `to_GH_space [`Y])))]
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Tactic.rwSeq
                   "rw"
                   []
                   (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `eq_to_GH_space_iff)] "]")
                   [])
                  []
                  (Tactic.exact
                   "exact"
                   (Term.anonymousCtor
                    "⟨"
                    [(Term.fun
                      "fun"
                      (Term.basicFun [`x] [] "=>" (Term.app `F [(Term.app `Ψ' [`x])])))
                     ","
                     (Term.app
                      (Term.proj
                       (Term.app `kuratowskiEmbedding.isometry [(Term.hole "_")])
                       "."
                       `comp)
                      [`IΨ'])
                     ","
                     (Term.app `range_comp [(Term.hole "_") (Term.hole "_")])]
                    "⟩"))]))))))
           []
           (Tactic.refine'
            "refine'"
            (Term.app
             `cinfₛ_le
             [(Term.anonymousCtor "⟨" [(num "0") "," (Term.hole "_")] "⟩") (Term.hole "_")]))
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.simp
              "simp"
              []
              []
              ["only"]
              ["["
               [(Tactic.simpLemma [] [] `lowerBounds)
                ","
                (Tactic.simpLemma [] [] `mem_image)
                ","
                (Tactic.simpLemma [] [] `mem_prod)
                ","
                (Tactic.simpLemma [] [] `mem_set_of_eq)
                ","
                (Tactic.simpLemma [] [] `Prod.exists)
                ","
                (Tactic.simpLemma [] [] `and_imp)
                ","
                (Tactic.simpLemma [] [] `forall_exists_index)]
               "]"]
              [])
             []
             (Tactic.intro
              "intro"
              [`t (Term.hole "_") (Term.hole "_") (Term.hole "_") (Term.hole "_") `ht])
             []
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq "[" [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `ht)] "]")
              [])
             []
             (Tactic.exact "exact" `Hausdorff_dist_nonneg)])
           []
           (Tactic.apply
            "apply"
            (Term.proj
             (Term.app `mem_image [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
             "."
             (fieldIdx "2")))
           []
           (Tactic.«tacticExists_,,»
            "exists"
            [(Term.typeAscription
              "("
              (Term.anonymousCtor "⟨" [`A "," `B] "⟩")
              ":"
              [(«term_×_»
                (Term.app
                 `nonempty_compacts
                 [(Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ "ℓ_infty_ℝ")])
                "×"
                (Term.app
                 `nonempty_compacts
                 [(Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ "ℓ_infty_ℝ")]))]
              ")")])
           []
           (Tactic.simp
            "simp"
            []
            []
            []
            ["[" [(Tactic.simpLemma [] [] `AX) "," (Tactic.simpLemma [] [] `BY)] "]"]
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
         [(Std.Tactic.rcases
           "rcases"
           [(Tactic.casesTarget [] (Term.app `exists_mem_of_nonempty [`X]))]
           ["with"
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed
              [(Std.Tactic.RCases.rcasesPat.tuple
                "⟨"
                [(Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `xX)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.ignore "_")])
                  [])]
                "⟩")])
             [])])
          []
          (Tactic.tacticLet_
           "let"
           (Term.letDecl
            (Term.letIdDecl
             `s
             []
             [(Term.typeSpec ":" (Term.app `Set [`γ]))]
             ":="
             («term_∪_» (Term.app `range [`Φ]) "∪" (Term.app `range [`Ψ])))))
          []
          (Tactic.tacticLet_
           "let"
           (Term.letDecl
            (Term.letIdDecl
             `Φ'
             []
             [(Term.typeSpec ":" (Term.arrow `X "→" (Term.app `Subtype [`s])))]
             ":="
             (Term.fun
              "fun"
              (Term.basicFun
               [`y]
               []
               "=>"
               (Term.anonymousCtor
                "⟨"
                [(Term.app `Φ [`y])
                 ","
                 (Term.app
                  `mem_union_left
                  [(Term.hole "_") (Term.app `mem_range_self [(Term.hole "_")])])]
                "⟩"))))))
          []
          (Tactic.tacticLet_
           "let"
           (Term.letDecl
            (Term.letIdDecl
             `Ψ'
             []
             [(Term.typeSpec ":" (Term.arrow `Y "→" (Term.app `Subtype [`s])))]
             ":="
             (Term.fun
              "fun"
              (Term.basicFun
               [`y]
               []
               "=>"
               (Term.anonymousCtor
                "⟨"
                [(Term.app `Ψ [`y])
                 ","
                 (Term.app
                  `mem_union_right
                  [(Term.hole "_") (Term.app `mem_range_self [(Term.hole "_")])])]
                "⟩"))))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`IΦ' []]
             [(Term.typeSpec ":" (Term.app `Isometry [`Φ']))]
             ":="
             (Term.fun "fun" (Term.basicFun [`x `y] [] "=>" (Term.app `ha [`x `y]))))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`IΨ' []]
             [(Term.typeSpec ":" (Term.app `Isometry [`Ψ']))]
             ":="
             (Term.fun "fun" (Term.basicFun [`x `y] [] "=>" (Term.app `hb [`x `y]))))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             []
             [(Term.typeSpec ":" (Term.app `IsCompact [`s]))]
             ":="
             (Term.app
              (Term.proj (Term.app `is_compact_range [`ha.continuous]) "." `union)
              [(Term.app `is_compact_range [`hb.continuous])]))))
          []
          (Std.Tactic.tacticLetI_
           "letI"
           (Term.haveDecl
            (Term.haveIdDecl
             []
             [(Term.typeSpec ":" (Term.app `MetricSpace [(Term.app `Subtype [`s])]))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented [(Tactic.tacticInfer_instance "infer_instance")]))))))
          []
          (Std.Tactic.tacticHaveI_
           "haveI"
           (Term.haveDecl
            (Term.haveIdDecl
             []
             [(Term.typeSpec ":" (Term.app `CompactSpace [(Term.app `Subtype [`s])]))]
             ":="
             (Term.anonymousCtor
              "⟨"
              [(Term.app
                (Term.proj `is_compact_iff_is_compact_univ "." (fieldIdx "1"))
                [(«term‹_›» "‹" (Term.app `IsCompact [`s]) "›")])]
              "⟩"))))
          []
          (Std.Tactic.tacticHaveI_
           "haveI"
           (Term.haveDecl
            (Term.haveIdDecl
             []
             [(Term.typeSpec ":" (Term.app `Nonempty [(Term.app `Subtype [`s])]))]
             ":="
             (Term.anonymousCtor "⟨" [(Term.app `Φ' [`xX])] "⟩"))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`ΦΦ' []]
             [(Term.typeSpec ":" («term_=_» `Φ "=" («term_∘_» `Subtype.val "∘" `Φ')))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(tacticFunext__ "funext" []) [] (Tactic.tacticRfl "rfl")]))))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`ΨΨ' []]
             [(Term.typeSpec ":" («term_=_» `Ψ "=" («term_∘_» `Subtype.val "∘" `Ψ')))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(tacticFunext__ "funext" []) [] (Tactic.tacticRfl "rfl")]))))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             []
             [(Term.typeSpec
               ":"
               («term_=_»
                (Term.app `Hausdorff_dist [(Term.app `range [`Φ]) (Term.app `range [`Ψ])])
                "="
                (Term.app `Hausdorff_dist [(Term.app `range [`Φ']) (Term.app `range [`Ψ'])])))]
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
                   [(Tactic.rwRule [] `ΦΦ')
                    ","
                    (Tactic.rwRule [] `ΨΨ')
                    ","
                    (Tactic.rwRule [] `range_comp)
                    ","
                    (Tactic.rwRule [] `range_comp)]
                   "]")
                  [])
                 []
                 (Tactic.exact
                  "exact"
                  (Term.app `Hausdorff_dist_image [`isometry_subtype_coe]))]))))))
          []
          (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `this)] "]") [])
          []
          (Tactic.tacticLet_
           "let"
           (Term.letDecl
            (Term.letIdDecl
             `F
             []
             []
             ":="
             (Term.app `kuratowskiEmbedding [(Term.app `Subtype [`s])]))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             []
             [(Term.typeSpec
               ":"
               («term_=_»
                (Term.app
                 `Hausdorff_dist
                 [(Set.Data.Set.Image.term_''_ `F " '' " (Term.app `range [`Φ']))
                  (Set.Data.Set.Image.term_''_ `F " '' " (Term.app `range [`Ψ']))])
                "="
                (Term.app `Hausdorff_dist [(Term.app `range [`Φ']) (Term.app `range [`Ψ'])])))]
             ":="
             (Term.app
              `Hausdorff_dist_image
              [(Term.app `kuratowskiEmbedding.isometry [(Term.hole "_")])]))))
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `this)] "]")
           [])
          []
          (Tactic.tacticLet_
           "let"
           (Term.letDecl
            (Term.letIdDecl
             `A
             []
             [(Term.typeSpec
               ":"
               (Term.app
                `nonempty_compacts
                [(Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ "ℓ_infty_ℝ")]))]
             ":="
             (Term.anonymousCtor
              "⟨"
              [(Term.anonymousCtor
                "⟨"
                [(Set.Data.Set.Image.term_''_ `F " '' " (Term.app `range [`Φ']))
                 ","
                 (Term.app
                  (Term.proj (Term.app `is_compact_range [`IΦ'.continuous]) "." `image)
                  [(Term.proj
                    (Term.app `kuratowskiEmbedding.isometry [(Term.hole "_")])
                    "."
                    `Continuous)])]
                "⟩")
               ","
               (Term.app
                (Term.proj (Term.app `range_nonempty [(Term.hole "_")]) "." `image)
                [(Term.hole "_")])]
              "⟩"))))
          []
          (Tactic.tacticLet_
           "let"
           (Term.letDecl
            (Term.letIdDecl
             `B
             []
             [(Term.typeSpec
               ":"
               (Term.app
                `nonempty_compacts
                [(Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ "ℓ_infty_ℝ")]))]
             ":="
             (Term.anonymousCtor
              "⟨"
              [(Term.anonymousCtor
                "⟨"
                [(Set.Data.Set.Image.term_''_ `F " '' " (Term.app `range [`Ψ']))
                 ","
                 (Term.app
                  (Term.proj (Term.app `is_compact_range [`IΨ'.continuous]) "." `image)
                  [(Term.proj
                    (Term.app `kuratowskiEmbedding.isometry [(Term.hole "_")])
                    "."
                    `Continuous)])]
                "⟩")
               ","
               (Term.app
                (Term.proj (Term.app `range_nonempty [(Term.hole "_")]) "." `image)
                [(Term.hole "_")])]
              "⟩"))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`AX []]
             [(Term.typeSpec
               ":"
               («term_=_»
                (Quotient.Init.Data.Quot.«term⟦_⟧» "⟦" `A "⟧")
                "="
                (Term.app `to_GH_space [`X])))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `eq_to_GH_space_iff)] "]")
                  [])
                 []
                 (Tactic.exact
                  "exact"
                  (Term.anonymousCtor
                   "⟨"
                   [(Term.fun
                     "fun"
                     (Term.basicFun [`x] [] "=>" (Term.app `F [(Term.app `Φ' [`x])])))
                    ","
                    (Term.app
                     (Term.proj
                      (Term.app `kuratowskiEmbedding.isometry [(Term.hole "_")])
                      "."
                      `comp)
                     [`IΦ'])
                    ","
                    (Term.app `range_comp [(Term.hole "_") (Term.hole "_")])]
                   "⟩"))]))))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`BY []]
             [(Term.typeSpec
               ":"
               («term_=_»
                (Quotient.Init.Data.Quot.«term⟦_⟧» "⟦" `B "⟧")
                "="
                (Term.app `to_GH_space [`Y])))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `eq_to_GH_space_iff)] "]")
                  [])
                 []
                 (Tactic.exact
                  "exact"
                  (Term.anonymousCtor
                   "⟨"
                   [(Term.fun
                     "fun"
                     (Term.basicFun [`x] [] "=>" (Term.app `F [(Term.app `Ψ' [`x])])))
                    ","
                    (Term.app
                     (Term.proj
                      (Term.app `kuratowskiEmbedding.isometry [(Term.hole "_")])
                      "."
                      `comp)
                     [`IΨ'])
                    ","
                    (Term.app `range_comp [(Term.hole "_") (Term.hole "_")])]
                   "⟩"))]))))))
          []
          (Tactic.refine'
           "refine'"
           (Term.app
            `cinfₛ_le
            [(Term.anonymousCtor "⟨" [(num "0") "," (Term.hole "_")] "⟩") (Term.hole "_")]))
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.simp
             "simp"
             []
             []
             ["only"]
             ["["
              [(Tactic.simpLemma [] [] `lowerBounds)
               ","
               (Tactic.simpLemma [] [] `mem_image)
               ","
               (Tactic.simpLemma [] [] `mem_prod)
               ","
               (Tactic.simpLemma [] [] `mem_set_of_eq)
               ","
               (Tactic.simpLemma [] [] `Prod.exists)
               ","
               (Tactic.simpLemma [] [] `and_imp)
               ","
               (Tactic.simpLemma [] [] `forall_exists_index)]
              "]"]
             [])
            []
            (Tactic.intro
             "intro"
             [`t (Term.hole "_") (Term.hole "_") (Term.hole "_") (Term.hole "_") `ht])
            []
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq "[" [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `ht)] "]")
             [])
            []
            (Tactic.exact "exact" `Hausdorff_dist_nonneg)])
          []
          (Tactic.apply
           "apply"
           (Term.proj
            (Term.app `mem_image [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
            "."
            (fieldIdx "2")))
          []
          (Tactic.«tacticExists_,,»
           "exists"
           [(Term.typeAscription
             "("
             (Term.anonymousCtor "⟨" [`A "," `B] "⟩")
             ":"
             [(«term_×_»
               (Term.app
                `nonempty_compacts
                [(Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ "ℓ_infty_ℝ")])
               "×"
               (Term.app
                `nonempty_compacts
                [(Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ "ℓ_infty_ℝ")]))]
             ")")])
          []
          (Tactic.simp
           "simp"
           []
           []
           []
           ["[" [(Tactic.simpLemma [] [] `AX) "," (Tactic.simpLemma [] [] `BY)] "]"]
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       []
       ["[" [(Tactic.simpLemma [] [] `AX) "," (Tactic.simpLemma [] [] `BY)] "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `BY
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `AX
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.«tacticExists_,,»
       "exists"
       [(Term.typeAscription
         "("
         (Term.anonymousCtor "⟨" [`A "," `B] "⟩")
         ":"
         [(«term_×_»
           (Term.app
            `nonempty_compacts
            [(Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ "ℓ_infty_ℝ")])
           "×"
           (Term.app
            `nonempty_compacts
            [(Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ "ℓ_infty_ℝ")]))]
         ")")])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription
       "("
       (Term.anonymousCtor "⟨" [`A "," `B] "⟩")
       ":"
       [(«term_×_»
         (Term.app
          `nonempty_compacts
          [(Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ "ℓ_infty_ℝ")])
         "×"
         (Term.app
          `nonempty_compacts
          [(Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ "ℓ_infty_ℝ")]))]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_×_»
       (Term.app
        `nonempty_compacts
        [(Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ "ℓ_infty_ℝ")])
       "×"
       (Term.app
        `nonempty_compacts
        [(Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ "ℓ_infty_ℝ")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `nonempty_compacts
       [(Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ "ℓ_infty_ℝ")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ "ℓ_infty_ℝ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ', expected 'Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ._@.Topology.MetricSpace.GromovHausdorff._hyg.5'
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
    The Gromov-Hausdorff distance between two spaces is bounded by the Hausdorff distance
    of isometric copies of the spaces, in any metric space. -/
  theorem
    GH_dist_le_Hausdorff_dist
    { X : Type u }
        [ MetricSpace X ]
        [ CompactSpace X ]
        [ Nonempty X ]
        { Y : Type v }
        [ MetricSpace Y ]
        [ CompactSpace Y ]
        [ Nonempty Y ]
        { γ : Type w }
        [ MetricSpace γ ]
        { Φ : X → γ }
        { Ψ : Y → γ }
        ( ha : Isometry Φ )
        ( hb : Isometry Ψ )
      : gHDist X Y ≤ hausdorffDist range Φ range Ψ
    :=
      by
        rcases exists_mem_of_nonempty X with ⟨ xX , _ ⟩
          let s : Set γ := range Φ ∪ range Ψ
          let Φ' : X → Subtype s := fun y => ⟨ Φ y , mem_union_left _ mem_range_self _ ⟩
          let Ψ' : Y → Subtype s := fun y => ⟨ Ψ y , mem_union_right _ mem_range_self _ ⟩
          have IΦ' : Isometry Φ' := fun x y => ha x y
          have IΨ' : Isometry Ψ' := fun x y => hb x y
          have
            : IsCompact s := is_compact_range ha.continuous . union is_compact_range hb.continuous
          letI : MetricSpace Subtype s := by infer_instance
          haveI : CompactSpace Subtype s := ⟨ is_compact_iff_is_compact_univ . 1 ‹ IsCompact s › ⟩
          haveI : Nonempty Subtype s := ⟨ Φ' xX ⟩
          have ΦΦ' : Φ = Subtype.val ∘ Φ' := by funext rfl
          have ΨΨ' : Ψ = Subtype.val ∘ Ψ' := by funext rfl
          have
            : Hausdorff_dist range Φ range Ψ = Hausdorff_dist range Φ' range Ψ'
              :=
              by
                rw [ ΦΦ' , ΨΨ' , range_comp , range_comp ]
                  exact Hausdorff_dist_image isometry_subtype_coe
          rw [ this ]
          let F := kuratowskiEmbedding Subtype s
          have
            : Hausdorff_dist F '' range Φ' F '' range Ψ' = Hausdorff_dist range Φ' range Ψ'
              :=
              Hausdorff_dist_image kuratowskiEmbedding.isometry _
          rw [ ← this ]
          let
            A
              : nonempty_compacts ℓ_infty_ℝ
              :=
              ⟨
                ⟨
                    F '' range Φ'
                      ,
                      is_compact_range IΦ'.continuous . image
                        kuratowskiEmbedding.isometry _ . Continuous
                    ⟩
                  ,
                  range_nonempty _ . image _
                ⟩
          let
            B
              : nonempty_compacts ℓ_infty_ℝ
              :=
              ⟨
                ⟨
                    F '' range Ψ'
                      ,
                      is_compact_range IΨ'.continuous . image
                        kuratowskiEmbedding.isometry _ . Continuous
                    ⟩
                  ,
                  range_nonempty _ . image _
                ⟩
          have
            AX
              : ⟦ A ⟧ = to_GH_space X
              :=
              by
                rw [ eq_to_GH_space_iff ]
                  exact
                    ⟨ fun x => F Φ' x , kuratowskiEmbedding.isometry _ . comp IΦ' , range_comp _ _ ⟩
          have
            BY
              : ⟦ B ⟧ = to_GH_space Y
              :=
              by
                rw [ eq_to_GH_space_iff ]
                  exact
                    ⟨ fun x => F Ψ' x , kuratowskiEmbedding.isometry _ . comp IΨ' , range_comp _ _ ⟩
          refine' cinfₛ_le ⟨ 0 , _ ⟩ _
          ·
            simp
                only
                [
                  lowerBounds
                    ,
                    mem_image
                    ,
                    mem_prod
                    ,
                    mem_set_of_eq
                    ,
                    Prod.exists
                    ,
                    and_imp
                    ,
                    forall_exists_index
                  ]
              intro t _ _ _ _ ht
              rw [ ← ht ]
              exact Hausdorff_dist_nonneg
          apply mem_image _ _ _ . 2
          exists ( ⟨ A , B ⟩ : nonempty_compacts ℓ_infty_ℝ × nonempty_compacts ℓ_infty_ℝ )
          simp [ AX , BY ]
#align Gromov_Hausdorff.GH_dist_le_Hausdorff_dist GromovHausdorff.GH_dist_le_Hausdorff_dist

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "The optimal coupling constructed above realizes exactly the Gromov-Hausdorff distance,\nessentially by design. -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `Hausdorff_dist_optimal [])
      (Command.declSig
       [(Term.implicitBinder "{" [`X] [":" (Term.type "Type" [`u])] "}")
        (Term.instBinder "[" [] (Term.app `MetricSpace [`X]) "]")
        (Term.instBinder "[" [] (Term.app `CompactSpace [`X]) "]")
        (Term.instBinder "[" [] (Term.app `Nonempty [`X]) "]")
        (Term.implicitBinder "{" [`Y] [":" (Term.type "Type" [`v])] "}")
        (Term.instBinder "[" [] (Term.app `MetricSpace [`Y]) "]")
        (Term.instBinder "[" [] (Term.app `CompactSpace [`Y]) "]")
        (Term.instBinder "[" [] (Term.app `Nonempty [`Y]) "]")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app
          `hausdorffDist
          [(Term.app `range [(Term.app `optimalGHInjl [`X `Y])])
           (Term.app `range [(Term.app `optimalGHInjr [`X `Y])])])
         "="
         (Term.app `gHDist [`X `Y]))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Lean.Elab.Tactic.inhabit "inhabit" [] `X)
           []
           (Lean.Elab.Tactic.inhabit "inhabit" [] `Y)
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`A []]
              [(Term.typeSpec
                ":"
                (Term.forall
                 "∀"
                 [`p `q]
                 [(Term.typeSpec
                   ":"
                   (Term.app
                    `nonempty_compacts
                    [(Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ "ℓ_infty_ℝ")]))]
                 ","
                 (Term.arrow
                  («term_=_»
                   (Quotient.Init.Data.Quot.«term⟦_⟧» "⟦" `p "⟧")
                   "="
                   (Term.app `to_GH_space [`X]))
                  "→"
                  (Term.arrow
                   («term_=_»
                    (Quotient.Init.Data.Quot.«term⟦_⟧» "⟦" `q "⟧")
                    "="
                    (Term.app `to_GH_space [`Y]))
                   "→"
                   (Term.arrow
                    («term_<_»
                     (Term.app
                      `Hausdorff_dist
                      [(Term.typeAscription
                        "("
                        `p
                        ":"
                        [(Term.app
                          `Set
                          [(Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ "ℓ_infty_ℝ")])]
                        ")")
                       `q])
                     "<"
                     («term_+_»
                      («term_+_»
                       (Term.app
                        `diam
                        [(Term.typeAscription "(" `univ ":" [(Term.app `Set [`X])] ")")])
                       "+"
                       (num "1"))
                      "+"
                      (Term.app
                       `diam
                       [(Term.typeAscription "(" `univ ":" [(Term.app `Set [`Y])] ")")])))
                    "→"
                    («term_≤_»
                     (Term.app
                      `Hausdorff_dist
                      [(Term.app `range [(Term.app `optimal_GH_injl [`X `Y])])
                       (Term.app `range [(Term.app `optimal_GH_injr [`X `Y])])])
                     "≤"
                     (Term.app
                      `Hausdorff_dist
                      [(Term.typeAscription
                        "("
                        `p
                        ":"
                        [(Term.app
                          `Set
                          [(Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ "ℓ_infty_ℝ")])]
                        ")")
                       `q])))))))]
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Tactic.intro "intro" [`p `q `hp `hq `bound])
                  []
                  (Std.Tactic.rcases
                   "rcases"
                   [(Tactic.casesTarget
                     []
                     (Term.app (Term.proj `eq_to_GH_space_iff "." (fieldIdx "1")) [`hp]))]
                   ["with"
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed
                      [(Std.Tactic.RCases.rcasesPat.tuple
                        "⟨"
                        [(Std.Tactic.RCases.rcasesPatLo
                          (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `Φ)])
                          [])
                         ","
                         (Std.Tactic.RCases.rcasesPatLo
                          (Std.Tactic.RCases.rcasesPatMed
                           [(Std.Tactic.RCases.rcasesPat.tuple
                             "⟨"
                             [(Std.Tactic.RCases.rcasesPatLo
                               (Std.Tactic.RCases.rcasesPatMed
                                [(Std.Tactic.RCases.rcasesPat.one `Φisom)])
                               [])
                              ","
                              (Std.Tactic.RCases.rcasesPatLo
                               (Std.Tactic.RCases.rcasesPatMed
                                [(Std.Tactic.RCases.rcasesPat.one `Φrange)])
                               [])]
                             "⟩")])
                          [])]
                        "⟩")])
                     [])])
                  []
                  (Std.Tactic.rcases
                   "rcases"
                   [(Tactic.casesTarget
                     []
                     (Term.app (Term.proj `eq_to_GH_space_iff "." (fieldIdx "1")) [`hq]))]
                   ["with"
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed
                      [(Std.Tactic.RCases.rcasesPat.tuple
                        "⟨"
                        [(Std.Tactic.RCases.rcasesPatLo
                          (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `Ψ)])
                          [])
                         ","
                         (Std.Tactic.RCases.rcasesPatLo
                          (Std.Tactic.RCases.rcasesPatMed
                           [(Std.Tactic.RCases.rcasesPat.tuple
                             "⟨"
                             [(Std.Tactic.RCases.rcasesPatLo
                               (Std.Tactic.RCases.rcasesPatMed
                                [(Std.Tactic.RCases.rcasesPat.one `Ψisom)])
                               [])
                              ","
                              (Std.Tactic.RCases.rcasesPatLo
                               (Std.Tactic.RCases.rcasesPatMed
                                [(Std.Tactic.RCases.rcasesPat.one `Ψrange)])
                               [])]
                             "⟩")])
                          [])]
                        "⟩")])
                     [])])
                  []
                  (Tactic.tacticHave_
                   "have"
                   (Term.haveDecl
                    (Term.haveIdDecl
                     [`I []]
                     [(Term.typeSpec
                       ":"
                       («term_≤_»
                        (Term.app
                         `diam
                         [(«term_∪_» (Term.app `range [`Φ]) "∪" (Term.app `range [`Ψ]))])
                        "≤"
                        («term_+_»
                         («term_+_»
                          («term_*_»
                           (num "2")
                           "*"
                           (Term.app
                            `diam
                            [(Term.typeAscription "(" `univ ":" [(Term.app `Set [`X])] ")")]))
                          "+"
                          (num "1"))
                         "+"
                         («term_*_»
                          (num "2")
                          "*"
                          (Term.app
                           `diam
                           [(Term.typeAscription "(" `univ ":" [(Term.app `Set [`Y])] ")")])))))]
                     ":="
                     (Term.byTactic
                      "by"
                      (Tactic.tacticSeq
                       (Tactic.tacticSeq1Indented
                        [(Std.Tactic.rcases
                          "rcases"
                          [(Tactic.casesTarget [] (Term.app `exists_mem_of_nonempty [`X]))]
                          ["with"
                           (Std.Tactic.RCases.rcasesPatLo
                            (Std.Tactic.RCases.rcasesPatMed
                             [(Std.Tactic.RCases.rcasesPat.tuple
                               "⟨"
                               [(Std.Tactic.RCases.rcasesPatLo
                                 (Std.Tactic.RCases.rcasesPatMed
                                  [(Std.Tactic.RCases.rcasesPat.one `xX)])
                                 [])
                                ","
                                (Std.Tactic.RCases.rcasesPatLo
                                 (Std.Tactic.RCases.rcasesPatMed
                                  [(Std.Tactic.RCases.rcasesPat.ignore "_")])
                                 [])]
                               "⟩")])
                            [])])
                         []
                         (Tactic.tacticHave_
                          "have"
                          (Term.haveDecl
                           (Term.haveIdDecl
                            []
                            [(Term.typeSpec
                              ":"
                              (Std.ExtendedBinder.«term∃__,_»
                               "∃"
                               (Lean.binderIdent `y)
                               («binderTerm∈_» "∈" (Term.app `range [`Ψ]))
                               ","
                               («term_<_»
                                (Term.app `dist [(Term.app `Φ [`xX]) `y])
                                "<"
                                («term_+_»
                                 («term_+_»
                                  (Term.app
                                   `diam
                                   [(Term.typeAscription "(" `univ ":" [(Term.app `Set [`X])] ")")])
                                  "+"
                                  (num "1"))
                                 "+"
                                 (Term.app
                                  `diam
                                  [(Term.typeAscription
                                    "("
                                    `univ
                                    ":"
                                    [(Term.app `Set [`Y])]
                                    ")")])))))]
                            ":="
                            (Term.byTactic
                             "by"
                             (Tactic.tacticSeq
                              (Tactic.tacticSeq1Indented
                               [(Tactic.rwSeq
                                 "rw"
                                 []
                                 (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Ψrange)] "]")
                                 [])
                                []
                                (Tactic.tacticHave_
                                 "have"
                                 (Term.haveDecl
                                  (Term.haveIdDecl
                                   []
                                   [(Term.typeSpec
                                     ":"
                                     («term_∈_» (Term.app `Φ [`xX]) "∈" (coeNotation "↑" `p)))]
                                   ":="
                                   (Term.app
                                    `Φrange.subst
                                    [(Term.app `mem_range_self [(Term.hole "_")])]))))
                                []
                                (Tactic.exact
                                 "exact"
                                 (Term.app
                                  `exists_dist_lt_of_Hausdorff_dist_lt
                                  [`this
                                   `bound
                                   (Term.app
                                    `Hausdorff_edist_ne_top_of_nonempty_of_bounded
                                    [`p.nonempty
                                     `q.nonempty
                                     `p.is_compact.bounded
                                     `q.is_compact.bounded])]))]))))))
                         []
                         (Std.Tactic.rcases
                          "rcases"
                          [(Tactic.casesTarget [] `this)]
                          ["with"
                           (Std.Tactic.RCases.rcasesPatLo
                            (Std.Tactic.RCases.rcasesPatMed
                             [(Std.Tactic.RCases.rcasesPat.tuple
                               "⟨"
                               [(Std.Tactic.RCases.rcasesPatLo
                                 (Std.Tactic.RCases.rcasesPatMed
                                  [(Std.Tactic.RCases.rcasesPat.one `y)])
                                 [])
                                ","
                                (Std.Tactic.RCases.rcasesPatLo
                                 (Std.Tactic.RCases.rcasesPatMed
                                  [(Std.Tactic.RCases.rcasesPat.one `hy)])
                                 [])
                                ","
                                (Std.Tactic.RCases.rcasesPatLo
                                 (Std.Tactic.RCases.rcasesPatMed
                                  [(Std.Tactic.RCases.rcasesPat.one `dy)])
                                 [])]
                               "⟩")])
                            [])])
                         []
                         (Std.Tactic.rcases
                          "rcases"
                          [(Tactic.casesTarget
                            []
                            (Term.app (Term.proj `mem_range "." (fieldIdx "1")) [`hy]))]
                          ["with"
                           (Std.Tactic.RCases.rcasesPatLo
                            (Std.Tactic.RCases.rcasesPatMed
                             [(Std.Tactic.RCases.rcasesPat.tuple
                               "⟨"
                               [(Std.Tactic.RCases.rcasesPatLo
                                 (Std.Tactic.RCases.rcasesPatMed
                                  [(Std.Tactic.RCases.rcasesPat.one `z)])
                                 [])
                                ","
                                (Std.Tactic.RCases.rcasesPatLo
                                 (Std.Tactic.RCases.rcasesPatMed
                                  [(Std.Tactic.RCases.rcasesPat.one `hzy)])
                                 [])]
                               "⟩")])
                            [])])
                         []
                         (Tactic.rwSeq
                          "rw"
                          []
                          (Tactic.rwRuleSeq
                           "["
                           [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `hzy)]
                           "]")
                          [(Tactic.location "at" (Tactic.locationHyp [`dy] []))])
                         []
                         (Tactic.tacticHave_
                          "have"
                          (Term.haveDecl
                           (Term.haveIdDecl
                            [`DΦ []]
                            [(Term.typeSpec
                              ":"
                              («term_=_»
                               (Term.app `diam [(Term.app `range [`Φ])])
                               "="
                               (Term.app
                                `diam
                                [(Term.typeAscription "(" `univ ":" [(Term.app `Set [`X])] ")")])))]
                            ":="
                            `Φisom.diam_range)))
                         []
                         (Tactic.tacticHave_
                          "have"
                          (Term.haveDecl
                           (Term.haveIdDecl
                            [`DΨ []]
                            [(Term.typeSpec
                              ":"
                              («term_=_»
                               (Term.app `diam [(Term.app `range [`Ψ])])
                               "="
                               (Term.app
                                `diam
                                [(Term.typeAscription "(" `univ ":" [(Term.app `Set [`Y])] ")")])))]
                            ":="
                            `Ψisom.diam_range)))
                         []
                         (calcTactic
                          "calc"
                          (calcStep
                           («term_≤_»
                            (Term.app
                             `diam
                             [(«term_∪_» (Term.app `range [`Φ]) "∪" (Term.app `range [`Ψ]))])
                            "≤"
                            («term_+_»
                             («term_+_»
                              (Term.app `diam [(Term.app `range [`Φ])])
                              "+"
                              (Term.app `dist [(Term.app `Φ [`xX]) (Term.app `Ψ [`z])]))
                             "+"
                             (Term.app `diam [(Term.app `range [`Ψ])])))
                           ":="
                           (Term.app
                            `diam_union
                            [(Term.app `mem_range_self [(Term.hole "_")])
                             (Term.app `mem_range_self [(Term.hole "_")])]))
                          [(calcStep
                            («term_≤_»
                             (Term.hole "_")
                             "≤"
                             («term_+_»
                              («term_+_»
                               (Term.app
                                `diam
                                [(Term.typeAscription "(" `univ ":" [(Term.app `Set [`X])] ")")])
                               "+"
                               («term_+_»
                                («term_+_»
                                 (Term.app
                                  `diam
                                  [(Term.typeAscription "(" `univ ":" [(Term.app `Set [`X])] ")")])
                                 "+"
                                 (num "1"))
                                "+"
                                (Term.app
                                 `diam
                                 [(Term.typeAscription "(" `univ ":" [(Term.app `Set [`Y])] ")")])))
                              "+"
                              (Term.app
                               `diam
                               [(Term.typeAscription "(" `univ ":" [(Term.app `Set [`Y])] ")")])))
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
                                  [(Tactic.rwRule [] `DΦ) "," (Tactic.rwRule [] `DΨ)]
                                  "]")
                                 [])
                                []
                                (Tactic.apply
                                 "apply"
                                 (Term.app
                                  `add_le_add
                                  [(Term.app `add_le_add [`le_rfl (Term.app `le_of_lt [`dy])])
                                   `le_rfl]))]))))
                           (calcStep
                            («term_=_»
                             (Term.hole "_")
                             "="
                             («term_+_»
                              («term_+_»
                               («term_*_»
                                (num "2")
                                "*"
                                (Term.app
                                 `diam
                                 [(Term.typeAscription "(" `univ ":" [(Term.app `Set [`X])] ")")]))
                               "+"
                               (num "1"))
                              "+"
                              («term_*_»
                               (num "2")
                               "*"
                               (Term.app
                                `diam
                                [(Term.typeAscription "(" `univ ":" [(Term.app `Set [`Y])] ")")]))))
                            ":="
                            (Term.byTactic
                             "by"
                             (Tactic.tacticSeq
                              (Tactic.tacticSeq1Indented
                               [(Mathlib.Tactic.RingNF.ring "ring")]))))])]))))))
                  []
                  (Tactic.tacticLet_
                   "let"
                   (Term.letDecl
                    (Term.letIdDecl
                     `f
                     []
                     [(Term.typeSpec
                       ":"
                       (Term.arrow
                        (Term.app `Sum [`X `Y])
                        "→"
                        (Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ "ℓ_infty_ℝ")))]
                     ":="
                     (Term.fun
                      "fun"
                      (Term.basicFun
                       [`x]
                       []
                       "=>"
                       (Term.match
                        "match"
                        []
                        []
                        [(Term.matchDiscr [] `x)]
                        "with"
                        (Term.matchAlts
                         [(Term.matchAlt "|" [[(Term.app `inl [`y])]] "=>" (Term.app `Φ [`y]))
                          (Term.matchAlt
                           "|"
                           [[(Term.app `inr [`z])]]
                           "=>"
                           (Term.app `Ψ [`z]))])))))))
                  []
                  (Tactic.tacticLet_
                   "let"
                   (Term.letDecl
                    (Term.letIdDecl
                     `F
                     []
                     [(Term.typeSpec
                       ":"
                       (Term.arrow
                        («term_×_» (Term.app `Sum [`X `Y]) "×" (Term.app `Sum [`X `Y]))
                        "→"
                        (Data.Real.Basic.termℝ "ℝ")))]
                     ":="
                     (Term.fun
                      "fun"
                      (Term.basicFun
                       [`p]
                       []
                       "=>"
                       (Term.app
                        `dist
                        [(Term.app `f [(Term.proj `p "." (fieldIdx "1"))])
                         (Term.app `f [(Term.proj `p "." (fieldIdx "2"))])]))))))
                  []
                  (Tactic.tacticHave_
                   "have"
                   (Term.haveDecl
                    (Term.haveIdDecl
                     [`Fgood []]
                     [(Term.typeSpec ":" («term_∈_» `F "∈" (Term.app `candidates [`X `Y])))]
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
                           [(Tactic.simpLemma [] [] `candidates)
                            ","
                            (Tactic.simpLemma [] [] `forall_const)
                            ","
                            (Tactic.simpLemma [] [] `and_true_iff)
                            ","
                            (Tactic.simpLemma [] [] `add_comm)
                            ","
                            (Tactic.simpLemma [] [] `eq_self_iff_true)
                            ","
                            (Tactic.simpLemma [] [] `dist_eq_zero)
                            ","
                            (Tactic.simpLemma [] [] `and_self_iff)
                            ","
                            (Tactic.simpLemma [] [] `Set.mem_setOf_eq)]
                           "]"]
                          [])
                         []
                         (Std.Tactic.tacticRepeat'_
                          "repeat'"
                          (Tactic.tacticSeq
                           (Tactic.tacticSeq1Indented [(Tactic.constructor "constructor")])))
                         []
                         (tactic__
                          (cdotTk (patternIgnore (token.«· » "·")))
                          [(Tactic.exact
                            "exact"
                            (Term.fun
                             "fun"
                             (Term.basicFun
                              [`x `y]
                              []
                              "=>"
                              (calc
                               "calc"
                               (calcStep
                                («term_=_»
                                 (Term.app
                                  `F
                                  [(Term.tuple
                                    "("
                                    [(Term.app `inl [`x]) "," [(Term.app `inl [`y])]]
                                    ")")])
                                 "="
                                 (Term.app `dist [(Term.app `Φ [`x]) (Term.app `Φ [`y])]))
                                ":="
                                `rfl)
                               [(calcStep
                                 («term_=_» (Term.hole "_") "=" (Term.app `dist [`x `y]))
                                 ":="
                                 (Term.app `Φisom.dist_eq [`x `y]))]))))])
                         []
                         (tactic__
                          (cdotTk (patternIgnore (token.«· » "·")))
                          [(Tactic.exact
                            "exact"
                            (Term.fun
                             "fun"
                             (Term.basicFun
                              [`x `y]
                              []
                              "=>"
                              (calc
                               "calc"
                               (calcStep
                                («term_=_»
                                 (Term.app
                                  `F
                                  [(Term.tuple
                                    "("
                                    [(Term.app `inr [`x]) "," [(Term.app `inr [`y])]]
                                    ")")])
                                 "="
                                 (Term.app `dist [(Term.app `Ψ [`x]) (Term.app `Ψ [`y])]))
                                ":="
                                `rfl)
                               [(calcStep
                                 («term_=_» (Term.hole "_") "=" (Term.app `dist [`x `y]))
                                 ":="
                                 (Term.app `Ψisom.dist_eq [`x `y]))]))))])
                         []
                         (tactic__
                          (cdotTk (patternIgnore (token.«· » "·")))
                          [(Tactic.exact
                            "exact"
                            (Term.fun
                             "fun"
                             (Term.basicFun
                              [`x `y]
                              []
                              "=>"
                              (Term.app `dist_comm [(Term.hole "_") (Term.hole "_")]))))])
                         []
                         (tactic__
                          (cdotTk (patternIgnore (token.«· » "·")))
                          [(Tactic.exact
                            "exact"
                            (Term.fun
                             "fun"
                             (Term.basicFun
                              [`x `y `z]
                              []
                              "=>"
                              (Term.app
                               `dist_triangle
                               [(Term.hole "_") (Term.hole "_") (Term.hole "_")]))))])
                         []
                         (tactic__
                          (cdotTk (patternIgnore (token.«· » "·")))
                          [(Tactic.exact
                            "exact"
                            (Term.fun
                             "fun"
                             (Term.basicFun
                              [`x `y]
                              []
                              "=>"
                              (calc
                               "calc"
                               (calcStep
                                («term_≤_»
                                 (Term.app `F [(Term.tuple "(" [`x "," [`y]] ")")])
                                 "≤"
                                 (Term.app
                                  `diam
                                  [(«term_∪_» (Term.app `range [`Φ]) "∪" (Term.app `range [`Ψ]))]))
                                ":="
                                (Term.byTactic
                                 "by"
                                 (Tactic.tacticSeq
                                  (Tactic.tacticSeq1Indented
                                   [(Tactic.tacticHave_
                                     "have"
                                     (Term.haveDecl
                                      (Term.haveIdDecl
                                       [`A []]
                                       [(Term.typeSpec
                                         ":"
                                         (Term.forall
                                          "∀"
                                          [`z]
                                          [(Term.typeSpec ":" (Term.app `Sum [`X `Y]))]
                                          ","
                                          («term_∈_»
                                           (Term.app `f [`z])
                                           "∈"
                                           («term_∪_»
                                            (Term.app `range [`Φ])
                                            "∪"
                                            (Term.app `range [`Ψ])))))]
                                       ":="
                                       (Term.byTactic
                                        "by"
                                        (Tactic.tacticSeq
                                         (Tactic.tacticSeq1Indented
                                          [(Tactic.intro "intro" [`z])
                                           []
                                           (Tactic.cases "cases" [(Tactic.casesTarget [] `z)] [] [])
                                           []
                                           (tactic__
                                            (cdotTk (patternIgnore (token.«· » "·")))
                                            [(Tactic.apply "apply" `mem_union_left)
                                             []
                                             (Tactic.apply "apply" `mem_range_self)])
                                           []
                                           (tactic__
                                            (cdotTk (patternIgnore (token.«· » "·")))
                                            [(Tactic.apply "apply" `mem_union_right)
                                             []
                                             (Tactic.apply "apply" `mem_range_self)])]))))))
                                    []
                                    (Tactic.refine'
                                     "refine'"
                                     (Term.app
                                      `dist_le_diam_of_mem
                                      [(Term.hole "_")
                                       (Term.app `A [(Term.hole "_")])
                                       (Term.app `A [(Term.hole "_")])]))
                                    []
                                    (Tactic.rwSeq
                                     "rw"
                                     []
                                     (Tactic.rwRuleSeq
                                      "["
                                      [(Tactic.rwRule [] `Φrange) "," (Tactic.rwRule [] `Ψrange)]
                                      "]")
                                     [])
                                    []
                                    (Tactic.exact
                                     "exact"
                                     (Term.proj
                                      (Term.proj (Order.Basic.«term_⊔_» `p " ⊔ " `q) "." `IsCompact)
                                      "."
                                      `Bounded))]))))
                               [(calcStep
                                 («term_≤_»
                                  (Term.hole "_")
                                  "≤"
                                  («term_+_»
                                   («term_+_»
                                    («term_*_»
                                     (num "2")
                                     "*"
                                     (Term.app
                                      `diam
                                      [(Term.typeAscription
                                        "("
                                        `univ
                                        ":"
                                        [(Term.app `Set [`X])]
                                        ")")]))
                                    "+"
                                    (num "1"))
                                   "+"
                                   («term_*_»
                                    (num "2")
                                    "*"
                                    (Term.app
                                     `diam
                                     [(Term.typeAscription
                                       "("
                                       `univ
                                       ":"
                                       [(Term.app `Set [`Y])]
                                       ")")]))))
                                 ":="
                                 `I)]))))])]))))))
                  []
                  (Tactic.tacticLet_
                   "let"
                   (Term.letDecl
                    (Term.letIdDecl
                     `Fb
                     []
                     []
                     ":="
                     (Term.app `candidates_b_of_candidates [`F `Fgood]))))
                  []
                  (Tactic.tacticHave_
                   "have"
                   (Term.haveDecl
                    (Term.haveIdDecl
                     []
                     [(Term.typeSpec
                       ":"
                       («term_≤_»
                        (Term.app
                         `Hausdorff_dist
                         [(Term.app `range [(Term.app `optimal_GH_injl [`X `Y])])
                          (Term.app `range [(Term.app `optimal_GH_injr [`X `Y])])])
                        "≤"
                        (Term.app `HD [`Fb])))]
                     ":="
                     (Term.app
                      `Hausdorff_dist_optimal_le_HD
                      [(Term.hole "_")
                       (Term.hole "_")
                       (Term.app `candidates_b_of_candidates_mem [`F `Fgood])]))))
                  []
                  (Tactic.refine'
                   "refine'"
                   (Term.app
                    `le_trans
                    [`this
                     (Term.app
                      `le_of_forall_le_of_dense
                      [(Term.fun "fun" (Term.basicFun [`r `hr] [] "=>" (Term.hole "_")))])]))
                  []
                  (Tactic.tacticHave_
                   "have"
                   (Term.haveDecl
                    (Term.haveIdDecl
                     [`I1 []]
                     [(Term.typeSpec
                       ":"
                       (Term.forall
                        "∀"
                        [`x]
                        [(Term.typeSpec ":" `X)]
                        ","
                        («term_≤_»
                         (Order.CompleteLattice.«term⨅_,_»
                          "⨅"
                          (Std.ExtendedBinder.extBinders
                           (Std.ExtendedBinder.extBinder (Lean.binderIdent `y) []))
                          ", "
                          (Term.app
                           `Fb
                           [(Term.tuple
                             "("
                             [(Term.app `inl [`x]) "," [(Term.app `inr [`y])]]
                             ")")]))
                         "≤"
                         `r)))]
                     ":="
                     (Term.byTactic
                      "by"
                      (Tactic.tacticSeq
                       (Tactic.tacticSeq1Indented
                        [(Tactic.intro "intro" [`x])
                         []
                         (Tactic.tacticHave_
                          "have"
                          (Term.haveDecl
                           (Term.haveIdDecl
                            []
                            [(Term.typeSpec
                              ":"
                              («term_∈_»
                               (Term.app `f [(Term.app `inl [`x])])
                               "∈"
                               (coeNotation "↑" `p)))]
                            ":="
                            (Term.app
                             `Φrange.subst
                             [(Term.app `mem_range_self [(Term.hole "_")])]))))
                         []
                         (Std.Tactic.rcases
                          "rcases"
                          [(Tactic.casesTarget
                            []
                            (Term.app
                             `exists_dist_lt_of_Hausdorff_dist_lt
                             [`this
                              `hr
                              (Term.app
                               `Hausdorff_edist_ne_top_of_nonempty_of_bounded
                               [`p.nonempty
                                `q.nonempty
                                `p.is_compact.bounded
                                `q.is_compact.bounded])]))]
                          ["with"
                           (Std.Tactic.RCases.rcasesPatLo
                            (Std.Tactic.RCases.rcasesPatMed
                             [(Std.Tactic.RCases.rcasesPat.tuple
                               "⟨"
                               [(Std.Tactic.RCases.rcasesPatLo
                                 (Std.Tactic.RCases.rcasesPatMed
                                  [(Std.Tactic.RCases.rcasesPat.one `z)])
                                 [])
                                ","
                                (Std.Tactic.RCases.rcasesPatLo
                                 (Std.Tactic.RCases.rcasesPatMed
                                  [(Std.Tactic.RCases.rcasesPat.one `zq)])
                                 [])
                                ","
                                (Std.Tactic.RCases.rcasesPatLo
                                 (Std.Tactic.RCases.rcasesPatMed
                                  [(Std.Tactic.RCases.rcasesPat.one `hz)])
                                 [])]
                               "⟩")])
                            [])])
                         []
                         (Tactic.tacticHave_
                          "have"
                          (Term.haveDecl
                           (Term.haveIdDecl
                            []
                            [(Term.typeSpec ":" («term_∈_» `z "∈" (Term.app `range [`Ψ])))]
                            ":="
                            (Term.byTactic
                             "by"
                             (Tactic.tacticSeq
                              (Tactic.tacticSeq1Indented
                               [(Std.Tactic.tacticRwa__
                                 "rwa"
                                 (Tactic.rwRuleSeq
                                  "["
                                  [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Ψrange)]
                                  "]")
                                 [(Tactic.location "at" (Tactic.locationHyp [`zq] []))])]))))))
                         []
                         (Std.Tactic.rcases
                          "rcases"
                          [(Tactic.casesTarget
                            []
                            (Term.app (Term.proj `mem_range "." (fieldIdx "1")) [`this]))]
                          ["with"
                           (Std.Tactic.RCases.rcasesPatLo
                            (Std.Tactic.RCases.rcasesPatMed
                             [(Std.Tactic.RCases.rcasesPat.tuple
                               "⟨"
                               [(Std.Tactic.RCases.rcasesPatLo
                                 (Std.Tactic.RCases.rcasesPatMed
                                  [(Std.Tactic.RCases.rcasesPat.one `y)])
                                 [])
                                ","
                                (Std.Tactic.RCases.rcasesPatLo
                                 (Std.Tactic.RCases.rcasesPatMed
                                  [(Std.Tactic.RCases.rcasesPat.one `hy)])
                                 [])]
                               "⟩")])
                            [])])
                         []
                         (calcTactic
                          "calc"
                          (calcStep
                           («term_≤_»
                            (Order.CompleteLattice.«term⨅_,_»
                             "⨅"
                             (Std.ExtendedBinder.extBinders
                              (Std.ExtendedBinder.extBinder (Lean.binderIdent `y) []))
                             ", "
                             (Term.app
                              `Fb
                              [(Term.tuple
                                "("
                                [(Term.app `inl [`x]) "," [(Term.app `inr [`y])]]
                                ")")]))
                            "≤"
                            (Term.app
                             `Fb
                             [(Term.tuple
                               "("
                               [(Term.app `inl [`x]) "," [(Term.app `inr [`y])]]
                               ")")]))
                           ":="
                           (Term.app
                            `cinfᵢ_le
                            [(Term.byTactic
                              "by"
                              (Tactic.tacticSeq
                               (Tactic.tacticSeq1Indented
                                [(Std.Tactic.Simpa.simpa
                                  "simpa"
                                  []
                                  []
                                  (Std.Tactic.Simpa.simpaArgsRest
                                   []
                                   []
                                   ["only"]
                                   [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `add_zero)] "]")]
                                   ["using" (Term.app `HD_below_aux1 [(num "0")])]))])))
                             `y]))
                          [(calcStep
                            («term_=_»
                             (Term.hole "_")
                             "="
                             (Term.app `dist [(Term.app `Φ [`x]) (Term.app `Ψ [`y])]))
                            ":="
                            `rfl)
                           (calcStep
                            («term_=_»
                             (Term.hole "_")
                             "="
                             (Term.app `dist [(Term.app `f [(Term.app `inl [`x])]) `z]))
                            ":="
                            (Term.byTactic
                             "by"
                             (Tactic.tacticSeq
                              (Tactic.tacticSeq1Indented
                               [(Tactic.rwSeq
                                 "rw"
                                 []
                                 (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `hy)] "]")
                                 [])]))))
                           (calcStep
                            («term_≤_» (Term.hole "_") "≤" `r)
                            ":="
                            (Term.app `le_of_lt [`hz]))])]))))))
                  []
                  (Tactic.tacticHave_
                   "have"
                   (Term.haveDecl
                    (Term.haveIdDecl
                     [`I2 []]
                     [(Term.typeSpec
                       ":"
                       (Term.forall
                        "∀"
                        [`y]
                        [(Term.typeSpec ":" `Y)]
                        ","
                        («term_≤_»
                         (Order.CompleteLattice.«term⨅_,_»
                          "⨅"
                          (Std.ExtendedBinder.extBinders
                           (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
                          ", "
                          (Term.app
                           `Fb
                           [(Term.tuple
                             "("
                             [(Term.app `inl [`x]) "," [(Term.app `inr [`y])]]
                             ")")]))
                         "≤"
                         `r)))]
                     ":="
                     (Term.byTactic
                      "by"
                      (Tactic.tacticSeq
                       (Tactic.tacticSeq1Indented
                        [(Tactic.intro "intro" [`y])
                         []
                         (Tactic.tacticHave_
                          "have"
                          (Term.haveDecl
                           (Term.haveIdDecl
                            []
                            [(Term.typeSpec
                              ":"
                              («term_∈_»
                               (Term.app `f [(Term.app `inr [`y])])
                               "∈"
                               (coeNotation "↑" `q)))]
                            ":="
                            (Term.app
                             `Ψrange.subst
                             [(Term.app `mem_range_self [(Term.hole "_")])]))))
                         []
                         (Std.Tactic.rcases
                          "rcases"
                          [(Tactic.casesTarget
                            []
                            (Term.app
                             `exists_dist_lt_of_Hausdorff_dist_lt'
                             [`this
                              `hr
                              (Term.app
                               `Hausdorff_edist_ne_top_of_nonempty_of_bounded
                               [`p.nonempty
                                `q.nonempty
                                `p.is_compact.bounded
                                `q.is_compact.bounded])]))]
                          ["with"
                           (Std.Tactic.RCases.rcasesPatLo
                            (Std.Tactic.RCases.rcasesPatMed
                             [(Std.Tactic.RCases.rcasesPat.tuple
                               "⟨"
                               [(Std.Tactic.RCases.rcasesPatLo
                                 (Std.Tactic.RCases.rcasesPatMed
                                  [(Std.Tactic.RCases.rcasesPat.one `z)])
                                 [])
                                ","
                                (Std.Tactic.RCases.rcasesPatLo
                                 (Std.Tactic.RCases.rcasesPatMed
                                  [(Std.Tactic.RCases.rcasesPat.one `zq)])
                                 [])
                                ","
                                (Std.Tactic.RCases.rcasesPatLo
                                 (Std.Tactic.RCases.rcasesPatMed
                                  [(Std.Tactic.RCases.rcasesPat.one `hz)])
                                 [])]
                               "⟩")])
                            [])])
                         []
                         (Tactic.tacticHave_
                          "have"
                          (Term.haveDecl
                           (Term.haveIdDecl
                            []
                            [(Term.typeSpec ":" («term_∈_» `z "∈" (Term.app `range [`Φ])))]
                            ":="
                            (Term.byTactic
                             "by"
                             (Tactic.tacticSeq
                              (Tactic.tacticSeq1Indented
                               [(Std.Tactic.tacticRwa__
                                 "rwa"
                                 (Tactic.rwRuleSeq
                                  "["
                                  [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Φrange)]
                                  "]")
                                 [(Tactic.location "at" (Tactic.locationHyp [`zq] []))])]))))))
                         []
                         (Std.Tactic.rcases
                          "rcases"
                          [(Tactic.casesTarget
                            []
                            (Term.app (Term.proj `mem_range "." (fieldIdx "1")) [`this]))]
                          ["with"
                           (Std.Tactic.RCases.rcasesPatLo
                            (Std.Tactic.RCases.rcasesPatMed
                             [(Std.Tactic.RCases.rcasesPat.tuple
                               "⟨"
                               [(Std.Tactic.RCases.rcasesPatLo
                                 (Std.Tactic.RCases.rcasesPatMed
                                  [(Std.Tactic.RCases.rcasesPat.one `x)])
                                 [])
                                ","
                                (Std.Tactic.RCases.rcasesPatLo
                                 (Std.Tactic.RCases.rcasesPatMed
                                  [(Std.Tactic.RCases.rcasesPat.one `hx)])
                                 [])]
                               "⟩")])
                            [])])
                         []
                         (calcTactic
                          "calc"
                          (calcStep
                           («term_≤_»
                            (Order.CompleteLattice.«term⨅_,_»
                             "⨅"
                             (Std.ExtendedBinder.extBinders
                              (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
                             ", "
                             (Term.app
                              `Fb
                              [(Term.tuple
                                "("
                                [(Term.app `inl [`x]) "," [(Term.app `inr [`y])]]
                                ")")]))
                            "≤"
                            (Term.app
                             `Fb
                             [(Term.tuple
                               "("
                               [(Term.app `inl [`x]) "," [(Term.app `inr [`y])]]
                               ")")]))
                           ":="
                           (Term.app
                            `cinfᵢ_le
                            [(Term.byTactic
                              "by"
                              (Tactic.tacticSeq
                               (Tactic.tacticSeq1Indented
                                [(Std.Tactic.Simpa.simpa
                                  "simpa"
                                  []
                                  []
                                  (Std.Tactic.Simpa.simpaArgsRest
                                   []
                                   []
                                   ["only"]
                                   [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `add_zero)] "]")]
                                   ["using" (Term.app `HD_below_aux2 [(num "0")])]))])))
                             `x]))
                          [(calcStep
                            («term_=_»
                             (Term.hole "_")
                             "="
                             (Term.app `dist [(Term.app `Φ [`x]) (Term.app `Ψ [`y])]))
                            ":="
                            `rfl)
                           (calcStep
                            («term_=_»
                             (Term.hole "_")
                             "="
                             (Term.app `dist [`z (Term.app `f [(Term.app `inr [`y])])]))
                            ":="
                            (Term.byTactic
                             "by"
                             (Tactic.tacticSeq
                              (Tactic.tacticSeq1Indented
                               [(Tactic.rwSeq
                                 "rw"
                                 []
                                 (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `hx)] "]")
                                 [])]))))
                           (calcStep
                            («term_≤_» (Term.hole "_") "≤" `r)
                            ":="
                            (Term.app `le_of_lt [`hz]))])]))))))
                  []
                  (Tactic.simp
                   "simp"
                   []
                   []
                   ["only"]
                   ["["
                    [(Tactic.simpLemma [] [] `HD)
                     ","
                     (Tactic.simpLemma [] [] (Term.app `csupᵢ_le [`I1]))
                     ","
                     (Tactic.simpLemma [] [] (Term.app `csupᵢ_le [`I2]))
                     ","
                     (Tactic.simpLemma [] [] `max_le_iff)
                     ","
                     (Tactic.simpLemma [] [] `and_self_iff)]
                    "]"]
                   [])]))))))
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`B []]
              [(Term.typeSpec
                ":"
                (Term.forall
                 "∀"
                 [`p `q]
                 [(Term.typeSpec
                   ":"
                   (Term.app
                    `nonempty_compacts
                    [(Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ "ℓ_infty_ℝ")]))]
                 ","
                 (Term.arrow
                  («term_=_»
                   (Quotient.Init.Data.Quot.«term⟦_⟧» "⟦" `p "⟧")
                   "="
                   (Term.app `to_GH_space [`X]))
                  "→"
                  (Term.arrow
                   («term_=_»
                    (Quotient.Init.Data.Quot.«term⟦_⟧» "⟦" `q "⟧")
                    "="
                    (Term.app `to_GH_space [`Y]))
                   "→"
                   («term_≤_»
                    (Term.app
                     `Hausdorff_dist
                     [(Term.app `range [(Term.app `optimal_GH_injl [`X `Y])])
                      (Term.app `range [(Term.app `optimal_GH_injr [`X `Y])])])
                    "≤"
                    (Term.app
                     `Hausdorff_dist
                     [(Term.typeAscription
                       "("
                       `p
                       ":"
                       [(Term.app
                         `Set
                         [(Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ "ℓ_infty_ℝ")])]
                       ")")
                      `q]))))))]
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Tactic.intro "intro" [`p `q `hp `hq])
                  []
                  (Classical.«tacticBy_cases_:_»
                   "by_cases"
                   [`h ":"]
                   («term_<_»
                    (Term.app
                     `Hausdorff_dist
                     [(Term.typeAscription
                       "("
                       `p
                       ":"
                       [(Term.app
                         `Set
                         [(Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ "ℓ_infty_ℝ")])]
                       ")")
                      `q])
                    "<"
                    («term_+_»
                     («term_+_»
                      (Term.app
                       `diam
                       [(Term.typeAscription "(" `univ ":" [(Term.app `Set [`X])] ")")])
                      "+"
                      (num "1"))
                     "+"
                     (Term.app
                      `diam
                      [(Term.typeAscription "(" `univ ":" [(Term.app `Set [`Y])] ")")]))))
                  []
                  (tactic__
                   (cdotTk (patternIgnore (token.«· » "·")))
                   [(Tactic.exact "exact" (Term.app `A [`p `q `hp `hq `h]))])
                  []
                  (tactic__
                   (cdotTk (patternIgnore (token.«· » "·")))
                   [(calcTactic
                     "calc"
                     (calcStep
                      («term_≤_»
                       (Term.app
                        `Hausdorff_dist
                        [(Term.app `range [(Term.app `optimal_GH_injl [`X `Y])])
                         (Term.app `range [(Term.app `optimal_GH_injr [`X `Y])])])
                       "≤"
                       (Term.app `HD [(Term.app `candidates_b_dist [`X `Y])]))
                      ":="
                      (Term.app
                       `Hausdorff_dist_optimal_le_HD
                       [(Term.hole "_") (Term.hole "_") `candidates_b_dist_mem_candidates_b]))
                     [(calcStep
                       («term_≤_»
                        (Term.hole "_")
                        "≤"
                        («term_+_»
                         («term_+_»
                          (Term.app
                           `diam
                           [(Term.typeAscription "(" `univ ":" [(Term.app `Set [`X])] ")")])
                          "+"
                          (num "1"))
                         "+"
                         (Term.app
                          `diam
                          [(Term.typeAscription "(" `univ ":" [(Term.app `Set [`Y])] ")")])))
                       ":="
                       `HD_candidates_b_dist_le)
                      (calcStep
                       («term_≤_»
                        (Term.hole "_")
                        "≤"
                        (Term.app
                         `Hausdorff_dist
                         [(Term.typeAscription
                           "("
                           `p
                           ":"
                           [(Term.app
                             `Set
                             [(Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ "ℓ_infty_ℝ")])]
                           ")")
                          `q]))
                       ":="
                       (Term.app (Term.proj `not_lt "." (fieldIdx "1")) [`h]))])])]))))))
           []
           (Tactic.refine' "refine'" (Term.app `le_antisymm [(Term.hole "_") (Term.hole "_")]))
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.apply "apply" `le_cinfₛ)
             []
             (tactic__
              (cdotTk (patternIgnore (token.«· » "·")))
              [(Tactic.«tactic_<;>_»
                (Tactic.refine'
                 "refine'"
                 (Term.app
                  (Term.proj
                   (Term.app `Set.Nonempty.prod [(Term.hole "_") (Term.hole "_")])
                   "."
                   `image)
                  [(Term.hole "_")]))
                "<;>"
                (Tactic.exact "exact" (Term.anonymousCtor "⟨" [(Term.hole "_") "," `rfl] "⟩")))])
             []
             (tactic__
              (cdotTk (patternIgnore (token.«· » "·")))
              [(Std.Tactic.rintro
                "rintro"
                [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `b))
                 (Std.Tactic.RCases.rintroPat.one
                  (Std.Tactic.RCases.rcasesPat.tuple
                   "⟨"
                   [(Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed
                      [(Std.Tactic.RCases.rcasesPat.tuple
                        "⟨"
                        [(Std.Tactic.RCases.rcasesPatLo
                          (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `p)])
                          [])
                         ","
                         (Std.Tactic.RCases.rcasesPatLo
                          (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `q)])
                          [])]
                        "⟩")])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed
                      [(Std.Tactic.RCases.rcasesPat.tuple
                        "⟨"
                        [(Std.Tactic.RCases.rcasesPatLo
                          (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hp)])
                          [])
                         ","
                         (Std.Tactic.RCases.rcasesPatLo
                          (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hq)])
                          [])]
                        "⟩")])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                     [])]
                   "⟩"))]
                [])
               []
               (Tactic.exact "exact" (Term.app `B [`p `q `hp `hq]))])])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.exact
              "exact"
              (Term.app
               `GH_dist_le_Hausdorff_dist
               [(Term.app `isometry_optimal_GH_injl [`X `Y])
                (Term.app `isometry_optimal_GH_injr [`X `Y])]))])])))
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
         [(Lean.Elab.Tactic.inhabit "inhabit" [] `X)
          []
          (Lean.Elab.Tactic.inhabit "inhabit" [] `Y)
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`A []]
             [(Term.typeSpec
               ":"
               (Term.forall
                "∀"
                [`p `q]
                [(Term.typeSpec
                  ":"
                  (Term.app
                   `nonempty_compacts
                   [(Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ "ℓ_infty_ℝ")]))]
                ","
                (Term.arrow
                 («term_=_»
                  (Quotient.Init.Data.Quot.«term⟦_⟧» "⟦" `p "⟧")
                  "="
                  (Term.app `to_GH_space [`X]))
                 "→"
                 (Term.arrow
                  («term_=_»
                   (Quotient.Init.Data.Quot.«term⟦_⟧» "⟦" `q "⟧")
                   "="
                   (Term.app `to_GH_space [`Y]))
                  "→"
                  (Term.arrow
                   («term_<_»
                    (Term.app
                     `Hausdorff_dist
                     [(Term.typeAscription
                       "("
                       `p
                       ":"
                       [(Term.app
                         `Set
                         [(Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ "ℓ_infty_ℝ")])]
                       ")")
                      `q])
                    "<"
                    («term_+_»
                     («term_+_»
                      (Term.app
                       `diam
                       [(Term.typeAscription "(" `univ ":" [(Term.app `Set [`X])] ")")])
                      "+"
                      (num "1"))
                     "+"
                     (Term.app
                      `diam
                      [(Term.typeAscription "(" `univ ":" [(Term.app `Set [`Y])] ")")])))
                   "→"
                   («term_≤_»
                    (Term.app
                     `Hausdorff_dist
                     [(Term.app `range [(Term.app `optimal_GH_injl [`X `Y])])
                      (Term.app `range [(Term.app `optimal_GH_injr [`X `Y])])])
                    "≤"
                    (Term.app
                     `Hausdorff_dist
                     [(Term.typeAscription
                       "("
                       `p
                       ":"
                       [(Term.app
                         `Set
                         [(Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ "ℓ_infty_ℝ")])]
                       ")")
                      `q])))))))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.intro "intro" [`p `q `hp `hq `bound])
                 []
                 (Std.Tactic.rcases
                  "rcases"
                  [(Tactic.casesTarget
                    []
                    (Term.app (Term.proj `eq_to_GH_space_iff "." (fieldIdx "1")) [`hp]))]
                  ["with"
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed
                     [(Std.Tactic.RCases.rcasesPat.tuple
                       "⟨"
                       [(Std.Tactic.RCases.rcasesPatLo
                         (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `Φ)])
                         [])
                        ","
                        (Std.Tactic.RCases.rcasesPatLo
                         (Std.Tactic.RCases.rcasesPatMed
                          [(Std.Tactic.RCases.rcasesPat.tuple
                            "⟨"
                            [(Std.Tactic.RCases.rcasesPatLo
                              (Std.Tactic.RCases.rcasesPatMed
                               [(Std.Tactic.RCases.rcasesPat.one `Φisom)])
                              [])
                             ","
                             (Std.Tactic.RCases.rcasesPatLo
                              (Std.Tactic.RCases.rcasesPatMed
                               [(Std.Tactic.RCases.rcasesPat.one `Φrange)])
                              [])]
                            "⟩")])
                         [])]
                       "⟩")])
                    [])])
                 []
                 (Std.Tactic.rcases
                  "rcases"
                  [(Tactic.casesTarget
                    []
                    (Term.app (Term.proj `eq_to_GH_space_iff "." (fieldIdx "1")) [`hq]))]
                  ["with"
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed
                     [(Std.Tactic.RCases.rcasesPat.tuple
                       "⟨"
                       [(Std.Tactic.RCases.rcasesPatLo
                         (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `Ψ)])
                         [])
                        ","
                        (Std.Tactic.RCases.rcasesPatLo
                         (Std.Tactic.RCases.rcasesPatMed
                          [(Std.Tactic.RCases.rcasesPat.tuple
                            "⟨"
                            [(Std.Tactic.RCases.rcasesPatLo
                              (Std.Tactic.RCases.rcasesPatMed
                               [(Std.Tactic.RCases.rcasesPat.one `Ψisom)])
                              [])
                             ","
                             (Std.Tactic.RCases.rcasesPatLo
                              (Std.Tactic.RCases.rcasesPatMed
                               [(Std.Tactic.RCases.rcasesPat.one `Ψrange)])
                              [])]
                            "⟩")])
                         [])]
                       "⟩")])
                    [])])
                 []
                 (Tactic.tacticHave_
                  "have"
                  (Term.haveDecl
                   (Term.haveIdDecl
                    [`I []]
                    [(Term.typeSpec
                      ":"
                      («term_≤_»
                       (Term.app
                        `diam
                        [(«term_∪_» (Term.app `range [`Φ]) "∪" (Term.app `range [`Ψ]))])
                       "≤"
                       («term_+_»
                        («term_+_»
                         («term_*_»
                          (num "2")
                          "*"
                          (Term.app
                           `diam
                           [(Term.typeAscription "(" `univ ":" [(Term.app `Set [`X])] ")")]))
                         "+"
                         (num "1"))
                        "+"
                        («term_*_»
                         (num "2")
                         "*"
                         (Term.app
                          `diam
                          [(Term.typeAscription "(" `univ ":" [(Term.app `Set [`Y])] ")")])))))]
                    ":="
                    (Term.byTactic
                     "by"
                     (Tactic.tacticSeq
                      (Tactic.tacticSeq1Indented
                       [(Std.Tactic.rcases
                         "rcases"
                         [(Tactic.casesTarget [] (Term.app `exists_mem_of_nonempty [`X]))]
                         ["with"
                          (Std.Tactic.RCases.rcasesPatLo
                           (Std.Tactic.RCases.rcasesPatMed
                            [(Std.Tactic.RCases.rcasesPat.tuple
                              "⟨"
                              [(Std.Tactic.RCases.rcasesPatLo
                                (Std.Tactic.RCases.rcasesPatMed
                                 [(Std.Tactic.RCases.rcasesPat.one `xX)])
                                [])
                               ","
                               (Std.Tactic.RCases.rcasesPatLo
                                (Std.Tactic.RCases.rcasesPatMed
                                 [(Std.Tactic.RCases.rcasesPat.ignore "_")])
                                [])]
                              "⟩")])
                           [])])
                        []
                        (Tactic.tacticHave_
                         "have"
                         (Term.haveDecl
                          (Term.haveIdDecl
                           []
                           [(Term.typeSpec
                             ":"
                             (Std.ExtendedBinder.«term∃__,_»
                              "∃"
                              (Lean.binderIdent `y)
                              («binderTerm∈_» "∈" (Term.app `range [`Ψ]))
                              ","
                              («term_<_»
                               (Term.app `dist [(Term.app `Φ [`xX]) `y])
                               "<"
                               («term_+_»
                                («term_+_»
                                 (Term.app
                                  `diam
                                  [(Term.typeAscription "(" `univ ":" [(Term.app `Set [`X])] ")")])
                                 "+"
                                 (num "1"))
                                "+"
                                (Term.app
                                 `diam
                                 [(Term.typeAscription
                                   "("
                                   `univ
                                   ":"
                                   [(Term.app `Set [`Y])]
                                   ")")])))))]
                           ":="
                           (Term.byTactic
                            "by"
                            (Tactic.tacticSeq
                             (Tactic.tacticSeq1Indented
                              [(Tactic.rwSeq
                                "rw"
                                []
                                (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Ψrange)] "]")
                                [])
                               []
                               (Tactic.tacticHave_
                                "have"
                                (Term.haveDecl
                                 (Term.haveIdDecl
                                  []
                                  [(Term.typeSpec
                                    ":"
                                    («term_∈_» (Term.app `Φ [`xX]) "∈" (coeNotation "↑" `p)))]
                                  ":="
                                  (Term.app
                                   `Φrange.subst
                                   [(Term.app `mem_range_self [(Term.hole "_")])]))))
                               []
                               (Tactic.exact
                                "exact"
                                (Term.app
                                 `exists_dist_lt_of_Hausdorff_dist_lt
                                 [`this
                                  `bound
                                  (Term.app
                                   `Hausdorff_edist_ne_top_of_nonempty_of_bounded
                                   [`p.nonempty
                                    `q.nonempty
                                    `p.is_compact.bounded
                                    `q.is_compact.bounded])]))]))))))
                        []
                        (Std.Tactic.rcases
                         "rcases"
                         [(Tactic.casesTarget [] `this)]
                         ["with"
                          (Std.Tactic.RCases.rcasesPatLo
                           (Std.Tactic.RCases.rcasesPatMed
                            [(Std.Tactic.RCases.rcasesPat.tuple
                              "⟨"
                              [(Std.Tactic.RCases.rcasesPatLo
                                (Std.Tactic.RCases.rcasesPatMed
                                 [(Std.Tactic.RCases.rcasesPat.one `y)])
                                [])
                               ","
                               (Std.Tactic.RCases.rcasesPatLo
                                (Std.Tactic.RCases.rcasesPatMed
                                 [(Std.Tactic.RCases.rcasesPat.one `hy)])
                                [])
                               ","
                               (Std.Tactic.RCases.rcasesPatLo
                                (Std.Tactic.RCases.rcasesPatMed
                                 [(Std.Tactic.RCases.rcasesPat.one `dy)])
                                [])]
                              "⟩")])
                           [])])
                        []
                        (Std.Tactic.rcases
                         "rcases"
                         [(Tactic.casesTarget
                           []
                           (Term.app (Term.proj `mem_range "." (fieldIdx "1")) [`hy]))]
                         ["with"
                          (Std.Tactic.RCases.rcasesPatLo
                           (Std.Tactic.RCases.rcasesPatMed
                            [(Std.Tactic.RCases.rcasesPat.tuple
                              "⟨"
                              [(Std.Tactic.RCases.rcasesPatLo
                                (Std.Tactic.RCases.rcasesPatMed
                                 [(Std.Tactic.RCases.rcasesPat.one `z)])
                                [])
                               ","
                               (Std.Tactic.RCases.rcasesPatLo
                                (Std.Tactic.RCases.rcasesPatMed
                                 [(Std.Tactic.RCases.rcasesPat.one `hzy)])
                                [])]
                              "⟩")])
                           [])])
                        []
                        (Tactic.rwSeq
                         "rw"
                         []
                         (Tactic.rwRuleSeq
                          "["
                          [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `hzy)]
                          "]")
                         [(Tactic.location "at" (Tactic.locationHyp [`dy] []))])
                        []
                        (Tactic.tacticHave_
                         "have"
                         (Term.haveDecl
                          (Term.haveIdDecl
                           [`DΦ []]
                           [(Term.typeSpec
                             ":"
                             («term_=_»
                              (Term.app `diam [(Term.app `range [`Φ])])
                              "="
                              (Term.app
                               `diam
                               [(Term.typeAscription "(" `univ ":" [(Term.app `Set [`X])] ")")])))]
                           ":="
                           `Φisom.diam_range)))
                        []
                        (Tactic.tacticHave_
                         "have"
                         (Term.haveDecl
                          (Term.haveIdDecl
                           [`DΨ []]
                           [(Term.typeSpec
                             ":"
                             («term_=_»
                              (Term.app `diam [(Term.app `range [`Ψ])])
                              "="
                              (Term.app
                               `diam
                               [(Term.typeAscription "(" `univ ":" [(Term.app `Set [`Y])] ")")])))]
                           ":="
                           `Ψisom.diam_range)))
                        []
                        (calcTactic
                         "calc"
                         (calcStep
                          («term_≤_»
                           (Term.app
                            `diam
                            [(«term_∪_» (Term.app `range [`Φ]) "∪" (Term.app `range [`Ψ]))])
                           "≤"
                           («term_+_»
                            («term_+_»
                             (Term.app `diam [(Term.app `range [`Φ])])
                             "+"
                             (Term.app `dist [(Term.app `Φ [`xX]) (Term.app `Ψ [`z])]))
                            "+"
                            (Term.app `diam [(Term.app `range [`Ψ])])))
                          ":="
                          (Term.app
                           `diam_union
                           [(Term.app `mem_range_self [(Term.hole "_")])
                            (Term.app `mem_range_self [(Term.hole "_")])]))
                         [(calcStep
                           («term_≤_»
                            (Term.hole "_")
                            "≤"
                            («term_+_»
                             («term_+_»
                              (Term.app
                               `diam
                               [(Term.typeAscription "(" `univ ":" [(Term.app `Set [`X])] ")")])
                              "+"
                              («term_+_»
                               («term_+_»
                                (Term.app
                                 `diam
                                 [(Term.typeAscription "(" `univ ":" [(Term.app `Set [`X])] ")")])
                                "+"
                                (num "1"))
                               "+"
                               (Term.app
                                `diam
                                [(Term.typeAscription "(" `univ ":" [(Term.app `Set [`Y])] ")")])))
                             "+"
                             (Term.app
                              `diam
                              [(Term.typeAscription "(" `univ ":" [(Term.app `Set [`Y])] ")")])))
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
                                 [(Tactic.rwRule [] `DΦ) "," (Tactic.rwRule [] `DΨ)]
                                 "]")
                                [])
                               []
                               (Tactic.apply
                                "apply"
                                (Term.app
                                 `add_le_add
                                 [(Term.app `add_le_add [`le_rfl (Term.app `le_of_lt [`dy])])
                                  `le_rfl]))]))))
                          (calcStep
                           («term_=_»
                            (Term.hole "_")
                            "="
                            («term_+_»
                             («term_+_»
                              («term_*_»
                               (num "2")
                               "*"
                               (Term.app
                                `diam
                                [(Term.typeAscription "(" `univ ":" [(Term.app `Set [`X])] ")")]))
                              "+"
                              (num "1"))
                             "+"
                             («term_*_»
                              (num "2")
                              "*"
                              (Term.app
                               `diam
                               [(Term.typeAscription "(" `univ ":" [(Term.app `Set [`Y])] ")")]))))
                           ":="
                           (Term.byTactic
                            "by"
                            (Tactic.tacticSeq
                             (Tactic.tacticSeq1Indented
                              [(Mathlib.Tactic.RingNF.ring "ring")]))))])]))))))
                 []
                 (Tactic.tacticLet_
                  "let"
                  (Term.letDecl
                   (Term.letIdDecl
                    `f
                    []
                    [(Term.typeSpec
                      ":"
                      (Term.arrow
                       (Term.app `Sum [`X `Y])
                       "→"
                       (Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ "ℓ_infty_ℝ")))]
                    ":="
                    (Term.fun
                     "fun"
                     (Term.basicFun
                      [`x]
                      []
                      "=>"
                      (Term.match
                       "match"
                       []
                       []
                       [(Term.matchDiscr [] `x)]
                       "with"
                       (Term.matchAlts
                        [(Term.matchAlt "|" [[(Term.app `inl [`y])]] "=>" (Term.app `Φ [`y]))
                         (Term.matchAlt
                          "|"
                          [[(Term.app `inr [`z])]]
                          "=>"
                          (Term.app `Ψ [`z]))])))))))
                 []
                 (Tactic.tacticLet_
                  "let"
                  (Term.letDecl
                   (Term.letIdDecl
                    `F
                    []
                    [(Term.typeSpec
                      ":"
                      (Term.arrow
                       («term_×_» (Term.app `Sum [`X `Y]) "×" (Term.app `Sum [`X `Y]))
                       "→"
                       (Data.Real.Basic.termℝ "ℝ")))]
                    ":="
                    (Term.fun
                     "fun"
                     (Term.basicFun
                      [`p]
                      []
                      "=>"
                      (Term.app
                       `dist
                       [(Term.app `f [(Term.proj `p "." (fieldIdx "1"))])
                        (Term.app `f [(Term.proj `p "." (fieldIdx "2"))])]))))))
                 []
                 (Tactic.tacticHave_
                  "have"
                  (Term.haveDecl
                   (Term.haveIdDecl
                    [`Fgood []]
                    [(Term.typeSpec ":" («term_∈_» `F "∈" (Term.app `candidates [`X `Y])))]
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
                          [(Tactic.simpLemma [] [] `candidates)
                           ","
                           (Tactic.simpLemma [] [] `forall_const)
                           ","
                           (Tactic.simpLemma [] [] `and_true_iff)
                           ","
                           (Tactic.simpLemma [] [] `add_comm)
                           ","
                           (Tactic.simpLemma [] [] `eq_self_iff_true)
                           ","
                           (Tactic.simpLemma [] [] `dist_eq_zero)
                           ","
                           (Tactic.simpLemma [] [] `and_self_iff)
                           ","
                           (Tactic.simpLemma [] [] `Set.mem_setOf_eq)]
                          "]"]
                         [])
                        []
                        (Std.Tactic.tacticRepeat'_
                         "repeat'"
                         (Tactic.tacticSeq
                          (Tactic.tacticSeq1Indented [(Tactic.constructor "constructor")])))
                        []
                        (tactic__
                         (cdotTk (patternIgnore (token.«· » "·")))
                         [(Tactic.exact
                           "exact"
                           (Term.fun
                            "fun"
                            (Term.basicFun
                             [`x `y]
                             []
                             "=>"
                             (calc
                              "calc"
                              (calcStep
                               («term_=_»
                                (Term.app
                                 `F
                                 [(Term.tuple
                                   "("
                                   [(Term.app `inl [`x]) "," [(Term.app `inl [`y])]]
                                   ")")])
                                "="
                                (Term.app `dist [(Term.app `Φ [`x]) (Term.app `Φ [`y])]))
                               ":="
                               `rfl)
                              [(calcStep
                                («term_=_» (Term.hole "_") "=" (Term.app `dist [`x `y]))
                                ":="
                                (Term.app `Φisom.dist_eq [`x `y]))]))))])
                        []
                        (tactic__
                         (cdotTk (patternIgnore (token.«· » "·")))
                         [(Tactic.exact
                           "exact"
                           (Term.fun
                            "fun"
                            (Term.basicFun
                             [`x `y]
                             []
                             "=>"
                             (calc
                              "calc"
                              (calcStep
                               («term_=_»
                                (Term.app
                                 `F
                                 [(Term.tuple
                                   "("
                                   [(Term.app `inr [`x]) "," [(Term.app `inr [`y])]]
                                   ")")])
                                "="
                                (Term.app `dist [(Term.app `Ψ [`x]) (Term.app `Ψ [`y])]))
                               ":="
                               `rfl)
                              [(calcStep
                                («term_=_» (Term.hole "_") "=" (Term.app `dist [`x `y]))
                                ":="
                                (Term.app `Ψisom.dist_eq [`x `y]))]))))])
                        []
                        (tactic__
                         (cdotTk (patternIgnore (token.«· » "·")))
                         [(Tactic.exact
                           "exact"
                           (Term.fun
                            "fun"
                            (Term.basicFun
                             [`x `y]
                             []
                             "=>"
                             (Term.app `dist_comm [(Term.hole "_") (Term.hole "_")]))))])
                        []
                        (tactic__
                         (cdotTk (patternIgnore (token.«· » "·")))
                         [(Tactic.exact
                           "exact"
                           (Term.fun
                            "fun"
                            (Term.basicFun
                             [`x `y `z]
                             []
                             "=>"
                             (Term.app
                              `dist_triangle
                              [(Term.hole "_") (Term.hole "_") (Term.hole "_")]))))])
                        []
                        (tactic__
                         (cdotTk (patternIgnore (token.«· » "·")))
                         [(Tactic.exact
                           "exact"
                           (Term.fun
                            "fun"
                            (Term.basicFun
                             [`x `y]
                             []
                             "=>"
                             (calc
                              "calc"
                              (calcStep
                               («term_≤_»
                                (Term.app `F [(Term.tuple "(" [`x "," [`y]] ")")])
                                "≤"
                                (Term.app
                                 `diam
                                 [(«term_∪_» (Term.app `range [`Φ]) "∪" (Term.app `range [`Ψ]))]))
                               ":="
                               (Term.byTactic
                                "by"
                                (Tactic.tacticSeq
                                 (Tactic.tacticSeq1Indented
                                  [(Tactic.tacticHave_
                                    "have"
                                    (Term.haveDecl
                                     (Term.haveIdDecl
                                      [`A []]
                                      [(Term.typeSpec
                                        ":"
                                        (Term.forall
                                         "∀"
                                         [`z]
                                         [(Term.typeSpec ":" (Term.app `Sum [`X `Y]))]
                                         ","
                                         («term_∈_»
                                          (Term.app `f [`z])
                                          "∈"
                                          («term_∪_»
                                           (Term.app `range [`Φ])
                                           "∪"
                                           (Term.app `range [`Ψ])))))]
                                      ":="
                                      (Term.byTactic
                                       "by"
                                       (Tactic.tacticSeq
                                        (Tactic.tacticSeq1Indented
                                         [(Tactic.intro "intro" [`z])
                                          []
                                          (Tactic.cases "cases" [(Tactic.casesTarget [] `z)] [] [])
                                          []
                                          (tactic__
                                           (cdotTk (patternIgnore (token.«· » "·")))
                                           [(Tactic.apply "apply" `mem_union_left)
                                            []
                                            (Tactic.apply "apply" `mem_range_self)])
                                          []
                                          (tactic__
                                           (cdotTk (patternIgnore (token.«· » "·")))
                                           [(Tactic.apply "apply" `mem_union_right)
                                            []
                                            (Tactic.apply "apply" `mem_range_self)])]))))))
                                   []
                                   (Tactic.refine'
                                    "refine'"
                                    (Term.app
                                     `dist_le_diam_of_mem
                                     [(Term.hole "_")
                                      (Term.app `A [(Term.hole "_")])
                                      (Term.app `A [(Term.hole "_")])]))
                                   []
                                   (Tactic.rwSeq
                                    "rw"
                                    []
                                    (Tactic.rwRuleSeq
                                     "["
                                     [(Tactic.rwRule [] `Φrange) "," (Tactic.rwRule [] `Ψrange)]
                                     "]")
                                    [])
                                   []
                                   (Tactic.exact
                                    "exact"
                                    (Term.proj
                                     (Term.proj (Order.Basic.«term_⊔_» `p " ⊔ " `q) "." `IsCompact)
                                     "."
                                     `Bounded))]))))
                              [(calcStep
                                («term_≤_»
                                 (Term.hole "_")
                                 "≤"
                                 («term_+_»
                                  («term_+_»
                                   («term_*_»
                                    (num "2")
                                    "*"
                                    (Term.app
                                     `diam
                                     [(Term.typeAscription
                                       "("
                                       `univ
                                       ":"
                                       [(Term.app `Set [`X])]
                                       ")")]))
                                   "+"
                                   (num "1"))
                                  "+"
                                  («term_*_»
                                   (num "2")
                                   "*"
                                   (Term.app
                                    `diam
                                    [(Term.typeAscription
                                      "("
                                      `univ
                                      ":"
                                      [(Term.app `Set [`Y])]
                                      ")")]))))
                                ":="
                                `I)]))))])]))))))
                 []
                 (Tactic.tacticLet_
                  "let"
                  (Term.letDecl
                   (Term.letIdDecl
                    `Fb
                    []
                    []
                    ":="
                    (Term.app `candidates_b_of_candidates [`F `Fgood]))))
                 []
                 (Tactic.tacticHave_
                  "have"
                  (Term.haveDecl
                   (Term.haveIdDecl
                    []
                    [(Term.typeSpec
                      ":"
                      («term_≤_»
                       (Term.app
                        `Hausdorff_dist
                        [(Term.app `range [(Term.app `optimal_GH_injl [`X `Y])])
                         (Term.app `range [(Term.app `optimal_GH_injr [`X `Y])])])
                       "≤"
                       (Term.app `HD [`Fb])))]
                    ":="
                    (Term.app
                     `Hausdorff_dist_optimal_le_HD
                     [(Term.hole "_")
                      (Term.hole "_")
                      (Term.app `candidates_b_of_candidates_mem [`F `Fgood])]))))
                 []
                 (Tactic.refine'
                  "refine'"
                  (Term.app
                   `le_trans
                   [`this
                    (Term.app
                     `le_of_forall_le_of_dense
                     [(Term.fun "fun" (Term.basicFun [`r `hr] [] "=>" (Term.hole "_")))])]))
                 []
                 (Tactic.tacticHave_
                  "have"
                  (Term.haveDecl
                   (Term.haveIdDecl
                    [`I1 []]
                    [(Term.typeSpec
                      ":"
                      (Term.forall
                       "∀"
                       [`x]
                       [(Term.typeSpec ":" `X)]
                       ","
                       («term_≤_»
                        (Order.CompleteLattice.«term⨅_,_»
                         "⨅"
                         (Std.ExtendedBinder.extBinders
                          (Std.ExtendedBinder.extBinder (Lean.binderIdent `y) []))
                         ", "
                         (Term.app
                          `Fb
                          [(Term.tuple "(" [(Term.app `inl [`x]) "," [(Term.app `inr [`y])]] ")")]))
                        "≤"
                        `r)))]
                    ":="
                    (Term.byTactic
                     "by"
                     (Tactic.tacticSeq
                      (Tactic.tacticSeq1Indented
                       [(Tactic.intro "intro" [`x])
                        []
                        (Tactic.tacticHave_
                         "have"
                         (Term.haveDecl
                          (Term.haveIdDecl
                           []
                           [(Term.typeSpec
                             ":"
                             («term_∈_»
                              (Term.app `f [(Term.app `inl [`x])])
                              "∈"
                              (coeNotation "↑" `p)))]
                           ":="
                           (Term.app
                            `Φrange.subst
                            [(Term.app `mem_range_self [(Term.hole "_")])]))))
                        []
                        (Std.Tactic.rcases
                         "rcases"
                         [(Tactic.casesTarget
                           []
                           (Term.app
                            `exists_dist_lt_of_Hausdorff_dist_lt
                            [`this
                             `hr
                             (Term.app
                              `Hausdorff_edist_ne_top_of_nonempty_of_bounded
                              [`p.nonempty
                               `q.nonempty
                               `p.is_compact.bounded
                               `q.is_compact.bounded])]))]
                         ["with"
                          (Std.Tactic.RCases.rcasesPatLo
                           (Std.Tactic.RCases.rcasesPatMed
                            [(Std.Tactic.RCases.rcasesPat.tuple
                              "⟨"
                              [(Std.Tactic.RCases.rcasesPatLo
                                (Std.Tactic.RCases.rcasesPatMed
                                 [(Std.Tactic.RCases.rcasesPat.one `z)])
                                [])
                               ","
                               (Std.Tactic.RCases.rcasesPatLo
                                (Std.Tactic.RCases.rcasesPatMed
                                 [(Std.Tactic.RCases.rcasesPat.one `zq)])
                                [])
                               ","
                               (Std.Tactic.RCases.rcasesPatLo
                                (Std.Tactic.RCases.rcasesPatMed
                                 [(Std.Tactic.RCases.rcasesPat.one `hz)])
                                [])]
                              "⟩")])
                           [])])
                        []
                        (Tactic.tacticHave_
                         "have"
                         (Term.haveDecl
                          (Term.haveIdDecl
                           []
                           [(Term.typeSpec ":" («term_∈_» `z "∈" (Term.app `range [`Ψ])))]
                           ":="
                           (Term.byTactic
                            "by"
                            (Tactic.tacticSeq
                             (Tactic.tacticSeq1Indented
                              [(Std.Tactic.tacticRwa__
                                "rwa"
                                (Tactic.rwRuleSeq
                                 "["
                                 [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Ψrange)]
                                 "]")
                                [(Tactic.location "at" (Tactic.locationHyp [`zq] []))])]))))))
                        []
                        (Std.Tactic.rcases
                         "rcases"
                         [(Tactic.casesTarget
                           []
                           (Term.app (Term.proj `mem_range "." (fieldIdx "1")) [`this]))]
                         ["with"
                          (Std.Tactic.RCases.rcasesPatLo
                           (Std.Tactic.RCases.rcasesPatMed
                            [(Std.Tactic.RCases.rcasesPat.tuple
                              "⟨"
                              [(Std.Tactic.RCases.rcasesPatLo
                                (Std.Tactic.RCases.rcasesPatMed
                                 [(Std.Tactic.RCases.rcasesPat.one `y)])
                                [])
                               ","
                               (Std.Tactic.RCases.rcasesPatLo
                                (Std.Tactic.RCases.rcasesPatMed
                                 [(Std.Tactic.RCases.rcasesPat.one `hy)])
                                [])]
                              "⟩")])
                           [])])
                        []
                        (calcTactic
                         "calc"
                         (calcStep
                          («term_≤_»
                           (Order.CompleteLattice.«term⨅_,_»
                            "⨅"
                            (Std.ExtendedBinder.extBinders
                             (Std.ExtendedBinder.extBinder (Lean.binderIdent `y) []))
                            ", "
                            (Term.app
                             `Fb
                             [(Term.tuple
                               "("
                               [(Term.app `inl [`x]) "," [(Term.app `inr [`y])]]
                               ")")]))
                           "≤"
                           (Term.app
                            `Fb
                            [(Term.tuple
                              "("
                              [(Term.app `inl [`x]) "," [(Term.app `inr [`y])]]
                              ")")]))
                          ":="
                          (Term.app
                           `cinfᵢ_le
                           [(Term.byTactic
                             "by"
                             (Tactic.tacticSeq
                              (Tactic.tacticSeq1Indented
                               [(Std.Tactic.Simpa.simpa
                                 "simpa"
                                 []
                                 []
                                 (Std.Tactic.Simpa.simpaArgsRest
                                  []
                                  []
                                  ["only"]
                                  [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `add_zero)] "]")]
                                  ["using" (Term.app `HD_below_aux1 [(num "0")])]))])))
                            `y]))
                         [(calcStep
                           («term_=_»
                            (Term.hole "_")
                            "="
                            (Term.app `dist [(Term.app `Φ [`x]) (Term.app `Ψ [`y])]))
                           ":="
                           `rfl)
                          (calcStep
                           («term_=_»
                            (Term.hole "_")
                            "="
                            (Term.app `dist [(Term.app `f [(Term.app `inl [`x])]) `z]))
                           ":="
                           (Term.byTactic
                            "by"
                            (Tactic.tacticSeq
                             (Tactic.tacticSeq1Indented
                              [(Tactic.rwSeq
                                "rw"
                                []
                                (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `hy)] "]")
                                [])]))))
                          (calcStep
                           («term_≤_» (Term.hole "_") "≤" `r)
                           ":="
                           (Term.app `le_of_lt [`hz]))])]))))))
                 []
                 (Tactic.tacticHave_
                  "have"
                  (Term.haveDecl
                   (Term.haveIdDecl
                    [`I2 []]
                    [(Term.typeSpec
                      ":"
                      (Term.forall
                       "∀"
                       [`y]
                       [(Term.typeSpec ":" `Y)]
                       ","
                       («term_≤_»
                        (Order.CompleteLattice.«term⨅_,_»
                         "⨅"
                         (Std.ExtendedBinder.extBinders
                          (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
                         ", "
                         (Term.app
                          `Fb
                          [(Term.tuple "(" [(Term.app `inl [`x]) "," [(Term.app `inr [`y])]] ")")]))
                        "≤"
                        `r)))]
                    ":="
                    (Term.byTactic
                     "by"
                     (Tactic.tacticSeq
                      (Tactic.tacticSeq1Indented
                       [(Tactic.intro "intro" [`y])
                        []
                        (Tactic.tacticHave_
                         "have"
                         (Term.haveDecl
                          (Term.haveIdDecl
                           []
                           [(Term.typeSpec
                             ":"
                             («term_∈_»
                              (Term.app `f [(Term.app `inr [`y])])
                              "∈"
                              (coeNotation "↑" `q)))]
                           ":="
                           (Term.app
                            `Ψrange.subst
                            [(Term.app `mem_range_self [(Term.hole "_")])]))))
                        []
                        (Std.Tactic.rcases
                         "rcases"
                         [(Tactic.casesTarget
                           []
                           (Term.app
                            `exists_dist_lt_of_Hausdorff_dist_lt'
                            [`this
                             `hr
                             (Term.app
                              `Hausdorff_edist_ne_top_of_nonempty_of_bounded
                              [`p.nonempty
                               `q.nonempty
                               `p.is_compact.bounded
                               `q.is_compact.bounded])]))]
                         ["with"
                          (Std.Tactic.RCases.rcasesPatLo
                           (Std.Tactic.RCases.rcasesPatMed
                            [(Std.Tactic.RCases.rcasesPat.tuple
                              "⟨"
                              [(Std.Tactic.RCases.rcasesPatLo
                                (Std.Tactic.RCases.rcasesPatMed
                                 [(Std.Tactic.RCases.rcasesPat.one `z)])
                                [])
                               ","
                               (Std.Tactic.RCases.rcasesPatLo
                                (Std.Tactic.RCases.rcasesPatMed
                                 [(Std.Tactic.RCases.rcasesPat.one `zq)])
                                [])
                               ","
                               (Std.Tactic.RCases.rcasesPatLo
                                (Std.Tactic.RCases.rcasesPatMed
                                 [(Std.Tactic.RCases.rcasesPat.one `hz)])
                                [])]
                              "⟩")])
                           [])])
                        []
                        (Tactic.tacticHave_
                         "have"
                         (Term.haveDecl
                          (Term.haveIdDecl
                           []
                           [(Term.typeSpec ":" («term_∈_» `z "∈" (Term.app `range [`Φ])))]
                           ":="
                           (Term.byTactic
                            "by"
                            (Tactic.tacticSeq
                             (Tactic.tacticSeq1Indented
                              [(Std.Tactic.tacticRwa__
                                "rwa"
                                (Tactic.rwRuleSeq
                                 "["
                                 [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Φrange)]
                                 "]")
                                [(Tactic.location "at" (Tactic.locationHyp [`zq] []))])]))))))
                        []
                        (Std.Tactic.rcases
                         "rcases"
                         [(Tactic.casesTarget
                           []
                           (Term.app (Term.proj `mem_range "." (fieldIdx "1")) [`this]))]
                         ["with"
                          (Std.Tactic.RCases.rcasesPatLo
                           (Std.Tactic.RCases.rcasesPatMed
                            [(Std.Tactic.RCases.rcasesPat.tuple
                              "⟨"
                              [(Std.Tactic.RCases.rcasesPatLo
                                (Std.Tactic.RCases.rcasesPatMed
                                 [(Std.Tactic.RCases.rcasesPat.one `x)])
                                [])
                               ","
                               (Std.Tactic.RCases.rcasesPatLo
                                (Std.Tactic.RCases.rcasesPatMed
                                 [(Std.Tactic.RCases.rcasesPat.one `hx)])
                                [])]
                              "⟩")])
                           [])])
                        []
                        (calcTactic
                         "calc"
                         (calcStep
                          («term_≤_»
                           (Order.CompleteLattice.«term⨅_,_»
                            "⨅"
                            (Std.ExtendedBinder.extBinders
                             (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
                            ", "
                            (Term.app
                             `Fb
                             [(Term.tuple
                               "("
                               [(Term.app `inl [`x]) "," [(Term.app `inr [`y])]]
                               ")")]))
                           "≤"
                           (Term.app
                            `Fb
                            [(Term.tuple
                              "("
                              [(Term.app `inl [`x]) "," [(Term.app `inr [`y])]]
                              ")")]))
                          ":="
                          (Term.app
                           `cinfᵢ_le
                           [(Term.byTactic
                             "by"
                             (Tactic.tacticSeq
                              (Tactic.tacticSeq1Indented
                               [(Std.Tactic.Simpa.simpa
                                 "simpa"
                                 []
                                 []
                                 (Std.Tactic.Simpa.simpaArgsRest
                                  []
                                  []
                                  ["only"]
                                  [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `add_zero)] "]")]
                                  ["using" (Term.app `HD_below_aux2 [(num "0")])]))])))
                            `x]))
                         [(calcStep
                           («term_=_»
                            (Term.hole "_")
                            "="
                            (Term.app `dist [(Term.app `Φ [`x]) (Term.app `Ψ [`y])]))
                           ":="
                           `rfl)
                          (calcStep
                           («term_=_»
                            (Term.hole "_")
                            "="
                            (Term.app `dist [`z (Term.app `f [(Term.app `inr [`y])])]))
                           ":="
                           (Term.byTactic
                            "by"
                            (Tactic.tacticSeq
                             (Tactic.tacticSeq1Indented
                              [(Tactic.rwSeq
                                "rw"
                                []
                                (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `hx)] "]")
                                [])]))))
                          (calcStep
                           («term_≤_» (Term.hole "_") "≤" `r)
                           ":="
                           (Term.app `le_of_lt [`hz]))])]))))))
                 []
                 (Tactic.simp
                  "simp"
                  []
                  []
                  ["only"]
                  ["["
                   [(Tactic.simpLemma [] [] `HD)
                    ","
                    (Tactic.simpLemma [] [] (Term.app `csupᵢ_le [`I1]))
                    ","
                    (Tactic.simpLemma [] [] (Term.app `csupᵢ_le [`I2]))
                    ","
                    (Tactic.simpLemma [] [] `max_le_iff)
                    ","
                    (Tactic.simpLemma [] [] `and_self_iff)]
                   "]"]
                  [])]))))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`B []]
             [(Term.typeSpec
               ":"
               (Term.forall
                "∀"
                [`p `q]
                [(Term.typeSpec
                  ":"
                  (Term.app
                   `nonempty_compacts
                   [(Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ "ℓ_infty_ℝ")]))]
                ","
                (Term.arrow
                 («term_=_»
                  (Quotient.Init.Data.Quot.«term⟦_⟧» "⟦" `p "⟧")
                  "="
                  (Term.app `to_GH_space [`X]))
                 "→"
                 (Term.arrow
                  («term_=_»
                   (Quotient.Init.Data.Quot.«term⟦_⟧» "⟦" `q "⟧")
                   "="
                   (Term.app `to_GH_space [`Y]))
                  "→"
                  («term_≤_»
                   (Term.app
                    `Hausdorff_dist
                    [(Term.app `range [(Term.app `optimal_GH_injl [`X `Y])])
                     (Term.app `range [(Term.app `optimal_GH_injr [`X `Y])])])
                   "≤"
                   (Term.app
                    `Hausdorff_dist
                    [(Term.typeAscription
                      "("
                      `p
                      ":"
                      [(Term.app
                        `Set
                        [(Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ "ℓ_infty_ℝ")])]
                      ")")
                     `q]))))))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.intro "intro" [`p `q `hp `hq])
                 []
                 (Classical.«tacticBy_cases_:_»
                  "by_cases"
                  [`h ":"]
                  («term_<_»
                   (Term.app
                    `Hausdorff_dist
                    [(Term.typeAscription
                      "("
                      `p
                      ":"
                      [(Term.app
                        `Set
                        [(Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ "ℓ_infty_ℝ")])]
                      ")")
                     `q])
                   "<"
                   («term_+_»
                    («term_+_»
                     (Term.app
                      `diam
                      [(Term.typeAscription "(" `univ ":" [(Term.app `Set [`X])] ")")])
                     "+"
                     (num "1"))
                    "+"
                    (Term.app
                     `diam
                     [(Term.typeAscription "(" `univ ":" [(Term.app `Set [`Y])] ")")]))))
                 []
                 (tactic__
                  (cdotTk (patternIgnore (token.«· » "·")))
                  [(Tactic.exact "exact" (Term.app `A [`p `q `hp `hq `h]))])
                 []
                 (tactic__
                  (cdotTk (patternIgnore (token.«· » "·")))
                  [(calcTactic
                    "calc"
                    (calcStep
                     («term_≤_»
                      (Term.app
                       `Hausdorff_dist
                       [(Term.app `range [(Term.app `optimal_GH_injl [`X `Y])])
                        (Term.app `range [(Term.app `optimal_GH_injr [`X `Y])])])
                      "≤"
                      (Term.app `HD [(Term.app `candidates_b_dist [`X `Y])]))
                     ":="
                     (Term.app
                      `Hausdorff_dist_optimal_le_HD
                      [(Term.hole "_") (Term.hole "_") `candidates_b_dist_mem_candidates_b]))
                    [(calcStep
                      («term_≤_»
                       (Term.hole "_")
                       "≤"
                       («term_+_»
                        («term_+_»
                         (Term.app
                          `diam
                          [(Term.typeAscription "(" `univ ":" [(Term.app `Set [`X])] ")")])
                         "+"
                         (num "1"))
                        "+"
                        (Term.app
                         `diam
                         [(Term.typeAscription "(" `univ ":" [(Term.app `Set [`Y])] ")")])))
                      ":="
                      `HD_candidates_b_dist_le)
                     (calcStep
                      («term_≤_»
                       (Term.hole "_")
                       "≤"
                       (Term.app
                        `Hausdorff_dist
                        [(Term.typeAscription
                          "("
                          `p
                          ":"
                          [(Term.app
                            `Set
                            [(Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ "ℓ_infty_ℝ")])]
                          ")")
                         `q]))
                      ":="
                      (Term.app (Term.proj `not_lt "." (fieldIdx "1")) [`h]))])])]))))))
          []
          (Tactic.refine' "refine'" (Term.app `le_antisymm [(Term.hole "_") (Term.hole "_")]))
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.apply "apply" `le_cinfₛ)
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(Tactic.«tactic_<;>_»
               (Tactic.refine'
                "refine'"
                (Term.app
                 (Term.proj
                  (Term.app `Set.Nonempty.prod [(Term.hole "_") (Term.hole "_")])
                  "."
                  `image)
                 [(Term.hole "_")]))
               "<;>"
               (Tactic.exact "exact" (Term.anonymousCtor "⟨" [(Term.hole "_") "," `rfl] "⟩")))])
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(Std.Tactic.rintro
               "rintro"
               [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `b))
                (Std.Tactic.RCases.rintroPat.one
                 (Std.Tactic.RCases.rcasesPat.tuple
                  "⟨"
                  [(Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed
                     [(Std.Tactic.RCases.rcasesPat.tuple
                       "⟨"
                       [(Std.Tactic.RCases.rcasesPatLo
                         (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `p)])
                         [])
                        ","
                        (Std.Tactic.RCases.rcasesPatLo
                         (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `q)])
                         [])]
                       "⟩")])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed
                     [(Std.Tactic.RCases.rcasesPat.tuple
                       "⟨"
                       [(Std.Tactic.RCases.rcasesPatLo
                         (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hp)])
                         [])
                        ","
                        (Std.Tactic.RCases.rcasesPatLo
                         (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hq)])
                         [])]
                       "⟩")])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                    [])]
                  "⟩"))]
               [])
              []
              (Tactic.exact "exact" (Term.app `B [`p `q `hp `hq]))])])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.exact
             "exact"
             (Term.app
              `GH_dist_le_Hausdorff_dist
              [(Term.app `isometry_optimal_GH_injl [`X `Y])
               (Term.app `isometry_optimal_GH_injr [`X `Y])]))])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.exact
         "exact"
         (Term.app
          `GH_dist_le_Hausdorff_dist
          [(Term.app `isometry_optimal_GH_injl [`X `Y])
           (Term.app `isometry_optimal_GH_injr [`X `Y])]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.app
        `GH_dist_le_Hausdorff_dist
        [(Term.app `isometry_optimal_GH_injl [`X `Y])
         (Term.app `isometry_optimal_GH_injr [`X `Y])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `GH_dist_le_Hausdorff_dist
       [(Term.app `isometry_optimal_GH_injl [`X `Y]) (Term.app `isometry_optimal_GH_injr [`X `Y])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `isometry_optimal_GH_injr [`X `Y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `X
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `isometry_optimal_GH_injr
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `isometry_optimal_GH_injr [`X `Y])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `isometry_optimal_GH_injl [`X `Y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `X
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `isometry_optimal_GH_injl
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `isometry_optimal_GH_injl [`X `Y])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `GH_dist_le_Hausdorff_dist
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.apply "apply" `le_cinfₛ)
        []
        (tactic__
         (cdotTk (patternIgnore (token.«· » "·")))
         [(Tactic.«tactic_<;>_»
           (Tactic.refine'
            "refine'"
            (Term.app
             (Term.proj (Term.app `Set.Nonempty.prod [(Term.hole "_") (Term.hole "_")]) "." `image)
             [(Term.hole "_")]))
           "<;>"
           (Tactic.exact "exact" (Term.anonymousCtor "⟨" [(Term.hole "_") "," `rfl] "⟩")))])
        []
        (tactic__
         (cdotTk (patternIgnore (token.«· » "·")))
         [(Std.Tactic.rintro
           "rintro"
           [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `b))
            (Std.Tactic.RCases.rintroPat.one
             (Std.Tactic.RCases.rcasesPat.tuple
              "⟨"
              [(Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed
                 [(Std.Tactic.RCases.rcasesPat.tuple
                   "⟨"
                   [(Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `p)])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `q)])
                     [])]
                   "⟩")])
                [])
               ","
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed
                 [(Std.Tactic.RCases.rcasesPat.tuple
                   "⟨"
                   [(Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hp)])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hq)])
                     [])]
                   "⟩")])
                [])
               ","
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                [])]
              "⟩"))]
           [])
          []
          (Tactic.exact "exact" (Term.app `B [`p `q `hp `hq]))])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Std.Tactic.rintro
         "rintro"
         [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `b))
          (Std.Tactic.RCases.rintroPat.one
           (Std.Tactic.RCases.rcasesPat.tuple
            "⟨"
            [(Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed
               [(Std.Tactic.RCases.rcasesPat.tuple
                 "⟨"
                 [(Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `p)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `q)])
                   [])]
                 "⟩")])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed
               [(Std.Tactic.RCases.rcasesPat.tuple
                 "⟨"
                 [(Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hp)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hq)])
                   [])]
                 "⟩")])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
              [])]
            "⟩"))]
         [])
        []
        (Tactic.exact "exact" (Term.app `B [`p `q `hp `hq]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" (Term.app `B [`p `q `hp `hq]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `B [`p `q `hp `hq])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hq
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hp
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `q
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `B
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.rintro
       "rintro"
       [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `b))
        (Std.Tactic.RCases.rintroPat.one
         (Std.Tactic.RCases.rcasesPat.tuple
          "⟨"
          [(Std.Tactic.RCases.rcasesPatLo
            (Std.Tactic.RCases.rcasesPatMed
             [(Std.Tactic.RCases.rcasesPat.tuple
               "⟨"
               [(Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `p)])
                 [])
                ","
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `q)])
                 [])]
               "⟩")])
            [])
           ","
           (Std.Tactic.RCases.rcasesPatLo
            (Std.Tactic.RCases.rcasesPatMed
             [(Std.Tactic.RCases.rcasesPat.tuple
               "⟨"
               [(Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hp)])
                 [])
                ","
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hq)])
                 [])]
               "⟩")])
            [])
           ","
           (Std.Tactic.RCases.rcasesPatLo
            (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
            [])]
          "⟩"))]
       [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.«tactic_<;>_»
         (Tactic.refine'
          "refine'"
          (Term.app
           (Term.proj (Term.app `Set.Nonempty.prod [(Term.hole "_") (Term.hole "_")]) "." `image)
           [(Term.hole "_")]))
         "<;>"
         (Tactic.exact "exact" (Term.anonymousCtor "⟨" [(Term.hole "_") "," `rfl] "⟩")))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.«tactic_<;>_»
       (Tactic.refine'
        "refine'"
        (Term.app
         (Term.proj (Term.app `Set.Nonempty.prod [(Term.hole "_") (Term.hole "_")]) "." `image)
         [(Term.hole "_")]))
       "<;>"
       (Tactic.exact "exact" (Term.anonymousCtor "⟨" [(Term.hole "_") "," `rfl] "⟩")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" (Term.anonymousCtor "⟨" [(Term.hole "_") "," `rfl] "⟩"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [(Term.hole "_") "," `rfl] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rfl
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 2 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
      (Tactic.refine'
       "refine'"
       (Term.app
        (Term.proj (Term.app `Set.Nonempty.prod [(Term.hole "_") (Term.hole "_")]) "." `image)
        [(Term.hole "_")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj (Term.app `Set.Nonempty.prod [(Term.hole "_") (Term.hole "_")]) "." `image)
       [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app `Set.Nonempty.prod [(Term.hole "_") (Term.hole "_")]) "." `image)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `Set.Nonempty.prod [(Term.hole "_") (Term.hole "_")])
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
      `Set.Nonempty.prod
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `Set.Nonempty.prod [(Term.hole "_") (Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.apply "apply" `le_cinfₛ)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `le_cinfₛ
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine' "refine'" (Term.app `le_antisymm [(Term.hole "_") (Term.hole "_")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `le_antisymm [(Term.hole "_") (Term.hole "_")])
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
      `le_antisymm
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`B []]
         [(Term.typeSpec
           ":"
           (Term.forall
            "∀"
            [`p `q]
            [(Term.typeSpec
              ":"
              (Term.app
               `nonempty_compacts
               [(Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ "ℓ_infty_ℝ")]))]
            ","
            (Term.arrow
             («term_=_»
              (Quotient.Init.Data.Quot.«term⟦_⟧» "⟦" `p "⟧")
              "="
              (Term.app `to_GH_space [`X]))
             "→"
             (Term.arrow
              («term_=_»
               (Quotient.Init.Data.Quot.«term⟦_⟧» "⟦" `q "⟧")
               "="
               (Term.app `to_GH_space [`Y]))
              "→"
              («term_≤_»
               (Term.app
                `Hausdorff_dist
                [(Term.app `range [(Term.app `optimal_GH_injl [`X `Y])])
                 (Term.app `range [(Term.app `optimal_GH_injr [`X `Y])])])
               "≤"
               (Term.app
                `Hausdorff_dist
                [(Term.typeAscription
                  "("
                  `p
                  ":"
                  [(Term.app
                    `Set
                    [(Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ "ℓ_infty_ℝ")])]
                  ")")
                 `q]))))))]
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.intro "intro" [`p `q `hp `hq])
             []
             (Classical.«tacticBy_cases_:_»
              "by_cases"
              [`h ":"]
              («term_<_»
               (Term.app
                `Hausdorff_dist
                [(Term.typeAscription
                  "("
                  `p
                  ":"
                  [(Term.app
                    `Set
                    [(Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ "ℓ_infty_ℝ")])]
                  ")")
                 `q])
               "<"
               («term_+_»
                («term_+_»
                 (Term.app `diam [(Term.typeAscription "(" `univ ":" [(Term.app `Set [`X])] ")")])
                 "+"
                 (num "1"))
                "+"
                (Term.app `diam [(Term.typeAscription "(" `univ ":" [(Term.app `Set [`Y])] ")")]))))
             []
             (tactic__
              (cdotTk (patternIgnore (token.«· » "·")))
              [(Tactic.exact "exact" (Term.app `A [`p `q `hp `hq `h]))])
             []
             (tactic__
              (cdotTk (patternIgnore (token.«· » "·")))
              [(calcTactic
                "calc"
                (calcStep
                 («term_≤_»
                  (Term.app
                   `Hausdorff_dist
                   [(Term.app `range [(Term.app `optimal_GH_injl [`X `Y])])
                    (Term.app `range [(Term.app `optimal_GH_injr [`X `Y])])])
                  "≤"
                  (Term.app `HD [(Term.app `candidates_b_dist [`X `Y])]))
                 ":="
                 (Term.app
                  `Hausdorff_dist_optimal_le_HD
                  [(Term.hole "_") (Term.hole "_") `candidates_b_dist_mem_candidates_b]))
                [(calcStep
                  («term_≤_»
                   (Term.hole "_")
                   "≤"
                   («term_+_»
                    («term_+_»
                     (Term.app
                      `diam
                      [(Term.typeAscription "(" `univ ":" [(Term.app `Set [`X])] ")")])
                     "+"
                     (num "1"))
                    "+"
                    (Term.app
                     `diam
                     [(Term.typeAscription "(" `univ ":" [(Term.app `Set [`Y])] ")")])))
                  ":="
                  `HD_candidates_b_dist_le)
                 (calcStep
                  («term_≤_»
                   (Term.hole "_")
                   "≤"
                   (Term.app
                    `Hausdorff_dist
                    [(Term.typeAscription
                      "("
                      `p
                      ":"
                      [(Term.app
                        `Set
                        [(Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ "ℓ_infty_ℝ")])]
                      ")")
                     `q]))
                  ":="
                  (Term.app (Term.proj `not_lt "." (fieldIdx "1")) [`h]))])])]))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.intro "intro" [`p `q `hp `hq])
          []
          (Classical.«tacticBy_cases_:_»
           "by_cases"
           [`h ":"]
           («term_<_»
            (Term.app
             `Hausdorff_dist
             [(Term.typeAscription
               "("
               `p
               ":"
               [(Term.app `Set [(Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ "ℓ_infty_ℝ")])]
               ")")
              `q])
            "<"
            («term_+_»
             («term_+_»
              (Term.app `diam [(Term.typeAscription "(" `univ ":" [(Term.app `Set [`X])] ")")])
              "+"
              (num "1"))
             "+"
             (Term.app `diam [(Term.typeAscription "(" `univ ":" [(Term.app `Set [`Y])] ")")]))))
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.exact "exact" (Term.app `A [`p `q `hp `hq `h]))])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(calcTactic
             "calc"
             (calcStep
              («term_≤_»
               (Term.app
                `Hausdorff_dist
                [(Term.app `range [(Term.app `optimal_GH_injl [`X `Y])])
                 (Term.app `range [(Term.app `optimal_GH_injr [`X `Y])])])
               "≤"
               (Term.app `HD [(Term.app `candidates_b_dist [`X `Y])]))
              ":="
              (Term.app
               `Hausdorff_dist_optimal_le_HD
               [(Term.hole "_") (Term.hole "_") `candidates_b_dist_mem_candidates_b]))
             [(calcStep
               («term_≤_»
                (Term.hole "_")
                "≤"
                («term_+_»
                 («term_+_»
                  (Term.app `diam [(Term.typeAscription "(" `univ ":" [(Term.app `Set [`X])] ")")])
                  "+"
                  (num "1"))
                 "+"
                 (Term.app `diam [(Term.typeAscription "(" `univ ":" [(Term.app `Set [`Y])] ")")])))
               ":="
               `HD_candidates_b_dist_le)
              (calcStep
               («term_≤_»
                (Term.hole "_")
                "≤"
                (Term.app
                 `Hausdorff_dist
                 [(Term.typeAscription
                   "("
                   `p
                   ":"
                   [(Term.app
                     `Set
                     [(Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ "ℓ_infty_ℝ")])]
                   ")")
                  `q]))
               ":="
               (Term.app (Term.proj `not_lt "." (fieldIdx "1")) [`h]))])])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(calcTactic
         "calc"
         (calcStep
          («term_≤_»
           (Term.app
            `Hausdorff_dist
            [(Term.app `range [(Term.app `optimal_GH_injl [`X `Y])])
             (Term.app `range [(Term.app `optimal_GH_injr [`X `Y])])])
           "≤"
           (Term.app `HD [(Term.app `candidates_b_dist [`X `Y])]))
          ":="
          (Term.app
           `Hausdorff_dist_optimal_le_HD
           [(Term.hole "_") (Term.hole "_") `candidates_b_dist_mem_candidates_b]))
         [(calcStep
           («term_≤_»
            (Term.hole "_")
            "≤"
            («term_+_»
             («term_+_»
              (Term.app `diam [(Term.typeAscription "(" `univ ":" [(Term.app `Set [`X])] ")")])
              "+"
              (num "1"))
             "+"
             (Term.app `diam [(Term.typeAscription "(" `univ ":" [(Term.app `Set [`Y])] ")")])))
           ":="
           `HD_candidates_b_dist_le)
          (calcStep
           («term_≤_»
            (Term.hole "_")
            "≤"
            (Term.app
             `Hausdorff_dist
             [(Term.typeAscription
               "("
               `p
               ":"
               [(Term.app `Set [(Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ "ℓ_infty_ℝ")])]
               ")")
              `q]))
           ":="
           (Term.app (Term.proj `not_lt "." (fieldIdx "1")) [`h]))])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (calcTactic
       "calc"
       (calcStep
        («term_≤_»
         (Term.app
          `Hausdorff_dist
          [(Term.app `range [(Term.app `optimal_GH_injl [`X `Y])])
           (Term.app `range [(Term.app `optimal_GH_injr [`X `Y])])])
         "≤"
         (Term.app `HD [(Term.app `candidates_b_dist [`X `Y])]))
        ":="
        (Term.app
         `Hausdorff_dist_optimal_le_HD
         [(Term.hole "_") (Term.hole "_") `candidates_b_dist_mem_candidates_b]))
       [(calcStep
         («term_≤_»
          (Term.hole "_")
          "≤"
          («term_+_»
           («term_+_»
            (Term.app `diam [(Term.typeAscription "(" `univ ":" [(Term.app `Set [`X])] ")")])
            "+"
            (num "1"))
           "+"
           (Term.app `diam [(Term.typeAscription "(" `univ ":" [(Term.app `Set [`Y])] ")")])))
         ":="
         `HD_candidates_b_dist_le)
        (calcStep
         («term_≤_»
          (Term.hole "_")
          "≤"
          (Term.app
           `Hausdorff_dist
           [(Term.typeAscription
             "("
             `p
             ":"
             [(Term.app `Set [(Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ "ℓ_infty_ℝ")])]
             ")")
            `q]))
         ":="
         (Term.app (Term.proj `not_lt "." (fieldIdx "1")) [`h]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj `not_lt "." (fieldIdx "1")) [`h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `not_lt "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `not_lt
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≤_»
       (Term.hole "_")
       "≤"
       (Term.app
        `Hausdorff_dist
        [(Term.typeAscription
          "("
          `p
          ":"
          [(Term.app `Set [(Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ "ℓ_infty_ℝ")])]
          ")")
         `q]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Hausdorff_dist
       [(Term.typeAscription
         "("
         `p
         ":"
         [(Term.app `Set [(Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ "ℓ_infty_ℝ")])]
         ")")
        `q])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `q
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.typeAscription
       "("
       `p
       ":"
       [(Term.app `Set [(Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ "ℓ_infty_ℝ")])]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Set [(Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ "ℓ_infty_ℝ")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ "ℓ_infty_ℝ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ', expected 'Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ._@.Topology.MetricSpace.GromovHausdorff._hyg.5'
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
/--
    The optimal coupling constructed above realizes exactly the Gromov-Hausdorff distance,
    essentially by design. -/
  theorem
    Hausdorff_dist_optimal
    { X : Type u }
        [ MetricSpace X ]
        [ CompactSpace X ]
        [ Nonempty X ]
        { Y : Type v }
        [ MetricSpace Y ]
        [ CompactSpace Y ]
        [ Nonempty Y ]
      : hausdorffDist range optimalGHInjl X Y range optimalGHInjr X Y = gHDist X Y
    :=
      by
        inhabit X
          inhabit Y
          have
            A
              :
                ∀
                  p q
                  : nonempty_compacts ℓ_infty_ℝ
                  ,
                  ⟦ p ⟧ = to_GH_space X
                    →
                    ⟦ q ⟧ = to_GH_space Y
                      →
                      Hausdorff_dist ( p : Set ℓ_infty_ℝ ) q
                          <
                          diam ( univ : Set X ) + 1 + diam ( univ : Set Y )
                        →
                        Hausdorff_dist range optimal_GH_injl X Y range optimal_GH_injr X Y
                          ≤
                          Hausdorff_dist ( p : Set ℓ_infty_ℝ ) q
              :=
              by
                intro p q hp hq bound
                  rcases eq_to_GH_space_iff . 1 hp with ⟨ Φ , ⟨ Φisom , Φrange ⟩ ⟩
                  rcases eq_to_GH_space_iff . 1 hq with ⟨ Ψ , ⟨ Ψisom , Ψrange ⟩ ⟩
                  have
                    I
                      :
                        diam range Φ ∪ range Ψ
                          ≤
                          2 * diam ( univ : Set X ) + 1 + 2 * diam ( univ : Set Y )
                      :=
                      by
                        rcases exists_mem_of_nonempty X with ⟨ xX , _ ⟩
                          have
                            :
                                ∃
                                  y
                                  ∈ range Ψ
                                  ,
                                  dist Φ xX y < diam ( univ : Set X ) + 1 + diam ( univ : Set Y )
                              :=
                              by
                                rw [ Ψrange ]
                                  have : Φ xX ∈ ↑ p := Φrange.subst mem_range_self _
                                  exact
                                    exists_dist_lt_of_Hausdorff_dist_lt
                                      this
                                        bound
                                        Hausdorff_edist_ne_top_of_nonempty_of_bounded
                                          p.nonempty
                                            q.nonempty
                                            p.is_compact.bounded
                                            q.is_compact.bounded
                          rcases this with ⟨ y , hy , dy ⟩
                          rcases mem_range . 1 hy with ⟨ z , hzy ⟩
                          rw [ ← hzy ] at dy
                          have DΦ : diam range Φ = diam ( univ : Set X ) := Φisom.diam_range
                          have DΨ : diam range Ψ = diam ( univ : Set Y ) := Ψisom.diam_range
                          calc
                            diam range Φ ∪ range Ψ ≤ diam range Φ + dist Φ xX Ψ z + diam range Ψ
                              :=
                              diam_union mem_range_self _ mem_range_self _
                            _
                                  ≤
                                  diam ( univ : Set X )
                                      +
                                      diam ( univ : Set X ) + 1 + diam ( univ : Set Y )
                                    +
                                    diam ( univ : Set Y )
                                :=
                                by
                                  rw [ DΦ , DΨ ]
                                    apply add_le_add add_le_add le_rfl le_of_lt dy le_rfl
                              _ = 2 * diam ( univ : Set X ) + 1 + 2 * diam ( univ : Set Y )
                                :=
                                by ring
                  let f : Sum X Y → ℓ_infty_ℝ := fun x => match x with | inl y => Φ y | inr z => Ψ z
                  let F : Sum X Y × Sum X Y → ℝ := fun p => dist f p . 1 f p . 2
                  have
                    Fgood
                      : F ∈ candidates X Y
                      :=
                      by
                        simp
                            only
                            [
                              candidates
                                ,
                                forall_const
                                ,
                                and_true_iff
                                ,
                                add_comm
                                ,
                                eq_self_iff_true
                                ,
                                dist_eq_zero
                                ,
                                and_self_iff
                                ,
                                Set.mem_setOf_eq
                              ]
                          repeat' constructor
                          ·
                            exact
                              fun
                                x y
                                  =>
                                  calc
                                    F ( inl x , inl y ) = dist Φ x Φ y := rfl
                                    _ = dist x y := Φisom.dist_eq x y
                          ·
                            exact
                              fun
                                x y
                                  =>
                                  calc
                                    F ( inr x , inr y ) = dist Ψ x Ψ y := rfl
                                    _ = dist x y := Ψisom.dist_eq x y
                          · exact fun x y => dist_comm _ _
                          · exact fun x y z => dist_triangle _ _ _
                          ·
                            exact
                              fun
                                x y
                                  =>
                                  calc
                                    F ( x , y ) ≤ diam range Φ ∪ range Ψ
                                      :=
                                      by
                                        have
                                            A
                                              : ∀ z : Sum X Y , f z ∈ range Φ ∪ range Ψ
                                              :=
                                              by
                                                intro z
                                                  cases z
                                                  · apply mem_union_left apply mem_range_self
                                                  · apply mem_union_right apply mem_range_self
                                          refine' dist_le_diam_of_mem _ A _ A _
                                          rw [ Φrange , Ψrange ]
                                          exact p ⊔ q . IsCompact . Bounded
                                    _ ≤ 2 * diam ( univ : Set X ) + 1 + 2 * diam ( univ : Set Y )
                                      :=
                                      I
                  let Fb := candidates_b_of_candidates F Fgood
                  have
                    : Hausdorff_dist range optimal_GH_injl X Y range optimal_GH_injr X Y ≤ HD Fb
                      :=
                      Hausdorff_dist_optimal_le_HD _ _ candidates_b_of_candidates_mem F Fgood
                  refine' le_trans this le_of_forall_le_of_dense fun r hr => _
                  have
                    I1
                      : ∀ x : X , ⨅ y , Fb ( inl x , inr y ) ≤ r
                      :=
                      by
                        intro x
                          have : f inl x ∈ ↑ p := Φrange.subst mem_range_self _
                          rcases
                            exists_dist_lt_of_Hausdorff_dist_lt
                              this
                                hr
                                Hausdorff_edist_ne_top_of_nonempty_of_bounded
                                  p.nonempty q.nonempty p.is_compact.bounded q.is_compact.bounded
                            with ⟨ z , zq , hz ⟩
                          have : z ∈ range Ψ := by rwa [ ← Ψrange ] at zq
                          rcases mem_range . 1 this with ⟨ y , hy ⟩
                          calc
                            ⨅ y , Fb ( inl x , inr y ) ≤ Fb ( inl x , inr y )
                              :=
                              cinfᵢ_le by simpa only [ add_zero ] using HD_below_aux1 0 y
                            _ = dist Φ x Ψ y := rfl
                              _ = dist f inl x z := by rw [ hy ]
                              _ ≤ r := le_of_lt hz
                  have
                    I2
                      : ∀ y : Y , ⨅ x , Fb ( inl x , inr y ) ≤ r
                      :=
                      by
                        intro y
                          have : f inr y ∈ ↑ q := Ψrange.subst mem_range_self _
                          rcases
                            exists_dist_lt_of_Hausdorff_dist_lt'
                              this
                                hr
                                Hausdorff_edist_ne_top_of_nonempty_of_bounded
                                  p.nonempty q.nonempty p.is_compact.bounded q.is_compact.bounded
                            with ⟨ z , zq , hz ⟩
                          have : z ∈ range Φ := by rwa [ ← Φrange ] at zq
                          rcases mem_range . 1 this with ⟨ x , hx ⟩
                          calc
                            ⨅ x , Fb ( inl x , inr y ) ≤ Fb ( inl x , inr y )
                              :=
                              cinfᵢ_le by simpa only [ add_zero ] using HD_below_aux2 0 x
                            _ = dist Φ x Ψ y := rfl
                              _ = dist z f inr y := by rw [ hx ]
                              _ ≤ r := le_of_lt hz
                  simp only [ HD , csupᵢ_le I1 , csupᵢ_le I2 , max_le_iff , and_self_iff ]
          have
            B
              :
                ∀
                  p q
                  : nonempty_compacts ℓ_infty_ℝ
                  ,
                  ⟦ p ⟧ = to_GH_space X
                    →
                    ⟦ q ⟧ = to_GH_space Y
                      →
                      Hausdorff_dist range optimal_GH_injl X Y range optimal_GH_injr X Y
                        ≤
                        Hausdorff_dist ( p : Set ℓ_infty_ℝ ) q
              :=
              by
                intro p q hp hq
                  by_cases
                    h :
                    Hausdorff_dist ( p : Set ℓ_infty_ℝ ) q
                      <
                      diam ( univ : Set X ) + 1 + diam ( univ : Set Y )
                  · exact A p q hp hq h
                  ·
                    calc
                      Hausdorff_dist range optimal_GH_injl X Y range optimal_GH_injr X Y
                          ≤
                          HD candidates_b_dist X Y
                        :=
                        Hausdorff_dist_optimal_le_HD _ _ candidates_b_dist_mem_candidates_b
                      _ ≤ diam ( univ : Set X ) + 1 + diam ( univ : Set Y )
                          :=
                          HD_candidates_b_dist_le
                        _ ≤ Hausdorff_dist ( p : Set ℓ_infty_ℝ ) q := not_lt . 1 h
          refine' le_antisymm _ _
          ·
            apply le_cinfₛ
              · refine' Set.Nonempty.prod _ _ . image _ <;> exact ⟨ _ , rfl ⟩
              · rintro b ⟨ ⟨ p , q ⟩ , ⟨ hp , hq ⟩ , rfl ⟩ exact B p q hp hq
          ·
            exact
              GH_dist_le_Hausdorff_dist isometry_optimal_GH_injl X Y isometry_optimal_GH_injr X Y
#align Gromov_Hausdorff.Hausdorff_dist_optimal GromovHausdorff.Hausdorff_dist_optimal

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "The Gromov-Hausdorff distance can also be realized by a coupling in `ℓ^∞(ℝ)`, by embedding\nthe optimal coupling through its Kuratowski embedding. -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `GH_dist_eq_Hausdorff_dist [])
      (Command.declSig
       [(Term.explicitBinder "(" [`X] [":" (Term.type "Type" [`u])] [] ")")
        (Term.instBinder "[" [] (Term.app `MetricSpace [`X]) "]")
        (Term.instBinder "[" [] (Term.app `CompactSpace [`X]) "]")
        (Term.instBinder "[" [] (Term.app `Nonempty [`X]) "]")
        (Term.explicitBinder "(" [`Y] [":" (Term.type "Type" [`v])] [] ")")
        (Term.instBinder "[" [] (Term.app `MetricSpace [`Y]) "]")
        (Term.instBinder "[" [] (Term.app `CompactSpace [`Y]) "]")
        (Term.instBinder "[" [] (Term.app `Nonempty [`Y]) "]")]
       (Term.typeSpec
        ":"
        («term∃_,_»
         "∃"
         (Lean.explicitBinders
          (Lean.unbracketedExplicitBinders
           [(Lean.binderIdent `Φ)]
           [":"
            (Term.arrow `X "→" (Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ "ℓ_infty_ℝ"))]))
         ","
         («term∃_,_»
          "∃"
          (Lean.explicitBinders
           (Lean.unbracketedExplicitBinders
            [(Lean.binderIdent `Ψ)]
            [":"
             (Term.arrow `Y "→" (Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ "ℓ_infty_ℝ"))]))
          ","
          («term_∧_»
           (Term.app `Isometry [`Φ])
           "∧"
           («term_∧_»
            (Term.app `Isometry [`Ψ])
            "∧"
            («term_=_»
             (Term.app `gHDist [`X `Y])
             "="
             (Term.app `hausdorffDist [(Term.app `range [`Φ]) (Term.app `range [`Ψ])]))))))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.tacticLet_
            "let"
            (Term.letDecl
             (Term.letIdDecl
              `F
              []
              []
              ":="
              (Term.app `kuratowskiEmbedding [(Term.app `optimal_GH_coupling [`X `Y])]))))
           []
           (Tactic.tacticLet_
            "let"
            (Term.letDecl
             (Term.letIdDecl `Φ [] [] ":=" («term_∘_» `F "∘" (Term.app `optimal_GH_injl [`X `Y])))))
           []
           (Tactic.tacticLet_
            "let"
            (Term.letDecl
             (Term.letIdDecl `Ψ [] [] ":=" («term_∘_» `F "∘" (Term.app `optimal_GH_injr [`X `Y])))))
           []
           (Tactic.refine'
            "refine'"
            (Term.anonymousCtor
             "⟨"
             [`Φ "," `Ψ "," (Term.hole "_") "," (Term.hole "_") "," (Term.hole "_")]
             "⟩"))
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.exact
              "exact"
              (Term.app
               (Term.proj (Term.app `kuratowskiEmbedding.isometry [(Term.hole "_")]) "." `comp)
               [(Term.app `isometry_optimal_GH_injl [`X `Y])]))])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.exact
              "exact"
              (Term.app
               (Term.proj (Term.app `kuratowskiEmbedding.isometry [(Term.hole "_")]) "." `comp)
               [(Term.app `isometry_optimal_GH_injr [`X `Y])]))])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `image_univ)
                ","
                (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `image_univ)
                ","
                (Tactic.rwRule [] (Term.app `image_comp [`F]))
                ","
                (Tactic.rwRule [] `image_univ)
                ","
                (Tactic.rwRule [] (Term.app `image_comp [`F (Term.app `optimal_GH_injr [`X `Y])]))
                ","
                (Tactic.rwRule [] `image_univ)
                ","
                (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Hausdorff_dist_optimal)]
               "]")
              [])
             []
             (Tactic.exact
              "exact"
              (Term.proj
               (Term.app
                `Hausdorff_dist_image
                [(Term.app `kuratowskiEmbedding.isometry [(Term.hole "_")])])
               "."
               `symm))])])))
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
         [(Tactic.tacticLet_
           "let"
           (Term.letDecl
            (Term.letIdDecl
             `F
             []
             []
             ":="
             (Term.app `kuratowskiEmbedding [(Term.app `optimal_GH_coupling [`X `Y])]))))
          []
          (Tactic.tacticLet_
           "let"
           (Term.letDecl
            (Term.letIdDecl `Φ [] [] ":=" («term_∘_» `F "∘" (Term.app `optimal_GH_injl [`X `Y])))))
          []
          (Tactic.tacticLet_
           "let"
           (Term.letDecl
            (Term.letIdDecl `Ψ [] [] ":=" («term_∘_» `F "∘" (Term.app `optimal_GH_injr [`X `Y])))))
          []
          (Tactic.refine'
           "refine'"
           (Term.anonymousCtor
            "⟨"
            [`Φ "," `Ψ "," (Term.hole "_") "," (Term.hole "_") "," (Term.hole "_")]
            "⟩"))
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.exact
             "exact"
             (Term.app
              (Term.proj (Term.app `kuratowskiEmbedding.isometry [(Term.hole "_")]) "." `comp)
              [(Term.app `isometry_optimal_GH_injl [`X `Y])]))])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.exact
             "exact"
             (Term.app
              (Term.proj (Term.app `kuratowskiEmbedding.isometry [(Term.hole "_")]) "." `comp)
              [(Term.app `isometry_optimal_GH_injr [`X `Y])]))])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `image_univ)
               ","
               (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `image_univ)
               ","
               (Tactic.rwRule [] (Term.app `image_comp [`F]))
               ","
               (Tactic.rwRule [] `image_univ)
               ","
               (Tactic.rwRule [] (Term.app `image_comp [`F (Term.app `optimal_GH_injr [`X `Y])]))
               ","
               (Tactic.rwRule [] `image_univ)
               ","
               (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Hausdorff_dist_optimal)]
              "]")
             [])
            []
            (Tactic.exact
             "exact"
             (Term.proj
              (Term.app
               `Hausdorff_dist_image
               [(Term.app `kuratowskiEmbedding.isometry [(Term.hole "_")])])
              "."
              `symm))])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `image_univ)
           ","
           (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `image_univ)
           ","
           (Tactic.rwRule [] (Term.app `image_comp [`F]))
           ","
           (Tactic.rwRule [] `image_univ)
           ","
           (Tactic.rwRule [] (Term.app `image_comp [`F (Term.app `optimal_GH_injr [`X `Y])]))
           ","
           (Tactic.rwRule [] `image_univ)
           ","
           (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Hausdorff_dist_optimal)]
          "]")
         [])
        []
        (Tactic.exact
         "exact"
         (Term.proj
          (Term.app
           `Hausdorff_dist_image
           [(Term.app `kuratowskiEmbedding.isometry [(Term.hole "_")])])
          "."
          `symm))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.proj
        (Term.app
         `Hausdorff_dist_image
         [(Term.app `kuratowskiEmbedding.isometry [(Term.hole "_")])])
        "."
        `symm))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj
       (Term.app `Hausdorff_dist_image [(Term.app `kuratowskiEmbedding.isometry [(Term.hole "_")])])
       "."
       `symm)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `Hausdorff_dist_image [(Term.app `kuratowskiEmbedding.isometry [(Term.hole "_")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `kuratowskiEmbedding.isometry [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `kuratowskiEmbedding.isometry
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `kuratowskiEmbedding.isometry [(Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Hausdorff_dist_image
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `Hausdorff_dist_image
      [(Term.paren "(" (Term.app `kuratowskiEmbedding.isometry [(Term.hole "_")]) ")")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `image_univ)
         ","
         (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `image_univ)
         ","
         (Tactic.rwRule [] (Term.app `image_comp [`F]))
         ","
         (Tactic.rwRule [] `image_univ)
         ","
         (Tactic.rwRule [] (Term.app `image_comp [`F (Term.app `optimal_GH_injr [`X `Y])]))
         ","
         (Tactic.rwRule [] `image_univ)
         ","
         (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Hausdorff_dist_optimal)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Hausdorff_dist_optimal
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `image_univ
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `image_comp [`F (Term.app `optimal_GH_injr [`X `Y])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `optimal_GH_injr [`X `Y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `X
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `optimal_GH_injr
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `optimal_GH_injr [`X `Y]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `F
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `image_comp
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `image_univ
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `image_comp [`F])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `F
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `image_comp
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `image_univ
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `image_univ
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.exact
         "exact"
         (Term.app
          (Term.proj (Term.app `kuratowskiEmbedding.isometry [(Term.hole "_")]) "." `comp)
          [(Term.app `isometry_optimal_GH_injr [`X `Y])]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.app
        (Term.proj (Term.app `kuratowskiEmbedding.isometry [(Term.hole "_")]) "." `comp)
        [(Term.app `isometry_optimal_GH_injr [`X `Y])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj (Term.app `kuratowskiEmbedding.isometry [(Term.hole "_")]) "." `comp)
       [(Term.app `isometry_optimal_GH_injr [`X `Y])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `isometry_optimal_GH_injr [`X `Y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `X
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `isometry_optimal_GH_injr
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `isometry_optimal_GH_injr [`X `Y])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app `kuratowskiEmbedding.isometry [(Term.hole "_")]) "." `comp)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `kuratowskiEmbedding.isometry [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `kuratowskiEmbedding.isometry
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `kuratowskiEmbedding.isometry [(Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.exact
         "exact"
         (Term.app
          (Term.proj (Term.app `kuratowskiEmbedding.isometry [(Term.hole "_")]) "." `comp)
          [(Term.app `isometry_optimal_GH_injl [`X `Y])]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.app
        (Term.proj (Term.app `kuratowskiEmbedding.isometry [(Term.hole "_")]) "." `comp)
        [(Term.app `isometry_optimal_GH_injl [`X `Y])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj (Term.app `kuratowskiEmbedding.isometry [(Term.hole "_")]) "." `comp)
       [(Term.app `isometry_optimal_GH_injl [`X `Y])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `isometry_optimal_GH_injl [`X `Y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `X
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `isometry_optimal_GH_injl
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `isometry_optimal_GH_injl [`X `Y])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app `kuratowskiEmbedding.isometry [(Term.hole "_")]) "." `comp)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `kuratowskiEmbedding.isometry [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `kuratowskiEmbedding.isometry
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `kuratowskiEmbedding.isometry [(Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine'
       "refine'"
       (Term.anonymousCtor
        "⟨"
        [`Φ "," `Ψ "," (Term.hole "_") "," (Term.hole "_") "," (Term.hole "_")]
        "⟩"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [`Φ "," `Ψ "," (Term.hole "_") "," (Term.hole "_") "," (Term.hole "_")]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Ψ
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Φ
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticLet_
       "let"
       (Term.letDecl
        (Term.letIdDecl `Ψ [] [] ":=" («term_∘_» `F "∘" (Term.app `optimal_GH_injr [`X `Y])))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∘_» `F "∘" (Term.app `optimal_GH_injr [`X `Y]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `optimal_GH_injr [`X `Y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `X
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `optimal_GH_injr
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 90 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 90, term))
      `F
[PrettyPrinter.parenthesize] ...precedences are 91 >? 1024, (none, [anonymous]) <=? (some 90, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 90, (some 90, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticLet_
       "let"
       (Term.letDecl
        (Term.letIdDecl `Φ [] [] ":=" («term_∘_» `F "∘" (Term.app `optimal_GH_injl [`X `Y])))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∘_» `F "∘" (Term.app `optimal_GH_injl [`X `Y]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `optimal_GH_injl [`X `Y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `X
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `optimal_GH_injl
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 90 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 90, term))
      `F
[PrettyPrinter.parenthesize] ...precedences are 91 >? 1024, (none, [anonymous]) <=? (some 90, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 90, (some 90, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticLet_
       "let"
       (Term.letDecl
        (Term.letIdDecl
         `F
         []
         []
         ":="
         (Term.app `kuratowskiEmbedding [(Term.app `optimal_GH_coupling [`X `Y])]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `kuratowskiEmbedding [(Term.app `optimal_GH_coupling [`X `Y])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `optimal_GH_coupling [`X `Y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `X
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `optimal_GH_coupling
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `optimal_GH_coupling [`X `Y])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `kuratowskiEmbedding
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term∃_,_»
       "∃"
       (Lean.explicitBinders
        (Lean.unbracketedExplicitBinders
         [(Lean.binderIdent `Φ)]
         [":"
          (Term.arrow `X "→" (Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ "ℓ_infty_ℝ"))]))
       ","
       («term∃_,_»
        "∃"
        (Lean.explicitBinders
         (Lean.unbracketedExplicitBinders
          [(Lean.binderIdent `Ψ)]
          [":"
           (Term.arrow `Y "→" (Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ "ℓ_infty_ℝ"))]))
        ","
        («term_∧_»
         (Term.app `Isometry [`Φ])
         "∧"
         («term_∧_»
          (Term.app `Isometry [`Ψ])
          "∧"
          («term_=_»
           (Term.app `gHDist [`X `Y])
           "="
           (Term.app `hausdorffDist [(Term.app `range [`Φ]) (Term.app `range [`Ψ])]))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term∃_,_»
       "∃"
       (Lean.explicitBinders
        (Lean.unbracketedExplicitBinders
         [(Lean.binderIdent `Ψ)]
         [":"
          (Term.arrow `Y "→" (Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ "ℓ_infty_ℝ"))]))
       ","
       («term_∧_»
        (Term.app `Isometry [`Φ])
        "∧"
        («term_∧_»
         (Term.app `Isometry [`Ψ])
         "∧"
         («term_=_»
          (Term.app `gHDist [`X `Y])
          "="
          (Term.app `hausdorffDist [(Term.app `range [`Φ]) (Term.app `range [`Ψ])])))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∧_»
       (Term.app `Isometry [`Φ])
       "∧"
       («term_∧_»
        (Term.app `Isometry [`Ψ])
        "∧"
        («term_=_»
         (Term.app `gHDist [`X `Y])
         "="
         (Term.app `hausdorffDist [(Term.app `range [`Φ]) (Term.app `range [`Ψ])]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∧_»
       (Term.app `Isometry [`Ψ])
       "∧"
       («term_=_»
        (Term.app `gHDist [`X `Y])
        "="
        (Term.app `hausdorffDist [(Term.app `range [`Φ]) (Term.app `range [`Ψ])])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Term.app `gHDist [`X `Y])
       "="
       (Term.app `hausdorffDist [(Term.app `range [`Φ]) (Term.app `range [`Ψ])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `hausdorffDist [(Term.app `range [`Φ]) (Term.app `range [`Ψ])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `range [`Ψ])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Ψ
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `range
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `range [`Ψ]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `range [`Φ])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Φ
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `range
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `range [`Φ]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `hausdorffDist
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app `gHDist [`X `Y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `X
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `gHDist
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 35 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 35, term))
      (Term.app `Isometry [`Ψ])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Ψ
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Isometry
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 36 >? 1022, (some 1023, term) <=? (some 35, term)
[PrettyPrinter.parenthesize] ...precedences are 35 >? 35, (some 35, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 35, term))
      (Term.app `Isometry [`Φ])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Φ
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Isometry
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 36 >? 1022, (some 1023, term) <=? (some 35, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 35, (some 35, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'Lean.bracketedExplicitBinders'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.arrow `Y "→" (Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ "ℓ_infty_ℝ"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ "ℓ_infty_ℝ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ', expected 'Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ._@.Topology.MetricSpace.GromovHausdorff._hyg.5'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    The Gromov-Hausdorff distance can also be realized by a coupling in `ℓ^∞(ℝ)`, by embedding
    the optimal coupling through its Kuratowski embedding. -/
  theorem
    GH_dist_eq_Hausdorff_dist
    ( X : Type u )
        [ MetricSpace X ]
        [ CompactSpace X ]
        [ Nonempty X ]
        ( Y : Type v )
        [ MetricSpace Y ]
        [ CompactSpace Y ]
        [ Nonempty Y ]
      :
        ∃
          Φ : X → ℓ_infty_ℝ
          ,
          ∃ Ψ : Y → ℓ_infty_ℝ , Isometry Φ ∧ Isometry Ψ ∧ gHDist X Y = hausdorffDist range Φ range Ψ
    :=
      by
        let F := kuratowskiEmbedding optimal_GH_coupling X Y
          let Φ := F ∘ optimal_GH_injl X Y
          let Ψ := F ∘ optimal_GH_injr X Y
          refine' ⟨ Φ , Ψ , _ , _ , _ ⟩
          · exact kuratowskiEmbedding.isometry _ . comp isometry_optimal_GH_injl X Y
          · exact kuratowskiEmbedding.isometry _ . comp isometry_optimal_GH_injr X Y
          ·
            rw
                [
                  ← image_univ
                    ,
                    ← image_univ
                    ,
                    image_comp F
                    ,
                    image_univ
                    ,
                    image_comp F optimal_GH_injr X Y
                    ,
                    image_univ
                    ,
                    ← Hausdorff_dist_optimal
                  ]
              exact Hausdorff_dist_image kuratowskiEmbedding.isometry _ . symm
#align Gromov_Hausdorff.GH_dist_eq_Hausdorff_dist GromovHausdorff.GH_dist_eq_Hausdorff_dist

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "The Gromov-Hausdorff distance defines a genuine distance on the Gromov-Hausdorff space. -/")]
      []
      []
      []
      []
      [])
     (Command.instance
      (Term.attrKind [])
      "instance"
      []
      []
      (Command.declSig [] (Term.typeSpec ":" (Term.app `MetricSpace [`GHSpace])))
      (Command.whereStructInst
       "where"
       [(Command.whereStructField (Term.letDecl (Term.letIdDecl `dist [] [] ":=" `dist)))
        []
        (Command.whereStructField
         (Term.letDecl
          (Term.letIdDecl
           `dist_self
           [`x]
           []
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Std.Tactic.rcases
                "rcases"
                [(Tactic.casesTarget [] (Term.app `exists_rep [`x]))]
                ["with"
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed
                   [(Std.Tactic.RCases.rcasesPat.tuple
                     "⟨"
                     [(Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `y)])
                       [])
                      ","
                      (Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hy)])
                       [])]
                     "⟩")])
                  [])])
               []
               (Tactic.refine' "refine'" (Term.app `le_antisymm [(Term.hole "_") (Term.hole "_")]))
               []
               (tactic__
                (cdotTk (patternIgnore (token.«· » "·")))
                [(Tactic.apply "apply" `cinfₛ_le)
                 []
                 (tactic__
                  (cdotTk (patternIgnore (token.«· » "·")))
                  [(Tactic.exact
                    "exact"
                    (Term.anonymousCtor
                     "⟨"
                     [(num "0")
                      ","
                      (Term.byTactic
                       "by"
                       (Tactic.tacticSeq
                        (Tactic.tacticSeq1Indented
                         [(Std.Tactic.rintro
                           "rintro"
                           [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `b))
                            (Std.Tactic.RCases.rintroPat.one
                             (Std.Tactic.RCases.rcasesPat.tuple
                              "⟨"
                              [(Std.Tactic.RCases.rcasesPatLo
                                (Std.Tactic.RCases.rcasesPatMed
                                 [(Std.Tactic.RCases.rcasesPat.tuple
                                   "⟨"
                                   [(Std.Tactic.RCases.rcasesPatLo
                                     (Std.Tactic.RCases.rcasesPatMed
                                      [(Std.Tactic.RCases.rcasesPat.one `u)])
                                     [])
                                    ","
                                    (Std.Tactic.RCases.rcasesPatLo
                                     (Std.Tactic.RCases.rcasesPatMed
                                      [(Std.Tactic.RCases.rcasesPat.one `v)])
                                     [])]
                                   "⟩")])
                                [])
                               ","
                               (Std.Tactic.RCases.rcasesPatLo
                                (Std.Tactic.RCases.rcasesPatMed
                                 [(Std.Tactic.RCases.rcasesPat.tuple
                                   "⟨"
                                   [(Std.Tactic.RCases.rcasesPatLo
                                     (Std.Tactic.RCases.rcasesPatMed
                                      [(Std.Tactic.RCases.rcasesPat.one `hu)])
                                     [])
                                    ","
                                    (Std.Tactic.RCases.rcasesPatLo
                                     (Std.Tactic.RCases.rcasesPatMed
                                      [(Std.Tactic.RCases.rcasesPat.one `hv)])
                                     [])]
                                   "⟩")])
                                [])
                               ","
                               (Std.Tactic.RCases.rcasesPatLo
                                (Std.Tactic.RCases.rcasesPatMed
                                 [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                                [])]
                              "⟩"))]
                           [])
                          []
                          (Tactic.exact "exact" `Hausdorff_dist_nonneg)])))]
                     "⟩"))])
                 []
                 (tactic__
                  (cdotTk (patternIgnore (token.«· » "·")))
                  [(Tactic.simp
                    "simp"
                    []
                    []
                    ["only"]
                    ["["
                     [(Tactic.simpLemma [] [] `mem_image)
                      ","
                      (Tactic.simpLemma [] [] `mem_prod)
                      ","
                      (Tactic.simpLemma [] [] `mem_set_of_eq)
                      ","
                      (Tactic.simpLemma [] [] `Prod.exists)]
                     "]"]
                    [])
                   []
                   (Tactic.«tacticExists_,,» "exists" [`y "," `y])
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
                       [(Tactic.simpLemma [] [] `and_self_iff)
                        ","
                        (Tactic.simpLemma [] [] `Hausdorff_dist_self_zero)
                        ","
                        (Tactic.simpLemma [] [] `eq_self_iff_true)
                        ","
                        (Tactic.simpLemma [] [] `and_true_iff)]
                       "]")]
                     []))])])
               []
               (tactic__
                (cdotTk (patternIgnore (token.«· » "·")))
                [(Tactic.apply "apply" `le_cinfₛ)
                 []
                 (tactic__
                  (cdotTk (patternIgnore (token.«· » "·")))
                  [(Tactic.exact
                    "exact"
                    (Term.app
                     (Term.proj
                      (Term.app
                       `nonempty.prod
                       [(Term.anonymousCtor "⟨" [`y "," `hy] "⟩")
                        (Term.anonymousCtor "⟨" [`y "," `hy] "⟩")])
                      "."
                      `image)
                     [(Term.hole "_")]))])
                 []
                 (tactic__
                  (cdotTk (patternIgnore (token.«· » "·")))
                  [(Std.Tactic.rintro
                    "rintro"
                    [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `b))
                     (Std.Tactic.RCases.rintroPat.one
                      (Std.Tactic.RCases.rcasesPat.tuple
                       "⟨"
                       [(Std.Tactic.RCases.rcasesPatLo
                         (Std.Tactic.RCases.rcasesPatMed
                          [(Std.Tactic.RCases.rcasesPat.tuple
                            "⟨"
                            [(Std.Tactic.RCases.rcasesPatLo
                              (Std.Tactic.RCases.rcasesPatMed
                               [(Std.Tactic.RCases.rcasesPat.one `u)])
                              [])
                             ","
                             (Std.Tactic.RCases.rcasesPatLo
                              (Std.Tactic.RCases.rcasesPatMed
                               [(Std.Tactic.RCases.rcasesPat.one `v)])
                              [])]
                            "⟩")])
                         [])
                        ","
                        (Std.Tactic.RCases.rcasesPatLo
                         (Std.Tactic.RCases.rcasesPatMed
                          [(Std.Tactic.RCases.rcasesPat.tuple
                            "⟨"
                            [(Std.Tactic.RCases.rcasesPatLo
                              (Std.Tactic.RCases.rcasesPatMed
                               [(Std.Tactic.RCases.rcasesPat.one `hu)])
                              [])
                             ","
                             (Std.Tactic.RCases.rcasesPatLo
                              (Std.Tactic.RCases.rcasesPatMed
                               [(Std.Tactic.RCases.rcasesPat.one `hv)])
                              [])]
                            "⟩")])
                         [])
                        ","
                        (Std.Tactic.RCases.rcasesPatLo
                         (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                         [])]
                       "⟩"))]
                    [])
                   []
                   (Tactic.exact "exact" `Hausdorff_dist_nonneg)])])]))))))
        []
        (Command.whereStructField
         (Term.letDecl
          (Term.letIdDecl
           `dist_comm
           [`x `y]
           []
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.tacticHave_
                "have"
                (Term.haveDecl
                 (Term.haveIdDecl
                  [`A []]
                  [(Term.typeSpec
                    ":"
                    («term_=_»
                     (Set.Data.Set.Image.term_''_
                      (Term.fun
                       "fun"
                       (Term.basicFun
                        [`p]
                        [(Term.typeSpec
                          ":"
                          («term_×_»
                           (Term.app
                            `nonempty_compacts
                            [(Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ "ℓ_infty_ℝ")])
                           "×"
                           (Term.app
                            `nonempty_compacts
                            [(Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ "ℓ_infty_ℝ")])))]
                        "=>"
                        (Term.app
                         `Hausdorff_dist
                         [(Term.typeAscription
                           "("
                           (Term.proj `p "." (fieldIdx "1"))
                           ":"
                           [(Term.app
                             `Set
                             [(Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ "ℓ_infty_ℝ")])]
                           ")")
                          (Term.proj `p "." (fieldIdx "2"))])))
                      " '' "
                      (LowerSet.Order.UpperLower.lower_set.prod
                       (Set.«term{_|_}»
                        "{"
                        (Std.ExtendedBinder.extBinder (Lean.binderIdent `a) [])
                        "|"
                        («term_=_» (Quotient.Init.Data.Quot.«term⟦_⟧» "⟦" `a "⟧") "=" `x)
                        "}")
                       " ×ˢ "
                       (Set.«term{_|_}»
                        "{"
                        (Std.ExtendedBinder.extBinder (Lean.binderIdent `b) [])
                        "|"
                        («term_=_» (Quotient.Init.Data.Quot.«term⟦_⟧» "⟦" `b "⟧") "=" `y)
                        "}")))
                     "="
                     (Set.Data.Set.Image.term_''_
                      («term_∘_»
                       (Term.fun
                        "fun"
                        (Term.basicFun
                         [`p]
                         [(Term.typeSpec
                           ":"
                           («term_×_»
                            (Term.app
                             `nonempty_compacts
                             [(Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ "ℓ_infty_ℝ")])
                            "×"
                            (Term.app
                             `nonempty_compacts
                             [(Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ "ℓ_infty_ℝ")])))]
                         "=>"
                         (Term.app
                          `Hausdorff_dist
                          [(Term.typeAscription
                            "("
                            (Term.proj `p "." (fieldIdx "1"))
                            ":"
                            [(Term.app
                              `Set
                              [(Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ "ℓ_infty_ℝ")])]
                            ")")
                           (Term.proj `p "." (fieldIdx "2"))])))
                       "∘"
                       `Prod.swap)
                      " '' "
                      (LowerSet.Order.UpperLower.lower_set.prod
                       (Set.«term{_|_}»
                        "{"
                        (Std.ExtendedBinder.extBinder (Lean.binderIdent `a) [])
                        "|"
                        («term_=_» (Quotient.Init.Data.Quot.«term⟦_⟧» "⟦" `a "⟧") "=" `x)
                        "}")
                       " ×ˢ "
                       (Set.«term{_|_}»
                        "{"
                        (Std.ExtendedBinder.extBinder (Lean.binderIdent `b) [])
                        "|"
                        («term_=_» (Quotient.Init.Data.Quot.«term⟦_⟧» "⟦" `b "⟧") "=" `y)
                        "}")))))]
                  ":="
                  (Term.byTactic
                   "by"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented
                     [(Tactic.congr "congr" [])
                      []
                      (tacticFunext__ "funext" [])
                      []
                      (Tactic.simp
                       "simp"
                       []
                       []
                       ["only"]
                       ["["
                        [(Tactic.simpLemma [] [] `comp_app)
                         ","
                         (Tactic.simpLemma [] [] `Prod.fst_swap)
                         ","
                         (Tactic.simpLemma [] [] `Prod.snd_swap)]
                        "]"]
                       [])
                      []
                      (Tactic.rwSeq
                       "rw"
                       []
                       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Hausdorff_dist_comm)] "]")
                       [])]))))))
               []
               (Tactic.simp
                "simp"
                []
                []
                ["only"]
                ["["
                 [(Tactic.simpLemma [] [] `dist)
                  ","
                  (Tactic.simpLemma [] [] `A)
                  ","
                  (Tactic.simpLemma [] [] `image_comp)
                  ","
                  (Tactic.simpLemma [] [] `image_swap_prod)]
                 "]"]
                [])]))))))
        []
        (Command.whereStructField
         (Term.letDecl
          (Term.letIdDecl
           `eq_of_dist_eq_zero
           [`x `y `hxy]
           []
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Std.Tactic.rcases
                "rcases"
                [(Tactic.casesTarget [] (Term.app `GH_dist_eq_Hausdorff_dist [`x.rep `y.rep]))]
                ["with"
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed
                   [(Std.Tactic.RCases.rcasesPat.tuple
                     "⟨"
                     [(Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `Φ)])
                       [])
                      ","
                      (Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `Ψ)])
                       [])
                      ","
                      (Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `Φisom)])
                       [])
                      ","
                      (Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `Ψisom)])
                       [])
                      ","
                      (Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `DΦΨ)])
                       [])]
                     "⟩")])
                  [])])
               []
               (Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `dist_GH_dist)
                  ","
                  (Tactic.rwRule [] `hxy)]
                 "]")
                [(Tactic.location "at" (Tactic.locationHyp [`DΦΨ] []))])
               []
               (Tactic.tacticHave_
                "have"
                (Term.haveDecl
                 (Term.haveIdDecl
                  []
                  [(Term.typeSpec
                    ":"
                    («term_=_» (Term.app `range [`Φ]) "=" (Term.app `range [`Ψ])))]
                  ":="
                  (Term.byTactic
                   "by"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented
                     [(Tactic.tacticHave_
                       "have"
                       (Term.haveDecl
                        (Term.haveIdDecl
                         [`hΦ []]
                         [(Term.typeSpec ":" (Term.app `IsCompact [(Term.app `range [`Φ])]))]
                         ":="
                         (Term.app `is_compact_range [`Φisom.continuous]))))
                      []
                      (Tactic.tacticHave_
                       "have"
                       (Term.haveDecl
                        (Term.haveIdDecl
                         [`hΨ []]
                         [(Term.typeSpec ":" (Term.app `IsCompact [(Term.app `range [`Ψ])]))]
                         ":="
                         (Term.app `is_compact_range [`Ψisom.continuous]))))
                      []
                      (Tactic.apply
                       "apply"
                       (Term.app
                        (Term.proj
                         (Term.app
                          `IsClosed.Hausdorff_dist_zero_iff_eq
                          [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
                         "."
                         (fieldIdx "1"))
                        [`DΦΨ.symm]))
                      []
                      (tactic__
                       (cdotTk (patternIgnore (token.«· » "·")))
                       [(Tactic.exact "exact" `hΦ.is_closed)])
                      []
                      (tactic__
                       (cdotTk (patternIgnore (token.«· » "·")))
                       [(Tactic.exact "exact" `hΨ.is_closed)])
                      []
                      (tactic__
                       (cdotTk (patternIgnore (token.«· » "·")))
                       [(Tactic.exact
                         "exact"
                         (Term.app
                          `Hausdorff_edist_ne_top_of_nonempty_of_bounded
                          [(Term.app `range_nonempty [(Term.hole "_")])
                           (Term.app `range_nonempty [(Term.hole "_")])
                           `hΦ.bounded
                           `hΨ.bounded]))])]))))))
               []
               (Tactic.tacticHave_
                "have"
                (Term.haveDecl
                 (Term.haveIdDecl
                  [`T []]
                  [(Term.typeSpec
                    ":"
                    («term_=_»
                     (Topology.MetricSpace.Isometry.«term_≃ᵢ_» (Term.app `range [`Ψ]) " ≃ᵢ " `y.rep)
                     "="
                     (Topology.MetricSpace.Isometry.«term_≃ᵢ_»
                      (Term.app `range [`Φ])
                      " ≃ᵢ "
                      `y.rep)))]
                  ":="
                  (Term.byTactic
                   "by"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented
                     [(Tactic.rwSeq
                       "rw"
                       []
                       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `this)] "]")
                       [])]))))))
               []
               (Tactic.tacticHave_
                "have"
                (Term.haveDecl
                 (Term.haveIdDecl
                  [`eΨ []]
                  []
                  ":="
                  (Term.app `cast [`T `Ψisom.isometric_on_range.symm]))))
               []
               (Tactic.tacticHave_
                "have"
                (Term.haveDecl
                 (Term.haveIdDecl
                  [`e []]
                  []
                  ":="
                  (Term.app `Φisom.isometric_on_range.trans [`eΨ]))))
               []
               (Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `x.to_GH_space_rep)
                  ","
                  (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `y.to_GH_space_rep)
                  ","
                  (Tactic.rwRule [] `to_GH_space_eq_to_GH_space_iff_isometric)]
                 "]")
                [])
               []
               (Tactic.exact "exact" (Term.anonymousCtor "⟨" [`e] "⟩"))]))))))
        []
        (Command.whereStructField
         (Term.letDecl
          (Term.letIdDecl
           `dist_triangle
           [`x `y `z]
           []
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.tacticLet_ "let" (Term.letDecl (Term.letIdDecl `X [] [] ":=" `x.rep)))
               []
               (Tactic.tacticLet_ "let" (Term.letDecl (Term.letIdDecl `Y [] [] ":=" `y.rep)))
               []
               (Tactic.tacticLet_ "let" (Term.letDecl (Term.letIdDecl `Z [] [] ":=" `z.rep)))
               []
               (Tactic.tacticLet_
                "let"
                (Term.letDecl
                 (Term.letIdDecl `γ1 [] [] ":=" (Term.app `optimal_GH_coupling [`X `Y]))))
               []
               (Tactic.tacticLet_
                "let"
                (Term.letDecl
                 (Term.letIdDecl `γ2 [] [] ":=" (Term.app `optimal_GH_coupling [`Y `Z]))))
               []
               (Tactic.tacticLet_
                "let"
                (Term.letDecl
                 (Term.letIdDecl
                  `Φ
                  []
                  [(Term.typeSpec ":" (Term.arrow `Y "→" `γ1))]
                  ":="
                  (Term.app `optimal_GH_injr [`X `Y]))))
               []
               (Tactic.tacticHave_
                "have"
                (Term.haveDecl
                 (Term.haveIdDecl
                  [`hΦ []]
                  [(Term.typeSpec ":" (Term.app `Isometry [`Φ]))]
                  ":="
                  (Term.app `isometry_optimal_GH_injr [`X `Y]))))
               []
               (Tactic.tacticLet_
                "let"
                (Term.letDecl
                 (Term.letIdDecl
                  `Ψ
                  []
                  [(Term.typeSpec ":" (Term.arrow `Y "→" `γ2))]
                  ":="
                  (Term.app `optimal_GH_injl [`Y `Z]))))
               []
               (Tactic.tacticHave_
                "have"
                (Term.haveDecl
                 (Term.haveIdDecl
                  [`hΨ []]
                  [(Term.typeSpec ":" (Term.app `Isometry [`Ψ]))]
                  ":="
                  (Term.app `isometry_optimal_GH_injl [`Y `Z]))))
               []
               (Tactic.tacticLet_
                "let"
                (Term.letDecl (Term.letIdDecl `γ [] [] ":=" (Term.app `glue_space [`hΦ `hΨ]))))
               []
               (Std.Tactic.tacticLetI_
                "letI"
                (Term.haveDecl
                 (Term.haveIdDecl
                  []
                  [(Term.typeSpec ":" (Term.app `MetricSpace [`γ]))]
                  ":="
                  (Term.app `Metric.metricSpaceGlueSpace [`hΦ `hΨ]))))
               []
               (Tactic.tacticHave_
                "have"
                (Term.haveDecl
                 (Term.haveIdDecl
                  [`Comm []]
                  [(Term.typeSpec
                    ":"
                    («term_=_»
                     («term_∘_»
                      (Term.app `to_glue_l [`hΦ `hΨ])
                      "∘"
                      (Term.app `optimal_GH_injr [`X `Y]))
                     "="
                     («term_∘_»
                      (Term.app `to_glue_r [`hΦ `hΨ])
                      "∘"
                      (Term.app `optimal_GH_injl [`Y `Z]))))]
                  ":="
                  (Term.app `to_glue_commute [`hΦ `hΨ]))))
               []
               (calcTactic
                "calc"
                (calcStep
                 («term_=_»
                  (Term.app `dist [`x `z])
                  "="
                  (Term.app `dist [(Term.app `to_GH_space [`X]) (Term.app `to_GH_space [`Z])]))
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
                       [(Tactic.rwRule [] `x.to_GH_space_rep)
                        ","
                        (Tactic.rwRule [] `z.to_GH_space_rep)]
                       "]")
                      [])]))))
                [(calcStep
                  («term_≤_»
                   (Term.hole "_")
                   "≤"
                   (Term.app
                    `Hausdorff_dist
                    [(Term.app
                      `range
                      [(«term_∘_»
                        (Term.app `to_glue_l [`hΦ `hΨ])
                        "∘"
                        (Term.app `optimal_GH_injl [`X `Y]))])
                     (Term.app
                      `range
                      [(«term_∘_»
                        (Term.app `to_glue_r [`hΦ `hΨ])
                        "∘"
                        (Term.app `optimal_GH_injr [`Y `Z]))])]))
                  ":="
                  (Term.app
                   `GH_dist_le_Hausdorff_dist
                   [(Term.app
                     (Term.proj (Term.app `to_glue_l_isometry [`hΦ `hΨ]) "." `comp)
                     [(Term.app `isometry_optimal_GH_injl [`X `Y])])
                    (Term.app
                     (Term.proj (Term.app `to_glue_r_isometry [`hΦ `hΨ]) "." `comp)
                     [(Term.app `isometry_optimal_GH_injr [`Y `Z])])]))
                 (calcStep
                  («term_≤_»
                   (Term.hole "_")
                   "≤"
                   («term_+_»
                    (Term.app
                     `Hausdorff_dist
                     [(Term.app
                       `range
                       [(«term_∘_»
                         (Term.app `to_glue_l [`hΦ `hΨ])
                         "∘"
                         (Term.app `optimal_GH_injl [`X `Y]))])
                      (Term.app
                       `range
                       [(«term_∘_»
                         (Term.app `to_glue_l [`hΦ `hΨ])
                         "∘"
                         (Term.app `optimal_GH_injr [`X `Y]))])])
                    "+"
                    (Term.app
                     `Hausdorff_dist
                     [(Term.app
                       `range
                       [(«term_∘_»
                         (Term.app `to_glue_l [`hΦ `hΨ])
                         "∘"
                         (Term.app `optimal_GH_injr [`X `Y]))])
                      (Term.app
                       `range
                       [(«term_∘_»
                         (Term.app `to_glue_r [`hΦ `hΨ])
                         "∘"
                         (Term.app `optimal_GH_injr [`Y `Z]))])])))
                  ":="
                  (Term.byTactic
                   "by"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented
                     [(Tactic.refine'
                       "refine'"
                       (Term.app
                        `Hausdorff_dist_triangle
                        [(Term.app
                          `Hausdorff_edist_ne_top_of_nonempty_of_bounded
                          [(Term.app `range_nonempty [(Term.hole "_")])
                           (Term.app `range_nonempty [(Term.hole "_")])
                           (Term.hole "_")
                           (Term.hole "_")])]))
                      []
                      (tactic__
                       (cdotTk (patternIgnore (token.«· » "·")))
                       [(Tactic.exact
                         "exact"
                         (Term.proj
                          (Term.app
                           `is_compact_range
                           [(Term.app
                             `Isometry.continuous
                             [(Term.app
                               (Term.proj (Term.app `to_glue_l_isometry [`hΦ `hΨ]) "." `comp)
                               [(Term.app `isometry_optimal_GH_injl [`X `Y])])])])
                          "."
                          `Bounded))])
                      []
                      (tactic__
                       (cdotTk (patternIgnore (token.«· » "·")))
                       [(Tactic.exact
                         "exact"
                         (Term.proj
                          (Term.app
                           `is_compact_range
                           [(Term.app
                             `Isometry.continuous
                             [(Term.app
                               (Term.proj (Term.app `to_glue_l_isometry [`hΦ `hΨ]) "." `comp)
                               [(Term.app `isometry_optimal_GH_injr [`X `Y])])])])
                          "."
                          `Bounded))])]))))
                 (calcStep
                  («term_=_»
                   (Term.hole "_")
                   "="
                   («term_+_»
                    (Term.app
                     `Hausdorff_dist
                     [(Set.Data.Set.Image.term_''_
                       (Term.app `to_glue_l [`hΦ `hΨ])
                       " '' "
                       (Term.app `range [(Term.app `optimal_GH_injl [`X `Y])]))
                      (Set.Data.Set.Image.term_''_
                       (Term.app `to_glue_l [`hΦ `hΨ])
                       " '' "
                       (Term.app `range [(Term.app `optimal_GH_injr [`X `Y])]))])
                    "+"
                    (Term.app
                     `Hausdorff_dist
                     [(Set.Data.Set.Image.term_''_
                       (Term.app `to_glue_r [`hΦ `hΨ])
                       " '' "
                       (Term.app `range [(Term.app `optimal_GH_injl [`Y `Z])]))
                      (Set.Data.Set.Image.term_''_
                       (Term.app `to_glue_r [`hΦ `hΨ])
                       " '' "
                       (Term.app `range [(Term.app `optimal_GH_injr [`Y `Z])]))])))
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
                        [(Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `range_comp)
                         ","
                         (Tactic.simpLemma [] [] `Comm)
                         ","
                         (Tactic.simpLemma [] [] `eq_self_iff_true)
                         ","
                         (Tactic.simpLemma [] [] `add_right_inj)]
                        "]"]
                       [])]))))
                 (calcStep
                  («term_=_»
                   (Term.hole "_")
                   "="
                   («term_+_»
                    (Term.app
                     `Hausdorff_dist
                     [(Term.app `range [(Term.app `optimal_GH_injl [`X `Y])])
                      (Term.app `range [(Term.app `optimal_GH_injr [`X `Y])])])
                    "+"
                    (Term.app
                     `Hausdorff_dist
                     [(Term.app `range [(Term.app `optimal_GH_injl [`Y `Z])])
                      (Term.app `range [(Term.app `optimal_GH_injr [`Y `Z])])])))
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
                        [(Tactic.rwRule
                          []
                          (Term.app
                           `Hausdorff_dist_image
                           [(Term.app `to_glue_l_isometry [`hΦ `hΨ])]))
                         ","
                         (Tactic.rwRule
                          []
                          (Term.app
                           `Hausdorff_dist_image
                           [(Term.app `to_glue_r_isometry [`hΦ `hΨ])]))]
                        "]")
                       [])]))))
                 (calcStep
                  («term_=_»
                   (Term.hole "_")
                   "="
                   («term_+_»
                    (Term.app `dist [(Term.app `to_GH_space [`X]) (Term.app `to_GH_space [`Y])])
                    "+"
                    (Term.app `dist [(Term.app `to_GH_space [`Y]) (Term.app `to_GH_space [`Z])])))
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
                        [(Tactic.rwRule [] `Hausdorff_dist_optimal)
                         ","
                         (Tactic.rwRule [] `Hausdorff_dist_optimal)
                         ","
                         (Tactic.rwRule [] `GH_dist)
                         ","
                         (Tactic.rwRule [] `GH_dist)]
                        "]")
                       [])]))))
                 (calcStep
                  («term_=_»
                   (Term.hole "_")
                   "="
                   («term_+_» (Term.app `dist [`x `y]) "+" (Term.app `dist [`y `z])))
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
                        [(Tactic.rwRule [] `x.to_GH_space_rep)
                         ","
                         (Tactic.rwRule [] `y.to_GH_space_rep)
                         ","
                         (Tactic.rwRule [] `z.to_GH_space_rep)]
                        "]")
                       [])]))))])]))))))]
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
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.tacticLet_ "let" (Term.letDecl (Term.letIdDecl `X [] [] ":=" `x.rep)))
          []
          (Tactic.tacticLet_ "let" (Term.letDecl (Term.letIdDecl `Y [] [] ":=" `y.rep)))
          []
          (Tactic.tacticLet_ "let" (Term.letDecl (Term.letIdDecl `Z [] [] ":=" `z.rep)))
          []
          (Tactic.tacticLet_
           "let"
           (Term.letDecl (Term.letIdDecl `γ1 [] [] ":=" (Term.app `optimal_GH_coupling [`X `Y]))))
          []
          (Tactic.tacticLet_
           "let"
           (Term.letDecl (Term.letIdDecl `γ2 [] [] ":=" (Term.app `optimal_GH_coupling [`Y `Z]))))
          []
          (Tactic.tacticLet_
           "let"
           (Term.letDecl
            (Term.letIdDecl
             `Φ
             []
             [(Term.typeSpec ":" (Term.arrow `Y "→" `γ1))]
             ":="
             (Term.app `optimal_GH_injr [`X `Y]))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`hΦ []]
             [(Term.typeSpec ":" (Term.app `Isometry [`Φ]))]
             ":="
             (Term.app `isometry_optimal_GH_injr [`X `Y]))))
          []
          (Tactic.tacticLet_
           "let"
           (Term.letDecl
            (Term.letIdDecl
             `Ψ
             []
             [(Term.typeSpec ":" (Term.arrow `Y "→" `γ2))]
             ":="
             (Term.app `optimal_GH_injl [`Y `Z]))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`hΨ []]
             [(Term.typeSpec ":" (Term.app `Isometry [`Ψ]))]
             ":="
             (Term.app `isometry_optimal_GH_injl [`Y `Z]))))
          []
          (Tactic.tacticLet_
           "let"
           (Term.letDecl (Term.letIdDecl `γ [] [] ":=" (Term.app `glue_space [`hΦ `hΨ]))))
          []
          (Std.Tactic.tacticLetI_
           "letI"
           (Term.haveDecl
            (Term.haveIdDecl
             []
             [(Term.typeSpec ":" (Term.app `MetricSpace [`γ]))]
             ":="
             (Term.app `Metric.metricSpaceGlueSpace [`hΦ `hΨ]))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`Comm []]
             [(Term.typeSpec
               ":"
               («term_=_»
                («term_∘_» (Term.app `to_glue_l [`hΦ `hΨ]) "∘" (Term.app `optimal_GH_injr [`X `Y]))
                "="
                («term_∘_»
                 (Term.app `to_glue_r [`hΦ `hΨ])
                 "∘"
                 (Term.app `optimal_GH_injl [`Y `Z]))))]
             ":="
             (Term.app `to_glue_commute [`hΦ `hΨ]))))
          []
          (calcTactic
           "calc"
           (calcStep
            («term_=_»
             (Term.app `dist [`x `z])
             "="
             (Term.app `dist [(Term.app `to_GH_space [`X]) (Term.app `to_GH_space [`Z])]))
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
                  [(Tactic.rwRule [] `x.to_GH_space_rep) "," (Tactic.rwRule [] `z.to_GH_space_rep)]
                  "]")
                 [])]))))
           [(calcStep
             («term_≤_»
              (Term.hole "_")
              "≤"
              (Term.app
               `Hausdorff_dist
               [(Term.app
                 `range
                 [(«term_∘_»
                   (Term.app `to_glue_l [`hΦ `hΨ])
                   "∘"
                   (Term.app `optimal_GH_injl [`X `Y]))])
                (Term.app
                 `range
                 [(«term_∘_»
                   (Term.app `to_glue_r [`hΦ `hΨ])
                   "∘"
                   (Term.app `optimal_GH_injr [`Y `Z]))])]))
             ":="
             (Term.app
              `GH_dist_le_Hausdorff_dist
              [(Term.app
                (Term.proj (Term.app `to_glue_l_isometry [`hΦ `hΨ]) "." `comp)
                [(Term.app `isometry_optimal_GH_injl [`X `Y])])
               (Term.app
                (Term.proj (Term.app `to_glue_r_isometry [`hΦ `hΨ]) "." `comp)
                [(Term.app `isometry_optimal_GH_injr [`Y `Z])])]))
            (calcStep
             («term_≤_»
              (Term.hole "_")
              "≤"
              («term_+_»
               (Term.app
                `Hausdorff_dist
                [(Term.app
                  `range
                  [(«term_∘_»
                    (Term.app `to_glue_l [`hΦ `hΨ])
                    "∘"
                    (Term.app `optimal_GH_injl [`X `Y]))])
                 (Term.app
                  `range
                  [(«term_∘_»
                    (Term.app `to_glue_l [`hΦ `hΨ])
                    "∘"
                    (Term.app `optimal_GH_injr [`X `Y]))])])
               "+"
               (Term.app
                `Hausdorff_dist
                [(Term.app
                  `range
                  [(«term_∘_»
                    (Term.app `to_glue_l [`hΦ `hΨ])
                    "∘"
                    (Term.app `optimal_GH_injr [`X `Y]))])
                 (Term.app
                  `range
                  [(«term_∘_»
                    (Term.app `to_glue_r [`hΦ `hΨ])
                    "∘"
                    (Term.app `optimal_GH_injr [`Y `Z]))])])))
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.refine'
                  "refine'"
                  (Term.app
                   `Hausdorff_dist_triangle
                   [(Term.app
                     `Hausdorff_edist_ne_top_of_nonempty_of_bounded
                     [(Term.app `range_nonempty [(Term.hole "_")])
                      (Term.app `range_nonempty [(Term.hole "_")])
                      (Term.hole "_")
                      (Term.hole "_")])]))
                 []
                 (tactic__
                  (cdotTk (patternIgnore (token.«· » "·")))
                  [(Tactic.exact
                    "exact"
                    (Term.proj
                     (Term.app
                      `is_compact_range
                      [(Term.app
                        `Isometry.continuous
                        [(Term.app
                          (Term.proj (Term.app `to_glue_l_isometry [`hΦ `hΨ]) "." `comp)
                          [(Term.app `isometry_optimal_GH_injl [`X `Y])])])])
                     "."
                     `Bounded))])
                 []
                 (tactic__
                  (cdotTk (patternIgnore (token.«· » "·")))
                  [(Tactic.exact
                    "exact"
                    (Term.proj
                     (Term.app
                      `is_compact_range
                      [(Term.app
                        `Isometry.continuous
                        [(Term.app
                          (Term.proj (Term.app `to_glue_l_isometry [`hΦ `hΨ]) "." `comp)
                          [(Term.app `isometry_optimal_GH_injr [`X `Y])])])])
                     "."
                     `Bounded))])]))))
            (calcStep
             («term_=_»
              (Term.hole "_")
              "="
              («term_+_»
               (Term.app
                `Hausdorff_dist
                [(Set.Data.Set.Image.term_''_
                  (Term.app `to_glue_l [`hΦ `hΨ])
                  " '' "
                  (Term.app `range [(Term.app `optimal_GH_injl [`X `Y])]))
                 (Set.Data.Set.Image.term_''_
                  (Term.app `to_glue_l [`hΦ `hΨ])
                  " '' "
                  (Term.app `range [(Term.app `optimal_GH_injr [`X `Y])]))])
               "+"
               (Term.app
                `Hausdorff_dist
                [(Set.Data.Set.Image.term_''_
                  (Term.app `to_glue_r [`hΦ `hΨ])
                  " '' "
                  (Term.app `range [(Term.app `optimal_GH_injl [`Y `Z])]))
                 (Set.Data.Set.Image.term_''_
                  (Term.app `to_glue_r [`hΦ `hΨ])
                  " '' "
                  (Term.app `range [(Term.app `optimal_GH_injr [`Y `Z])]))])))
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
                   [(Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `range_comp)
                    ","
                    (Tactic.simpLemma [] [] `Comm)
                    ","
                    (Tactic.simpLemma [] [] `eq_self_iff_true)
                    ","
                    (Tactic.simpLemma [] [] `add_right_inj)]
                   "]"]
                  [])]))))
            (calcStep
             («term_=_»
              (Term.hole "_")
              "="
              («term_+_»
               (Term.app
                `Hausdorff_dist
                [(Term.app `range [(Term.app `optimal_GH_injl [`X `Y])])
                 (Term.app `range [(Term.app `optimal_GH_injr [`X `Y])])])
               "+"
               (Term.app
                `Hausdorff_dist
                [(Term.app `range [(Term.app `optimal_GH_injl [`Y `Z])])
                 (Term.app `range [(Term.app `optimal_GH_injr [`Y `Z])])])))
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
                   [(Tactic.rwRule
                     []
                     (Term.app `Hausdorff_dist_image [(Term.app `to_glue_l_isometry [`hΦ `hΨ])]))
                    ","
                    (Tactic.rwRule
                     []
                     (Term.app `Hausdorff_dist_image [(Term.app `to_glue_r_isometry [`hΦ `hΨ])]))]
                   "]")
                  [])]))))
            (calcStep
             («term_=_»
              (Term.hole "_")
              "="
              («term_+_»
               (Term.app `dist [(Term.app `to_GH_space [`X]) (Term.app `to_GH_space [`Y])])
               "+"
               (Term.app `dist [(Term.app `to_GH_space [`Y]) (Term.app `to_GH_space [`Z])])))
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
                   [(Tactic.rwRule [] `Hausdorff_dist_optimal)
                    ","
                    (Tactic.rwRule [] `Hausdorff_dist_optimal)
                    ","
                    (Tactic.rwRule [] `GH_dist)
                    ","
                    (Tactic.rwRule [] `GH_dist)]
                   "]")
                  [])]))))
            (calcStep
             («term_=_»
              (Term.hole "_")
              "="
              («term_+_» (Term.app `dist [`x `y]) "+" (Term.app `dist [`y `z])))
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
                   [(Tactic.rwRule [] `x.to_GH_space_rep)
                    ","
                    (Tactic.rwRule [] `y.to_GH_space_rep)
                    ","
                    (Tactic.rwRule [] `z.to_GH_space_rep)]
                   "]")
                  [])]))))])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (calcTactic
       "calc"
       (calcStep
        («term_=_»
         (Term.app `dist [`x `z])
         "="
         (Term.app `dist [(Term.app `to_GH_space [`X]) (Term.app `to_GH_space [`Z])]))
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
              [(Tactic.rwRule [] `x.to_GH_space_rep) "," (Tactic.rwRule [] `z.to_GH_space_rep)]
              "]")
             [])]))))
       [(calcStep
         («term_≤_»
          (Term.hole "_")
          "≤"
          (Term.app
           `Hausdorff_dist
           [(Term.app
             `range
             [(«term_∘_» (Term.app `to_glue_l [`hΦ `hΨ]) "∘" (Term.app `optimal_GH_injl [`X `Y]))])
            (Term.app
             `range
             [(«term_∘_»
               (Term.app `to_glue_r [`hΦ `hΨ])
               "∘"
               (Term.app `optimal_GH_injr [`Y `Z]))])]))
         ":="
         (Term.app
          `GH_dist_le_Hausdorff_dist
          [(Term.app
            (Term.proj (Term.app `to_glue_l_isometry [`hΦ `hΨ]) "." `comp)
            [(Term.app `isometry_optimal_GH_injl [`X `Y])])
           (Term.app
            (Term.proj (Term.app `to_glue_r_isometry [`hΦ `hΨ]) "." `comp)
            [(Term.app `isometry_optimal_GH_injr [`Y `Z])])]))
        (calcStep
         («term_≤_»
          (Term.hole "_")
          "≤"
          («term_+_»
           (Term.app
            `Hausdorff_dist
            [(Term.app
              `range
              [(«term_∘_» (Term.app `to_glue_l [`hΦ `hΨ]) "∘" (Term.app `optimal_GH_injl [`X `Y]))])
             (Term.app
              `range
              [(«term_∘_»
                (Term.app `to_glue_l [`hΦ `hΨ])
                "∘"
                (Term.app `optimal_GH_injr [`X `Y]))])])
           "+"
           (Term.app
            `Hausdorff_dist
            [(Term.app
              `range
              [(«term_∘_» (Term.app `to_glue_l [`hΦ `hΨ]) "∘" (Term.app `optimal_GH_injr [`X `Y]))])
             (Term.app
              `range
              [(«term_∘_»
                (Term.app `to_glue_r [`hΦ `hΨ])
                "∘"
                (Term.app `optimal_GH_injr [`Y `Z]))])])))
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.refine'
              "refine'"
              (Term.app
               `Hausdorff_dist_triangle
               [(Term.app
                 `Hausdorff_edist_ne_top_of_nonempty_of_bounded
                 [(Term.app `range_nonempty [(Term.hole "_")])
                  (Term.app `range_nonempty [(Term.hole "_")])
                  (Term.hole "_")
                  (Term.hole "_")])]))
             []
             (tactic__
              (cdotTk (patternIgnore (token.«· » "·")))
              [(Tactic.exact
                "exact"
                (Term.proj
                 (Term.app
                  `is_compact_range
                  [(Term.app
                    `Isometry.continuous
                    [(Term.app
                      (Term.proj (Term.app `to_glue_l_isometry [`hΦ `hΨ]) "." `comp)
                      [(Term.app `isometry_optimal_GH_injl [`X `Y])])])])
                 "."
                 `Bounded))])
             []
             (tactic__
              (cdotTk (patternIgnore (token.«· » "·")))
              [(Tactic.exact
                "exact"
                (Term.proj
                 (Term.app
                  `is_compact_range
                  [(Term.app
                    `Isometry.continuous
                    [(Term.app
                      (Term.proj (Term.app `to_glue_l_isometry [`hΦ `hΨ]) "." `comp)
                      [(Term.app `isometry_optimal_GH_injr [`X `Y])])])])
                 "."
                 `Bounded))])]))))
        (calcStep
         («term_=_»
          (Term.hole "_")
          "="
          («term_+_»
           (Term.app
            `Hausdorff_dist
            [(Set.Data.Set.Image.term_''_
              (Term.app `to_glue_l [`hΦ `hΨ])
              " '' "
              (Term.app `range [(Term.app `optimal_GH_injl [`X `Y])]))
             (Set.Data.Set.Image.term_''_
              (Term.app `to_glue_l [`hΦ `hΨ])
              " '' "
              (Term.app `range [(Term.app `optimal_GH_injr [`X `Y])]))])
           "+"
           (Term.app
            `Hausdorff_dist
            [(Set.Data.Set.Image.term_''_
              (Term.app `to_glue_r [`hΦ `hΨ])
              " '' "
              (Term.app `range [(Term.app `optimal_GH_injl [`Y `Z])]))
             (Set.Data.Set.Image.term_''_
              (Term.app `to_glue_r [`hΦ `hΨ])
              " '' "
              (Term.app `range [(Term.app `optimal_GH_injr [`Y `Z])]))])))
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
               [(Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `range_comp)
                ","
                (Tactic.simpLemma [] [] `Comm)
                ","
                (Tactic.simpLemma [] [] `eq_self_iff_true)
                ","
                (Tactic.simpLemma [] [] `add_right_inj)]
               "]"]
              [])]))))
        (calcStep
         («term_=_»
          (Term.hole "_")
          "="
          («term_+_»
           (Term.app
            `Hausdorff_dist
            [(Term.app `range [(Term.app `optimal_GH_injl [`X `Y])])
             (Term.app `range [(Term.app `optimal_GH_injr [`X `Y])])])
           "+"
           (Term.app
            `Hausdorff_dist
            [(Term.app `range [(Term.app `optimal_GH_injl [`Y `Z])])
             (Term.app `range [(Term.app `optimal_GH_injr [`Y `Z])])])))
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
               [(Tactic.rwRule
                 []
                 (Term.app `Hausdorff_dist_image [(Term.app `to_glue_l_isometry [`hΦ `hΨ])]))
                ","
                (Tactic.rwRule
                 []
                 (Term.app `Hausdorff_dist_image [(Term.app `to_glue_r_isometry [`hΦ `hΨ])]))]
               "]")
              [])]))))
        (calcStep
         («term_=_»
          (Term.hole "_")
          "="
          («term_+_»
           (Term.app `dist [(Term.app `to_GH_space [`X]) (Term.app `to_GH_space [`Y])])
           "+"
           (Term.app `dist [(Term.app `to_GH_space [`Y]) (Term.app `to_GH_space [`Z])])))
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
               [(Tactic.rwRule [] `Hausdorff_dist_optimal)
                ","
                (Tactic.rwRule [] `Hausdorff_dist_optimal)
                ","
                (Tactic.rwRule [] `GH_dist)
                ","
                (Tactic.rwRule [] `GH_dist)]
               "]")
              [])]))))
        (calcStep
         («term_=_»
          (Term.hole "_")
          "="
          («term_+_» (Term.app `dist [`x `y]) "+" (Term.app `dist [`y `z])))
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
               [(Tactic.rwRule [] `x.to_GH_space_rep)
                ","
                (Tactic.rwRule [] `y.to_GH_space_rep)
                ","
                (Tactic.rwRule [] `z.to_GH_space_rep)]
               "]")
              [])]))))])
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
            [(Tactic.rwRule [] `x.to_GH_space_rep)
             ","
             (Tactic.rwRule [] `y.to_GH_space_rep)
             ","
             (Tactic.rwRule [] `z.to_GH_space_rep)]
            "]")
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `x.to_GH_space_rep)
         ","
         (Tactic.rwRule [] `y.to_GH_space_rep)
         ","
         (Tactic.rwRule [] `z.to_GH_space_rep)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `z.to_GH_space_rep
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y.to_GH_space_rep
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x.to_GH_space_rep
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Term.hole "_")
       "="
       («term_+_» (Term.app `dist [`x `y]) "+" (Term.app `dist [`y `z])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_» (Term.app `dist [`x `y]) "+" (Term.app `dist [`y `z]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `dist [`y `z])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `z
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `dist
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      (Term.app `dist [`x `y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `dist
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1022, (some 1023, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `Hausdorff_dist_optimal)
             ","
             (Tactic.rwRule [] `Hausdorff_dist_optimal)
             ","
             (Tactic.rwRule [] `GH_dist)
             ","
             (Tactic.rwRule [] `GH_dist)]
            "]")
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `Hausdorff_dist_optimal)
         ","
         (Tactic.rwRule [] `Hausdorff_dist_optimal)
         ","
         (Tactic.rwRule [] `GH_dist)
         ","
         (Tactic.rwRule [] `GH_dist)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `GH_dist
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `GH_dist
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Hausdorff_dist_optimal
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Hausdorff_dist_optimal
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Term.hole "_")
       "="
       («term_+_»
        (Term.app `dist [(Term.app `to_GH_space [`X]) (Term.app `to_GH_space [`Y])])
        "+"
        (Term.app `dist [(Term.app `to_GH_space [`Y]) (Term.app `to_GH_space [`Z])])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_»
       (Term.app `dist [(Term.app `to_GH_space [`X]) (Term.app `to_GH_space [`Y])])
       "+"
       (Term.app `dist [(Term.app `to_GH_space [`Y]) (Term.app `to_GH_space [`Z])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `dist [(Term.app `to_GH_space [`Y]) (Term.app `to_GH_space [`Z])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `to_GH_space [`Z])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Z
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `to_GH_space
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `to_GH_space [`Z]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `to_GH_space [`Y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `to_GH_space
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `to_GH_space [`Y]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `dist
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      (Term.app `dist [(Term.app `to_GH_space [`X]) (Term.app `to_GH_space [`Y])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `to_GH_space [`Y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `to_GH_space
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `to_GH_space [`Y]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `to_GH_space [`X])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `X
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `to_GH_space
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `to_GH_space [`X]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `dist
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1022, (some 1023, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule
              []
              (Term.app `Hausdorff_dist_image [(Term.app `to_glue_l_isometry [`hΦ `hΨ])]))
             ","
             (Tactic.rwRule
              []
              (Term.app `Hausdorff_dist_image [(Term.app `to_glue_r_isometry [`hΦ `hΨ])]))]
            "]")
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule
          []
          (Term.app `Hausdorff_dist_image [(Term.app `to_glue_l_isometry [`hΦ `hΨ])]))
         ","
         (Tactic.rwRule
          []
          (Term.app `Hausdorff_dist_image [(Term.app `to_glue_r_isometry [`hΦ `hΨ])]))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Hausdorff_dist_image [(Term.app `to_glue_r_isometry [`hΦ `hΨ])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `to_glue_r_isometry [`hΦ `hΨ])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hΨ
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hΦ
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `to_glue_r_isometry
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `to_glue_r_isometry [`hΦ `hΨ])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Hausdorff_dist_image
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Hausdorff_dist_image [(Term.app `to_glue_l_isometry [`hΦ `hΨ])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `to_glue_l_isometry [`hΦ `hΨ])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hΨ
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hΦ
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `to_glue_l_isometry
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `to_glue_l_isometry [`hΦ `hΨ])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Hausdorff_dist_image
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Term.hole "_")
       "="
       («term_+_»
        (Term.app
         `Hausdorff_dist
         [(Term.app `range [(Term.app `optimal_GH_injl [`X `Y])])
          (Term.app `range [(Term.app `optimal_GH_injr [`X `Y])])])
        "+"
        (Term.app
         `Hausdorff_dist
         [(Term.app `range [(Term.app `optimal_GH_injl [`Y `Z])])
          (Term.app `range [(Term.app `optimal_GH_injr [`Y `Z])])])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_»
       (Term.app
        `Hausdorff_dist
        [(Term.app `range [(Term.app `optimal_GH_injl [`X `Y])])
         (Term.app `range [(Term.app `optimal_GH_injr [`X `Y])])])
       "+"
       (Term.app
        `Hausdorff_dist
        [(Term.app `range [(Term.app `optimal_GH_injl [`Y `Z])])
         (Term.app `range [(Term.app `optimal_GH_injr [`Y `Z])])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Hausdorff_dist
       [(Term.app `range [(Term.app `optimal_GH_injl [`Y `Z])])
        (Term.app `range [(Term.app `optimal_GH_injr [`Y `Z])])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `range [(Term.app `optimal_GH_injr [`Y `Z])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `optimal_GH_injr [`Y `Z])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Z
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `Y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `optimal_GH_injr
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `optimal_GH_injr [`Y `Z]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `range
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `range [(Term.paren "(" (Term.app `optimal_GH_injr [`Y `Z]) ")")])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `range [(Term.app `optimal_GH_injl [`Y `Z])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `optimal_GH_injl [`Y `Z])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Z
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `Y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `optimal_GH_injl
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `optimal_GH_injl [`Y `Z]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `range
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `range [(Term.paren "(" (Term.app `optimal_GH_injl [`Y `Z]) ")")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Hausdorff_dist
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      (Term.app
       `Hausdorff_dist
       [(Term.app `range [(Term.app `optimal_GH_injl [`X `Y])])
        (Term.app `range [(Term.app `optimal_GH_injr [`X `Y])])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `range [(Term.app `optimal_GH_injr [`X `Y])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `optimal_GH_injr [`X `Y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `X
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `optimal_GH_injr
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `optimal_GH_injr [`X `Y]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `range
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `range [(Term.paren "(" (Term.app `optimal_GH_injr [`X `Y]) ")")])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `range [(Term.app `optimal_GH_injl [`X `Y])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `optimal_GH_injl [`X `Y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `X
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `optimal_GH_injl
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `optimal_GH_injl [`X `Y]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `range
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `range [(Term.paren "(" (Term.app `optimal_GH_injl [`X `Y]) ")")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Hausdorff_dist
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1022, (some 1023, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
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
            [(Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `range_comp)
             ","
             (Tactic.simpLemma [] [] `Comm)
             ","
             (Tactic.simpLemma [] [] `eq_self_iff_true)
             ","
             (Tactic.simpLemma [] [] `add_right_inj)]
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
        [(Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `range_comp)
         ","
         (Tactic.simpLemma [] [] `Comm)
         ","
         (Tactic.simpLemma [] [] `eq_self_iff_true)
         ","
         (Tactic.simpLemma [] [] `add_right_inj)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `add_right_inj
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `eq_self_iff_true
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Comm
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `range_comp
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Term.hole "_")
       "="
       («term_+_»
        (Term.app
         `Hausdorff_dist
         [(Set.Data.Set.Image.term_''_
           (Term.app `to_glue_l [`hΦ `hΨ])
           " '' "
           (Term.app `range [(Term.app `optimal_GH_injl [`X `Y])]))
          (Set.Data.Set.Image.term_''_
           (Term.app `to_glue_l [`hΦ `hΨ])
           " '' "
           (Term.app `range [(Term.app `optimal_GH_injr [`X `Y])]))])
        "+"
        (Term.app
         `Hausdorff_dist
         [(Set.Data.Set.Image.term_''_
           (Term.app `to_glue_r [`hΦ `hΨ])
           " '' "
           (Term.app `range [(Term.app `optimal_GH_injl [`Y `Z])]))
          (Set.Data.Set.Image.term_''_
           (Term.app `to_glue_r [`hΦ `hΨ])
           " '' "
           (Term.app `range [(Term.app `optimal_GH_injr [`Y `Z])]))])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_»
       (Term.app
        `Hausdorff_dist
        [(Set.Data.Set.Image.term_''_
          (Term.app `to_glue_l [`hΦ `hΨ])
          " '' "
          (Term.app `range [(Term.app `optimal_GH_injl [`X `Y])]))
         (Set.Data.Set.Image.term_''_
          (Term.app `to_glue_l [`hΦ `hΨ])
          " '' "
          (Term.app `range [(Term.app `optimal_GH_injr [`X `Y])]))])
       "+"
       (Term.app
        `Hausdorff_dist
        [(Set.Data.Set.Image.term_''_
          (Term.app `to_glue_r [`hΦ `hΨ])
          " '' "
          (Term.app `range [(Term.app `optimal_GH_injl [`Y `Z])]))
         (Set.Data.Set.Image.term_''_
          (Term.app `to_glue_r [`hΦ `hΨ])
          " '' "
          (Term.app `range [(Term.app `optimal_GH_injr [`Y `Z])]))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Hausdorff_dist
       [(Set.Data.Set.Image.term_''_
         (Term.app `to_glue_r [`hΦ `hΨ])
         " '' "
         (Term.app `range [(Term.app `optimal_GH_injl [`Y `Z])]))
        (Set.Data.Set.Image.term_''_
         (Term.app `to_glue_r [`hΦ `hΨ])
         " '' "
         (Term.app `range [(Term.app `optimal_GH_injr [`Y `Z])]))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.Data.Set.Image.term_''_', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.Data.Set.Image.term_''_', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Set.Data.Set.Image.term_''_
       (Term.app `to_glue_r [`hΦ `hΨ])
       " '' "
       (Term.app `range [(Term.app `optimal_GH_injr [`Y `Z])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `range [(Term.app `optimal_GH_injr [`Y `Z])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `optimal_GH_injr [`Y `Z])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Z
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `Y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `optimal_GH_injr
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `optimal_GH_injr [`Y `Z]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `range
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Term.app `to_glue_r [`hΦ `hΨ])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hΨ
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hΦ
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `to_glue_r
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1022, (some 1023, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 80, (some 81, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Set.Data.Set.Image.term_''_
      (Term.app `to_glue_r [`hΦ `hΨ])
      " '' "
      (Term.app `range [(Term.paren "(" (Term.app `optimal_GH_injr [`Y `Z]) ")")]))
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.Data.Set.Image.term_''_', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.Data.Set.Image.term_''_', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Set.Data.Set.Image.term_''_
       (Term.app `to_glue_r [`hΦ `hΨ])
       " '' "
       (Term.app `range [(Term.app `optimal_GH_injl [`Y `Z])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `range [(Term.app `optimal_GH_injl [`Y `Z])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `optimal_GH_injl [`Y `Z])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Z
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `Y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `optimal_GH_injl
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `optimal_GH_injl [`Y `Z]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `range
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Term.app `to_glue_r [`hΦ `hΨ])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hΨ
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hΦ
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `to_glue_r
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1022, (some 1023, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 80, (some 81, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Set.Data.Set.Image.term_''_
      (Term.app `to_glue_r [`hΦ `hΨ])
      " '' "
      (Term.app `range [(Term.paren "(" (Term.app `optimal_GH_injl [`Y `Z]) ")")]))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Hausdorff_dist
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      (Term.app
       `Hausdorff_dist
       [(Set.Data.Set.Image.term_''_
         (Term.app `to_glue_l [`hΦ `hΨ])
         " '' "
         (Term.app `range [(Term.app `optimal_GH_injl [`X `Y])]))
        (Set.Data.Set.Image.term_''_
         (Term.app `to_glue_l [`hΦ `hΨ])
         " '' "
         (Term.app `range [(Term.app `optimal_GH_injr [`X `Y])]))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.Data.Set.Image.term_''_', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.Data.Set.Image.term_''_', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Set.Data.Set.Image.term_''_
       (Term.app `to_glue_l [`hΦ `hΨ])
       " '' "
       (Term.app `range [(Term.app `optimal_GH_injr [`X `Y])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `range [(Term.app `optimal_GH_injr [`X `Y])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `optimal_GH_injr [`X `Y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `X
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `optimal_GH_injr
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `optimal_GH_injr [`X `Y]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `range
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Term.app `to_glue_l [`hΦ `hΨ])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hΨ
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hΦ
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `to_glue_l
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1022, (some 1023, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 80, (some 81, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Set.Data.Set.Image.term_''_
      (Term.app `to_glue_l [`hΦ `hΨ])
      " '' "
      (Term.app `range [(Term.paren "(" (Term.app `optimal_GH_injr [`X `Y]) ")")]))
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.Data.Set.Image.term_''_', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.Data.Set.Image.term_''_', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Set.Data.Set.Image.term_''_
       (Term.app `to_glue_l [`hΦ `hΨ])
       " '' "
       (Term.app `range [(Term.app `optimal_GH_injl [`X `Y])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `range [(Term.app `optimal_GH_injl [`X `Y])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `optimal_GH_injl [`X `Y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `X
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `optimal_GH_injl
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `optimal_GH_injl [`X `Y]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `range
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Term.app `to_glue_l [`hΦ `hΨ])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hΨ
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hΦ
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `to_glue_l
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1022, (some 1023, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 80, (some 81, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Set.Data.Set.Image.term_''_
      (Term.app `to_glue_l [`hΦ `hΨ])
      " '' "
      (Term.app `range [(Term.paren "(" (Term.app `optimal_GH_injl [`X `Y]) ")")]))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Hausdorff_dist
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1022, (some 1023, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.refine'
           "refine'"
           (Term.app
            `Hausdorff_dist_triangle
            [(Term.app
              `Hausdorff_edist_ne_top_of_nonempty_of_bounded
              [(Term.app `range_nonempty [(Term.hole "_")])
               (Term.app `range_nonempty [(Term.hole "_")])
               (Term.hole "_")
               (Term.hole "_")])]))
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.exact
             "exact"
             (Term.proj
              (Term.app
               `is_compact_range
               [(Term.app
                 `Isometry.continuous
                 [(Term.app
                   (Term.proj (Term.app `to_glue_l_isometry [`hΦ `hΨ]) "." `comp)
                   [(Term.app `isometry_optimal_GH_injl [`X `Y])])])])
              "."
              `Bounded))])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.exact
             "exact"
             (Term.proj
              (Term.app
               `is_compact_range
               [(Term.app
                 `Isometry.continuous
                 [(Term.app
                   (Term.proj (Term.app `to_glue_l_isometry [`hΦ `hΨ]) "." `comp)
                   [(Term.app `isometry_optimal_GH_injr [`X `Y])])])])
              "."
              `Bounded))])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.exact
         "exact"
         (Term.proj
          (Term.app
           `is_compact_range
           [(Term.app
             `Isometry.continuous
             [(Term.app
               (Term.proj (Term.app `to_glue_l_isometry [`hΦ `hΨ]) "." `comp)
               [(Term.app `isometry_optimal_GH_injr [`X `Y])])])])
          "."
          `Bounded))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.proj
        (Term.app
         `is_compact_range
         [(Term.app
           `Isometry.continuous
           [(Term.app
             (Term.proj (Term.app `to_glue_l_isometry [`hΦ `hΨ]) "." `comp)
             [(Term.app `isometry_optimal_GH_injr [`X `Y])])])])
        "."
        `Bounded))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj
       (Term.app
        `is_compact_range
        [(Term.app
          `Isometry.continuous
          [(Term.app
            (Term.proj (Term.app `to_glue_l_isometry [`hΦ `hΨ]) "." `comp)
            [(Term.app `isometry_optimal_GH_injr [`X `Y])])])])
       "."
       `Bounded)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       `is_compact_range
       [(Term.app
         `Isometry.continuous
         [(Term.app
           (Term.proj (Term.app `to_glue_l_isometry [`hΦ `hΨ]) "." `comp)
           [(Term.app `isometry_optimal_GH_injr [`X `Y])])])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Isometry.continuous
       [(Term.app
         (Term.proj (Term.app `to_glue_l_isometry [`hΦ `hΨ]) "." `comp)
         [(Term.app `isometry_optimal_GH_injr [`X `Y])])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj (Term.app `to_glue_l_isometry [`hΦ `hΨ]) "." `comp)
       [(Term.app `isometry_optimal_GH_injr [`X `Y])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `isometry_optimal_GH_injr [`X `Y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `X
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `isometry_optimal_GH_injr
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `isometry_optimal_GH_injr [`X `Y])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app `to_glue_l_isometry [`hΦ `hΨ]) "." `comp)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `to_glue_l_isometry [`hΦ `hΨ])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hΨ
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hΦ
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `to_glue_l_isometry
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `to_glue_l_isometry [`hΦ `hΨ])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      (Term.proj (Term.paren "(" (Term.app `to_glue_l_isometry [`hΦ `hΨ]) ")") "." `comp)
      [(Term.paren "(" (Term.app `isometry_optimal_GH_injr [`X `Y]) ")")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Isometry.continuous
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `Isometry.continuous
      [(Term.paren
        "("
        (Term.app
         (Term.proj (Term.paren "(" (Term.app `to_glue_l_isometry [`hΦ `hΨ]) ")") "." `comp)
         [(Term.paren "(" (Term.app `isometry_optimal_GH_injr [`X `Y]) ")")])
        ")")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `is_compact_range
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `is_compact_range
      [(Term.paren
        "("
        (Term.app
         `Isometry.continuous
         [(Term.paren
           "("
           (Term.app
            (Term.proj (Term.paren "(" (Term.app `to_glue_l_isometry [`hΦ `hΨ]) ")") "." `comp)
            [(Term.paren "(" (Term.app `isometry_optimal_GH_injr [`X `Y]) ")")])
           ")")])
        ")")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.exact
         "exact"
         (Term.proj
          (Term.app
           `is_compact_range
           [(Term.app
             `Isometry.continuous
             [(Term.app
               (Term.proj (Term.app `to_glue_l_isometry [`hΦ `hΨ]) "." `comp)
               [(Term.app `isometry_optimal_GH_injl [`X `Y])])])])
          "."
          `Bounded))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.proj
        (Term.app
         `is_compact_range
         [(Term.app
           `Isometry.continuous
           [(Term.app
             (Term.proj (Term.app `to_glue_l_isometry [`hΦ `hΨ]) "." `comp)
             [(Term.app `isometry_optimal_GH_injl [`X `Y])])])])
        "."
        `Bounded))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj
       (Term.app
        `is_compact_range
        [(Term.app
          `Isometry.continuous
          [(Term.app
            (Term.proj (Term.app `to_glue_l_isometry [`hΦ `hΨ]) "." `comp)
            [(Term.app `isometry_optimal_GH_injl [`X `Y])])])])
       "."
       `Bounded)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       `is_compact_range
       [(Term.app
         `Isometry.continuous
         [(Term.app
           (Term.proj (Term.app `to_glue_l_isometry [`hΦ `hΨ]) "." `comp)
           [(Term.app `isometry_optimal_GH_injl [`X `Y])])])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Isometry.continuous
       [(Term.app
         (Term.proj (Term.app `to_glue_l_isometry [`hΦ `hΨ]) "." `comp)
         [(Term.app `isometry_optimal_GH_injl [`X `Y])])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj (Term.app `to_glue_l_isometry [`hΦ `hΨ]) "." `comp)
       [(Term.app `isometry_optimal_GH_injl [`X `Y])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `isometry_optimal_GH_injl [`X `Y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `X
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `isometry_optimal_GH_injl
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `isometry_optimal_GH_injl [`X `Y])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app `to_glue_l_isometry [`hΦ `hΨ]) "." `comp)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `to_glue_l_isometry [`hΦ `hΨ])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hΨ
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hΦ
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `to_glue_l_isometry
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `to_glue_l_isometry [`hΦ `hΨ])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      (Term.proj (Term.paren "(" (Term.app `to_glue_l_isometry [`hΦ `hΨ]) ")") "." `comp)
      [(Term.paren "(" (Term.app `isometry_optimal_GH_injl [`X `Y]) ")")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Isometry.continuous
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `Isometry.continuous
      [(Term.paren
        "("
        (Term.app
         (Term.proj (Term.paren "(" (Term.app `to_glue_l_isometry [`hΦ `hΨ]) ")") "." `comp)
         [(Term.paren "(" (Term.app `isometry_optimal_GH_injl [`X `Y]) ")")])
        ")")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `is_compact_range
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `is_compact_range
      [(Term.paren
        "("
        (Term.app
         `Isometry.continuous
         [(Term.paren
           "("
           (Term.app
            (Term.proj (Term.paren "(" (Term.app `to_glue_l_isometry [`hΦ `hΨ]) ")") "." `comp)
            [(Term.paren "(" (Term.app `isometry_optimal_GH_injl [`X `Y]) ")")])
           ")")])
        ")")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine'
       "refine'"
       (Term.app
        `Hausdorff_dist_triangle
        [(Term.app
          `Hausdorff_edist_ne_top_of_nonempty_of_bounded
          [(Term.app `range_nonempty [(Term.hole "_")])
           (Term.app `range_nonempty [(Term.hole "_")])
           (Term.hole "_")
           (Term.hole "_")])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Hausdorff_dist_triangle
       [(Term.app
         `Hausdorff_edist_ne_top_of_nonempty_of_bounded
         [(Term.app `range_nonempty [(Term.hole "_")])
          (Term.app `range_nonempty [(Term.hole "_")])
          (Term.hole "_")
          (Term.hole "_")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Hausdorff_edist_ne_top_of_nonempty_of_bounded
       [(Term.app `range_nonempty [(Term.hole "_")])
        (Term.app `range_nonempty [(Term.hole "_")])
        (Term.hole "_")
        (Term.hole "_")])
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.app `range_nonempty [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `range_nonempty
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `range_nonempty [(Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `range_nonempty [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `range_nonempty
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `range_nonempty [(Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Hausdorff_edist_ne_top_of_nonempty_of_bounded
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `Hausdorff_edist_ne_top_of_nonempty_of_bounded
      [(Term.paren "(" (Term.app `range_nonempty [(Term.hole "_")]) ")")
       (Term.paren "(" (Term.app `range_nonempty [(Term.hole "_")]) ")")
       (Term.hole "_")
       (Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Hausdorff_dist_triangle
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≤_»
       (Term.hole "_")
       "≤"
       («term_+_»
        (Term.app
         `Hausdorff_dist
         [(Term.app
           `range
           [(«term_∘_» (Term.app `to_glue_l [`hΦ `hΨ]) "∘" (Term.app `optimal_GH_injl [`X `Y]))])
          (Term.app
           `range
           [(«term_∘_» (Term.app `to_glue_l [`hΦ `hΨ]) "∘" (Term.app `optimal_GH_injr [`X `Y]))])])
        "+"
        (Term.app
         `Hausdorff_dist
         [(Term.app
           `range
           [(«term_∘_» (Term.app `to_glue_l [`hΦ `hΨ]) "∘" (Term.app `optimal_GH_injr [`X `Y]))])
          (Term.app
           `range
           [(«term_∘_»
             (Term.app `to_glue_r [`hΦ `hΨ])
             "∘"
             (Term.app `optimal_GH_injr [`Y `Z]))])])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_»
       (Term.app
        `Hausdorff_dist
        [(Term.app
          `range
          [(«term_∘_» (Term.app `to_glue_l [`hΦ `hΨ]) "∘" (Term.app `optimal_GH_injl [`X `Y]))])
         (Term.app
          `range
          [(«term_∘_» (Term.app `to_glue_l [`hΦ `hΨ]) "∘" (Term.app `optimal_GH_injr [`X `Y]))])])
       "+"
       (Term.app
        `Hausdorff_dist
        [(Term.app
          `range
          [(«term_∘_» (Term.app `to_glue_l [`hΦ `hΨ]) "∘" (Term.app `optimal_GH_injr [`X `Y]))])
         (Term.app
          `range
          [(«term_∘_» (Term.app `to_glue_r [`hΦ `hΨ]) "∘" (Term.app `optimal_GH_injr [`Y `Z]))])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Hausdorff_dist
       [(Term.app
         `range
         [(«term_∘_» (Term.app `to_glue_l [`hΦ `hΨ]) "∘" (Term.app `optimal_GH_injr [`X `Y]))])
        (Term.app
         `range
         [(«term_∘_» (Term.app `to_glue_r [`hΦ `hΨ]) "∘" (Term.app `optimal_GH_injr [`Y `Z]))])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `range
       [(«term_∘_» (Term.app `to_glue_r [`hΦ `hΨ]) "∘" (Term.app `optimal_GH_injr [`Y `Z]))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_∘_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_∘_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∘_» (Term.app `to_glue_r [`hΦ `hΨ]) "∘" (Term.app `optimal_GH_injr [`Y `Z]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `optimal_GH_injr [`Y `Z])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Z
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `Y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `optimal_GH_injr
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 90 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 90, term))
      (Term.app `to_glue_r [`hΦ `hΨ])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hΨ
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hΦ
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `to_glue_r
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 91 >? 1022, (some 1023, term) <=? (some 90, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 90, (some 90, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_∘_» (Term.app `to_glue_r [`hΦ `hΨ]) "∘" (Term.app `optimal_GH_injr [`Y `Z]))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `range
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `range
      [(Term.paren
        "("
        («term_∘_» (Term.app `to_glue_r [`hΦ `hΨ]) "∘" (Term.app `optimal_GH_injr [`Y `Z]))
        ")")])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       `range
       [(«term_∘_» (Term.app `to_glue_l [`hΦ `hΨ]) "∘" (Term.app `optimal_GH_injr [`X `Y]))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_∘_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_∘_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∘_» (Term.app `to_glue_l [`hΦ `hΨ]) "∘" (Term.app `optimal_GH_injr [`X `Y]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `optimal_GH_injr [`X `Y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `X
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `optimal_GH_injr
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 90 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 90, term))
      (Term.app `to_glue_l [`hΦ `hΨ])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hΨ
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hΦ
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `to_glue_l
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 91 >? 1022, (some 1023, term) <=? (some 90, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 90, (some 90, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_∘_» (Term.app `to_glue_l [`hΦ `hΨ]) "∘" (Term.app `optimal_GH_injr [`X `Y]))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `range
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `range
      [(Term.paren
        "("
        («term_∘_» (Term.app `to_glue_l [`hΦ `hΨ]) "∘" (Term.app `optimal_GH_injr [`X `Y]))
        ")")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Hausdorff_dist
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      (Term.app
       `Hausdorff_dist
       [(Term.app
         `range
         [(«term_∘_» (Term.app `to_glue_l [`hΦ `hΨ]) "∘" (Term.app `optimal_GH_injl [`X `Y]))])
        (Term.app
         `range
         [(«term_∘_» (Term.app `to_glue_l [`hΦ `hΨ]) "∘" (Term.app `optimal_GH_injr [`X `Y]))])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `range
       [(«term_∘_» (Term.app `to_glue_l [`hΦ `hΨ]) "∘" (Term.app `optimal_GH_injr [`X `Y]))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_∘_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_∘_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∘_» (Term.app `to_glue_l [`hΦ `hΨ]) "∘" (Term.app `optimal_GH_injr [`X `Y]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `optimal_GH_injr [`X `Y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `X
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `optimal_GH_injr
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 90 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 90, term))
      (Term.app `to_glue_l [`hΦ `hΨ])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hΨ
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hΦ
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `to_glue_l
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 91 >? 1022, (some 1023, term) <=? (some 90, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 90, (some 90, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_∘_» (Term.app `to_glue_l [`hΦ `hΨ]) "∘" (Term.app `optimal_GH_injr [`X `Y]))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `range
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `range
      [(Term.paren
        "("
        («term_∘_» (Term.app `to_glue_l [`hΦ `hΨ]) "∘" (Term.app `optimal_GH_injr [`X `Y]))
        ")")])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       `range
       [(«term_∘_» (Term.app `to_glue_l [`hΦ `hΨ]) "∘" (Term.app `optimal_GH_injl [`X `Y]))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_∘_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_∘_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∘_» (Term.app `to_glue_l [`hΦ `hΨ]) "∘" (Term.app `optimal_GH_injl [`X `Y]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `optimal_GH_injl [`X `Y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `X
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `optimal_GH_injl
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 90 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 90, term))
      (Term.app `to_glue_l [`hΦ `hΨ])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hΨ
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hΦ
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `to_glue_l
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 91 >? 1022, (some 1023, term) <=? (some 90, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 90, (some 90, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_∘_» (Term.app `to_glue_l [`hΦ `hΨ]) "∘" (Term.app `optimal_GH_injl [`X `Y]))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `range
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `range
      [(Term.paren
        "("
        («term_∘_» (Term.app `to_glue_l [`hΦ `hΨ]) "∘" (Term.app `optimal_GH_injl [`X `Y]))
        ")")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Hausdorff_dist
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1022, (some 1023, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
      (Term.app
       `GH_dist_le_Hausdorff_dist
       [(Term.app
         (Term.proj (Term.app `to_glue_l_isometry [`hΦ `hΨ]) "." `comp)
         [(Term.app `isometry_optimal_GH_injl [`X `Y])])
        (Term.app
         (Term.proj (Term.app `to_glue_r_isometry [`hΦ `hΨ]) "." `comp)
         [(Term.app `isometry_optimal_GH_injr [`Y `Z])])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj (Term.app `to_glue_r_isometry [`hΦ `hΨ]) "." `comp)
       [(Term.app `isometry_optimal_GH_injr [`Y `Z])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `isometry_optimal_GH_injr [`Y `Z])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Z
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `Y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `isometry_optimal_GH_injr
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `isometry_optimal_GH_injr [`Y `Z])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app `to_glue_r_isometry [`hΦ `hΨ]) "." `comp)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `to_glue_r_isometry [`hΦ `hΨ])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hΨ
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hΦ
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `to_glue_r_isometry
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `to_glue_r_isometry [`hΦ `hΨ])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      (Term.proj (Term.paren "(" (Term.app `to_glue_r_isometry [`hΦ `hΨ]) ")") "." `comp)
      [(Term.paren "(" (Term.app `isometry_optimal_GH_injr [`Y `Z]) ")")])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       (Term.proj (Term.app `to_glue_l_isometry [`hΦ `hΨ]) "." `comp)
       [(Term.app `isometry_optimal_GH_injl [`X `Y])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `isometry_optimal_GH_injl [`X `Y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `X
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `isometry_optimal_GH_injl
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `isometry_optimal_GH_injl [`X `Y])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app `to_glue_l_isometry [`hΦ `hΨ]) "." `comp)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `to_glue_l_isometry [`hΦ `hΨ])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hΨ
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hΦ
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `to_glue_l_isometry
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `to_glue_l_isometry [`hΦ `hΨ])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      (Term.proj (Term.paren "(" (Term.app `to_glue_l_isometry [`hΦ `hΨ]) ")") "." `comp)
      [(Term.paren "(" (Term.app `isometry_optimal_GH_injl [`X `Y]) ")")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `GH_dist_le_Hausdorff_dist
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≤_»
       (Term.hole "_")
       "≤"
       (Term.app
        `Hausdorff_dist
        [(Term.app
          `range
          [(«term_∘_» (Term.app `to_glue_l [`hΦ `hΨ]) "∘" (Term.app `optimal_GH_injl [`X `Y]))])
         (Term.app
          `range
          [(«term_∘_» (Term.app `to_glue_r [`hΦ `hΨ]) "∘" (Term.app `optimal_GH_injr [`Y `Z]))])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Hausdorff_dist
       [(Term.app
         `range
         [(«term_∘_» (Term.app `to_glue_l [`hΦ `hΨ]) "∘" (Term.app `optimal_GH_injl [`X `Y]))])
        (Term.app
         `range
         [(«term_∘_» (Term.app `to_glue_r [`hΦ `hΨ]) "∘" (Term.app `optimal_GH_injr [`Y `Z]))])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `range
       [(«term_∘_» (Term.app `to_glue_r [`hΦ `hΨ]) "∘" (Term.app `optimal_GH_injr [`Y `Z]))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_∘_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_∘_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∘_» (Term.app `to_glue_r [`hΦ `hΨ]) "∘" (Term.app `optimal_GH_injr [`Y `Z]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `optimal_GH_injr [`Y `Z])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Z
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `Y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `optimal_GH_injr
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 90 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 90, term))
      (Term.app `to_glue_r [`hΦ `hΨ])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hΨ
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hΦ
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `to_glue_r
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 91 >? 1022, (some 1023, term) <=? (some 90, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 90, (some 90, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_∘_» (Term.app `to_glue_r [`hΦ `hΨ]) "∘" (Term.app `optimal_GH_injr [`Y `Z]))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `range
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `range
      [(Term.paren
        "("
        («term_∘_» (Term.app `to_glue_r [`hΦ `hΨ]) "∘" (Term.app `optimal_GH_injr [`Y `Z]))
        ")")])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       `range
       [(«term_∘_» (Term.app `to_glue_l [`hΦ `hΨ]) "∘" (Term.app `optimal_GH_injl [`X `Y]))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_∘_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_∘_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∘_» (Term.app `to_glue_l [`hΦ `hΨ]) "∘" (Term.app `optimal_GH_injl [`X `Y]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `optimal_GH_injl [`X `Y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `X
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `optimal_GH_injl
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 90 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 90, term))
      (Term.app `to_glue_l [`hΦ `hΨ])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hΨ
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hΦ
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `to_glue_l
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 91 >? 1022, (some 1023, term) <=? (some 90, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 90, (some 90, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_∘_» (Term.app `to_glue_l [`hΦ `hΨ]) "∘" (Term.app `optimal_GH_injl [`X `Y]))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `range
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `range
      [(Term.paren
        "("
        («term_∘_» (Term.app `to_glue_l [`hΦ `hΨ]) "∘" (Term.app `optimal_GH_injl [`X `Y]))
        ")")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Hausdorff_dist
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `x.to_GH_space_rep) "," (Tactic.rwRule [] `z.to_GH_space_rep)]
            "]")
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `x.to_GH_space_rep) "," (Tactic.rwRule [] `z.to_GH_space_rep)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `z.to_GH_space_rep
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x.to_GH_space_rep
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Term.app `dist [`x `z])
       "="
       (Term.app `dist [(Term.app `to_GH_space [`X]) (Term.app `to_GH_space [`Z])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `dist [(Term.app `to_GH_space [`X]) (Term.app `to_GH_space [`Z])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `to_GH_space [`Z])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Z
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `to_GH_space
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `to_GH_space [`Z]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `to_GH_space [`X])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `X
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `to_GH_space
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `to_GH_space [`X]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `dist
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app `dist [`x `z])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `z
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `dist
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`Comm []]
         [(Term.typeSpec
           ":"
           («term_=_»
            («term_∘_» (Term.app `to_glue_l [`hΦ `hΨ]) "∘" (Term.app `optimal_GH_injr [`X `Y]))
            "="
            («term_∘_» (Term.app `to_glue_r [`hΦ `hΨ]) "∘" (Term.app `optimal_GH_injl [`Y `Z]))))]
         ":="
         (Term.app `to_glue_commute [`hΦ `hΨ]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `to_glue_commute [`hΦ `hΨ])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hΨ
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hΦ
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `to_glue_commute
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       («term_∘_» (Term.app `to_glue_l [`hΦ `hΨ]) "∘" (Term.app `optimal_GH_injr [`X `Y]))
       "="
       («term_∘_» (Term.app `to_glue_r [`hΦ `hΨ]) "∘" (Term.app `optimal_GH_injl [`Y `Z])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∘_» (Term.app `to_glue_r [`hΦ `hΨ]) "∘" (Term.app `optimal_GH_injl [`Y `Z]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `optimal_GH_injl [`Y `Z])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Z
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `Y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `optimal_GH_injl
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 90 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 90, term))
      (Term.app `to_glue_r [`hΦ `hΨ])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hΨ
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hΦ
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `to_glue_r
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 91 >? 1022, (some 1023, term) <=? (some 90, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 90, (some 90, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      («term_∘_» (Term.app `to_glue_l [`hΦ `hΨ]) "∘" (Term.app `optimal_GH_injr [`X `Y]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `optimal_GH_injr [`X `Y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `X
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `optimal_GH_injr
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 90 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 90, term))
      (Term.app `to_glue_l [`hΦ `hΨ])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hΨ
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hΦ
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `to_glue_l
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 91 >? 1022, (some 1023, term) <=? (some 90, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 90, (some 90, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.tacticLetI_
       "letI"
       (Term.haveDecl
        (Term.haveIdDecl
         []
         [(Term.typeSpec ":" (Term.app `MetricSpace [`γ]))]
         ":="
         (Term.app `Metric.metricSpaceGlueSpace [`hΦ `hΨ]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Metric.metricSpaceGlueSpace [`hΦ `hΨ])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hΨ
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hΦ
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Metric.metricSpaceGlueSpace
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `MetricSpace [`γ])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `γ
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `MetricSpace
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticLet_
       "let"
       (Term.letDecl (Term.letIdDecl `γ [] [] ":=" (Term.app `glue_space [`hΦ `hΨ]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `glue_space [`hΦ `hΨ])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hΨ
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hΦ
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `glue_space
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`hΨ []]
         [(Term.typeSpec ":" (Term.app `Isometry [`Ψ]))]
         ":="
         (Term.app `isometry_optimal_GH_injl [`Y `Z]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `isometry_optimal_GH_injl [`Y `Z])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Z
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `Y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `isometry_optimal_GH_injl
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Isometry [`Ψ])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Ψ
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Isometry
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticLet_
       "let"
       (Term.letDecl
        (Term.letIdDecl
         `Ψ
         []
         [(Term.typeSpec ":" (Term.arrow `Y "→" `γ2))]
         ":="
         (Term.app `optimal_GH_injl [`Y `Z]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `optimal_GH_injl [`Y `Z])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Z
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `Y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `optimal_GH_injl
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.arrow `Y "→" `γ2)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `γ2
[PrettyPrinter.parenthesize] ...precedences are 25 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
      `Y
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 25, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 25, (some 25, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`hΦ []]
         [(Term.typeSpec ":" (Term.app `Isometry [`Φ]))]
         ":="
         (Term.app `isometry_optimal_GH_injr [`X `Y]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `isometry_optimal_GH_injr [`X `Y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `X
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `isometry_optimal_GH_injr
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Isometry [`Φ])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Φ
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Isometry
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticLet_
       "let"
       (Term.letDecl
        (Term.letIdDecl
         `Φ
         []
         [(Term.typeSpec ":" (Term.arrow `Y "→" `γ1))]
         ":="
         (Term.app `optimal_GH_injr [`X `Y]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `optimal_GH_injr [`X `Y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `X
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `optimal_GH_injr
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.arrow `Y "→" `γ1)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `γ1
[PrettyPrinter.parenthesize] ...precedences are 25 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
      `Y
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 25, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 25, (some 25, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticLet_
       "let"
       (Term.letDecl (Term.letIdDecl `γ2 [] [] ":=" (Term.app `optimal_GH_coupling [`Y `Z]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `optimal_GH_coupling [`Y `Z])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Z
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `Y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `optimal_GH_coupling
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticLet_
       "let"
       (Term.letDecl (Term.letIdDecl `γ1 [] [] ":=" (Term.app `optimal_GH_coupling [`X `Y]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `optimal_GH_coupling [`X `Y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `X
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `optimal_GH_coupling
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticLet_ "let" (Term.letDecl (Term.letIdDecl `Z [] [] ":=" `z.rep)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `z.rep
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticLet_ "let" (Term.letDecl (Term.letIdDecl `Y [] [] ":=" `y.rep)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y.rep
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticLet_ "let" (Term.letDecl (Term.letIdDecl `X [] [] ":=" `x.rep)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x.rep
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Std.Tactic.rcases
           "rcases"
           [(Tactic.casesTarget [] (Term.app `GH_dist_eq_Hausdorff_dist [`x.rep `y.rep]))]
           ["with"
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed
              [(Std.Tactic.RCases.rcasesPat.tuple
                "⟨"
                [(Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `Φ)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `Ψ)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `Φisom)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `Ψisom)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `DΦΨ)])
                  [])]
                "⟩")])
             [])])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `dist_GH_dist)
             ","
             (Tactic.rwRule [] `hxy)]
            "]")
           [(Tactic.location "at" (Tactic.locationHyp [`DΦΨ] []))])
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             []
             [(Term.typeSpec ":" («term_=_» (Term.app `range [`Φ]) "=" (Term.app `range [`Ψ])))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.tacticHave_
                  "have"
                  (Term.haveDecl
                   (Term.haveIdDecl
                    [`hΦ []]
                    [(Term.typeSpec ":" (Term.app `IsCompact [(Term.app `range [`Φ])]))]
                    ":="
                    (Term.app `is_compact_range [`Φisom.continuous]))))
                 []
                 (Tactic.tacticHave_
                  "have"
                  (Term.haveDecl
                   (Term.haveIdDecl
                    [`hΨ []]
                    [(Term.typeSpec ":" (Term.app `IsCompact [(Term.app `range [`Ψ])]))]
                    ":="
                    (Term.app `is_compact_range [`Ψisom.continuous]))))
                 []
                 (Tactic.apply
                  "apply"
                  (Term.app
                   (Term.proj
                    (Term.app
                     `IsClosed.Hausdorff_dist_zero_iff_eq
                     [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
                    "."
                    (fieldIdx "1"))
                   [`DΦΨ.symm]))
                 []
                 (tactic__
                  (cdotTk (patternIgnore (token.«· » "·")))
                  [(Tactic.exact "exact" `hΦ.is_closed)])
                 []
                 (tactic__
                  (cdotTk (patternIgnore (token.«· » "·")))
                  [(Tactic.exact "exact" `hΨ.is_closed)])
                 []
                 (tactic__
                  (cdotTk (patternIgnore (token.«· » "·")))
                  [(Tactic.exact
                    "exact"
                    (Term.app
                     `Hausdorff_edist_ne_top_of_nonempty_of_bounded
                     [(Term.app `range_nonempty [(Term.hole "_")])
                      (Term.app `range_nonempty [(Term.hole "_")])
                      `hΦ.bounded
                      `hΨ.bounded]))])]))))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`T []]
             [(Term.typeSpec
               ":"
               («term_=_»
                (Topology.MetricSpace.Isometry.«term_≃ᵢ_» (Term.app `range [`Ψ]) " ≃ᵢ " `y.rep)
                "="
                (Topology.MetricSpace.Isometry.«term_≃ᵢ_» (Term.app `range [`Φ]) " ≃ᵢ " `y.rep)))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `this)] "]")
                  [])]))))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`eΨ []]
             []
             ":="
             (Term.app `cast [`T `Ψisom.isometric_on_range.symm]))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl [`e []] [] ":=" (Term.app `Φisom.isometric_on_range.trans [`eΨ]))))
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `x.to_GH_space_rep)
             ","
             (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `y.to_GH_space_rep)
             ","
             (Tactic.rwRule [] `to_GH_space_eq_to_GH_space_iff_isometric)]
            "]")
           [])
          []
          (Tactic.exact "exact" (Term.anonymousCtor "⟨" [`e] "⟩"))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" (Term.anonymousCtor "⟨" [`e] "⟩"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [`e] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `e
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `x.to_GH_space_rep)
         ","
         (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `y.to_GH_space_rep)
         ","
         (Tactic.rwRule [] `to_GH_space_eq_to_GH_space_iff_isometric)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `to_GH_space_eq_to_GH_space_iff_isometric
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y.to_GH_space_rep
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x.to_GH_space_rep
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl [`e []] [] ":=" (Term.app `Φisom.isometric_on_range.trans [`eΨ]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Φisom.isometric_on_range.trans [`eΨ])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `eΨ
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Φisom.isometric_on_range.trans
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl [`eΨ []] [] ":=" (Term.app `cast [`T `Ψisom.isometric_on_range.symm]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `cast [`T `Ψisom.isometric_on_range.symm])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Ψisom.isometric_on_range.symm
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `T
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `cast
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`T []]
         [(Term.typeSpec
           ":"
           («term_=_»
            (Topology.MetricSpace.Isometry.«term_≃ᵢ_» (Term.app `range [`Ψ]) " ≃ᵢ " `y.rep)
            "="
            (Topology.MetricSpace.Isometry.«term_≃ᵢ_» (Term.app `range [`Φ]) " ≃ᵢ " `y.rep)))]
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `this)] "]") [])]))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `this)] "]") [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `this)] "]") [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `this
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Topology.MetricSpace.Isometry.«term_≃ᵢ_» (Term.app `range [`Ψ]) " ≃ᵢ " `y.rep)
       "="
       (Topology.MetricSpace.Isometry.«term_≃ᵢ_» (Term.app `range [`Φ]) " ≃ᵢ " `y.rep))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Topology.MetricSpace.Isometry.«term_≃ᵢ_» (Term.app `range [`Φ]) " ≃ᵢ " `y.rep)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y.rep
[PrettyPrinter.parenthesize] ...precedences are 26 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
      (Term.app `range [`Φ])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Φ
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `range
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 25 >? 1022, (some 1023, term) <=? (some 25, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 25, (some 26, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Topology.MetricSpace.Isometry.«term_≃ᵢ_» (Term.app `range [`Φ]) " ≃ᵢ " `y.rep)
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Topology.MetricSpace.Isometry.«term_≃ᵢ_» (Term.app `range [`Ψ]) " ≃ᵢ " `y.rep)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y.rep
[PrettyPrinter.parenthesize] ...precedences are 26 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
      (Term.app `range [`Ψ])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Ψ
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `range
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 25 >? 1022, (some 1023, term) <=? (some 25, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 25, (some 26, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Topology.MetricSpace.Isometry.«term_≃ᵢ_» (Term.app `range [`Ψ]) " ≃ᵢ " `y.rep)
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         []
         [(Term.typeSpec ":" («term_=_» (Term.app `range [`Φ]) "=" (Term.app `range [`Ψ])))]
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                [`hΦ []]
                [(Term.typeSpec ":" (Term.app `IsCompact [(Term.app `range [`Φ])]))]
                ":="
                (Term.app `is_compact_range [`Φisom.continuous]))))
             []
             (Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                [`hΨ []]
                [(Term.typeSpec ":" (Term.app `IsCompact [(Term.app `range [`Ψ])]))]
                ":="
                (Term.app `is_compact_range [`Ψisom.continuous]))))
             []
             (Tactic.apply
              "apply"
              (Term.app
               (Term.proj
                (Term.app
                 `IsClosed.Hausdorff_dist_zero_iff_eq
                 [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
                "."
                (fieldIdx "1"))
               [`DΦΨ.symm]))
             []
             (tactic__
              (cdotTk (patternIgnore (token.«· » "·")))
              [(Tactic.exact "exact" `hΦ.is_closed)])
             []
             (tactic__
              (cdotTk (patternIgnore (token.«· » "·")))
              [(Tactic.exact "exact" `hΨ.is_closed)])
             []
             (tactic__
              (cdotTk (patternIgnore (token.«· » "·")))
              [(Tactic.exact
                "exact"
                (Term.app
                 `Hausdorff_edist_ne_top_of_nonempty_of_bounded
                 [(Term.app `range_nonempty [(Term.hole "_")])
                  (Term.app `range_nonempty [(Term.hole "_")])
                  `hΦ.bounded
                  `hΨ.bounded]))])]))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`hΦ []]
             [(Term.typeSpec ":" (Term.app `IsCompact [(Term.app `range [`Φ])]))]
             ":="
             (Term.app `is_compact_range [`Φisom.continuous]))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`hΨ []]
             [(Term.typeSpec ":" (Term.app `IsCompact [(Term.app `range [`Ψ])]))]
             ":="
             (Term.app `is_compact_range [`Ψisom.continuous]))))
          []
          (Tactic.apply
           "apply"
           (Term.app
            (Term.proj
             (Term.app
              `IsClosed.Hausdorff_dist_zero_iff_eq
              [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
             "."
             (fieldIdx "1"))
            [`DΦΨ.symm]))
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.exact "exact" `hΦ.is_closed)])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.exact "exact" `hΨ.is_closed)])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.exact
             "exact"
             (Term.app
              `Hausdorff_edist_ne_top_of_nonempty_of_bounded
              [(Term.app `range_nonempty [(Term.hole "_")])
               (Term.app `range_nonempty [(Term.hole "_")])
               `hΦ.bounded
               `hΨ.bounded]))])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.exact
         "exact"
         (Term.app
          `Hausdorff_edist_ne_top_of_nonempty_of_bounded
          [(Term.app `range_nonempty [(Term.hole "_")])
           (Term.app `range_nonempty [(Term.hole "_")])
           `hΦ.bounded
           `hΨ.bounded]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.app
        `Hausdorff_edist_ne_top_of_nonempty_of_bounded
        [(Term.app `range_nonempty [(Term.hole "_")])
         (Term.app `range_nonempty [(Term.hole "_")])
         `hΦ.bounded
         `hΨ.bounded]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Hausdorff_edist_ne_top_of_nonempty_of_bounded
       [(Term.app `range_nonempty [(Term.hole "_")])
        (Term.app `range_nonempty [(Term.hole "_")])
        `hΦ.bounded
        `hΨ.bounded])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hΨ.bounded
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hΦ.bounded
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `range_nonempty [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `range_nonempty
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `range_nonempty [(Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `range_nonempty [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `range_nonempty
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `range_nonempty [(Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Hausdorff_edist_ne_top_of_nonempty_of_bounded
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__ (cdotTk (patternIgnore (token.«· » "·"))) [(Tactic.exact "exact" `hΨ.is_closed)])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" `hΨ.is_closed)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hΨ.is_closed
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__ (cdotTk (patternIgnore (token.«· » "·"))) [(Tactic.exact "exact" `hΦ.is_closed)])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" `hΦ.is_closed)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hΦ.is_closed
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.apply
       "apply"
       (Term.app
        (Term.proj
         (Term.app
          `IsClosed.Hausdorff_dist_zero_iff_eq
          [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
         "."
         (fieldIdx "1"))
        [`DΦΨ.symm]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (Term.app
         `IsClosed.Hausdorff_dist_zero_iff_eq
         [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
        "."
        (fieldIdx "1"))
       [`DΦΨ.symm])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `DΦΨ.symm
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (Term.app
        `IsClosed.Hausdorff_dist_zero_iff_eq
        [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
       "."
       (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       `IsClosed.Hausdorff_dist_zero_iff_eq
       [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
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
      `IsClosed.Hausdorff_dist_zero_iff_eq
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `IsClosed.Hausdorff_dist_zero_iff_eq
      [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
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
         [`hΨ []]
         [(Term.typeSpec ":" (Term.app `IsCompact [(Term.app `range [`Ψ])]))]
         ":="
         (Term.app `is_compact_range [`Ψisom.continuous]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `is_compact_range [`Ψisom.continuous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Ψisom.continuous
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `is_compact_range
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `IsCompact [(Term.app `range [`Ψ])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `range [`Ψ])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Ψ
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `range
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `range [`Ψ]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `IsCompact
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`hΦ []]
         [(Term.typeSpec ":" (Term.app `IsCompact [(Term.app `range [`Φ])]))]
         ":="
         (Term.app `is_compact_range [`Φisom.continuous]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `is_compact_range [`Φisom.continuous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Φisom.continuous
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `is_compact_range
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `IsCompact [(Term.app `range [`Φ])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `range [`Φ])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Φ
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `range
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `range [`Φ]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `IsCompact
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_» (Term.app `range [`Φ]) "=" (Term.app `range [`Ψ]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `range [`Ψ])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Ψ
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `range
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app `range [`Φ])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Φ
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `range
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `dist_GH_dist)
         ","
         (Tactic.rwRule [] `hxy)]
        "]")
       [(Tactic.location "at" (Tactic.locationHyp [`DΦΨ] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `DΦΨ
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hxy
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `dist_GH_dist
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.rcases
       "rcases"
       [(Tactic.casesTarget [] (Term.app `GH_dist_eq_Hausdorff_dist [`x.rep `y.rep]))]
       ["with"
        (Std.Tactic.RCases.rcasesPatLo
         (Std.Tactic.RCases.rcasesPatMed
          [(Std.Tactic.RCases.rcasesPat.tuple
            "⟨"
            [(Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `Φ)])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `Ψ)])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `Φisom)])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `Ψisom)])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `DΦΨ)])
              [])]
            "⟩")])
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `GH_dist_eq_Hausdorff_dist [`x.rep `y.rep])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y.rep
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x.rep
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `GH_dist_eq_Hausdorff_dist
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`A []]
             [(Term.typeSpec
               ":"
               («term_=_»
                (Set.Data.Set.Image.term_''_
                 (Term.fun
                  "fun"
                  (Term.basicFun
                   [`p]
                   [(Term.typeSpec
                     ":"
                     («term_×_»
                      (Term.app
                       `nonempty_compacts
                       [(Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ "ℓ_infty_ℝ")])
                      "×"
                      (Term.app
                       `nonempty_compacts
                       [(Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ "ℓ_infty_ℝ")])))]
                   "=>"
                   (Term.app
                    `Hausdorff_dist
                    [(Term.typeAscription
                      "("
                      (Term.proj `p "." (fieldIdx "1"))
                      ":"
                      [(Term.app
                        `Set
                        [(Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ "ℓ_infty_ℝ")])]
                      ")")
                     (Term.proj `p "." (fieldIdx "2"))])))
                 " '' "
                 (LowerSet.Order.UpperLower.lower_set.prod
                  (Set.«term{_|_}»
                   "{"
                   (Std.ExtendedBinder.extBinder (Lean.binderIdent `a) [])
                   "|"
                   («term_=_» (Quotient.Init.Data.Quot.«term⟦_⟧» "⟦" `a "⟧") "=" `x)
                   "}")
                  " ×ˢ "
                  (Set.«term{_|_}»
                   "{"
                   (Std.ExtendedBinder.extBinder (Lean.binderIdent `b) [])
                   "|"
                   («term_=_» (Quotient.Init.Data.Quot.«term⟦_⟧» "⟦" `b "⟧") "=" `y)
                   "}")))
                "="
                (Set.Data.Set.Image.term_''_
                 («term_∘_»
                  (Term.fun
                   "fun"
                   (Term.basicFun
                    [`p]
                    [(Term.typeSpec
                      ":"
                      («term_×_»
                       (Term.app
                        `nonempty_compacts
                        [(Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ "ℓ_infty_ℝ")])
                       "×"
                       (Term.app
                        `nonempty_compacts
                        [(Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ "ℓ_infty_ℝ")])))]
                    "=>"
                    (Term.app
                     `Hausdorff_dist
                     [(Term.typeAscription
                       "("
                       (Term.proj `p "." (fieldIdx "1"))
                       ":"
                       [(Term.app
                         `Set
                         [(Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ "ℓ_infty_ℝ")])]
                       ")")
                      (Term.proj `p "." (fieldIdx "2"))])))
                  "∘"
                  `Prod.swap)
                 " '' "
                 (LowerSet.Order.UpperLower.lower_set.prod
                  (Set.«term{_|_}»
                   "{"
                   (Std.ExtendedBinder.extBinder (Lean.binderIdent `a) [])
                   "|"
                   («term_=_» (Quotient.Init.Data.Quot.«term⟦_⟧» "⟦" `a "⟧") "=" `x)
                   "}")
                  " ×ˢ "
                  (Set.«term{_|_}»
                   "{"
                   (Std.ExtendedBinder.extBinder (Lean.binderIdent `b) [])
                   "|"
                   («term_=_» (Quotient.Init.Data.Quot.«term⟦_⟧» "⟦" `b "⟧") "=" `y)
                   "}")))))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.congr "congr" [])
                 []
                 (tacticFunext__ "funext" [])
                 []
                 (Tactic.simp
                  "simp"
                  []
                  []
                  ["only"]
                  ["["
                   [(Tactic.simpLemma [] [] `comp_app)
                    ","
                    (Tactic.simpLemma [] [] `Prod.fst_swap)
                    ","
                    (Tactic.simpLemma [] [] `Prod.snd_swap)]
                   "]"]
                  [])
                 []
                 (Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Hausdorff_dist_comm)] "]")
                  [])]))))))
          []
          (Tactic.simp
           "simp"
           []
           []
           ["only"]
           ["["
            [(Tactic.simpLemma [] [] `dist)
             ","
             (Tactic.simpLemma [] [] `A)
             ","
             (Tactic.simpLemma [] [] `image_comp)
             ","
             (Tactic.simpLemma [] [] `image_swap_prod)]
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
        [(Tactic.simpLemma [] [] `dist)
         ","
         (Tactic.simpLemma [] [] `A)
         ","
         (Tactic.simpLemma [] [] `image_comp)
         ","
         (Tactic.simpLemma [] [] `image_swap_prod)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `image_swap_prod
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `image_comp
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `A
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `dist
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`A []]
         [(Term.typeSpec
           ":"
           («term_=_»
            (Set.Data.Set.Image.term_''_
             (Term.fun
              "fun"
              (Term.basicFun
               [`p]
               [(Term.typeSpec
                 ":"
                 («term_×_»
                  (Term.app
                   `nonempty_compacts
                   [(Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ "ℓ_infty_ℝ")])
                  "×"
                  (Term.app
                   `nonempty_compacts
                   [(Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ "ℓ_infty_ℝ")])))]
               "=>"
               (Term.app
                `Hausdorff_dist
                [(Term.typeAscription
                  "("
                  (Term.proj `p "." (fieldIdx "1"))
                  ":"
                  [(Term.app
                    `Set
                    [(Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ "ℓ_infty_ℝ")])]
                  ")")
                 (Term.proj `p "." (fieldIdx "2"))])))
             " '' "
             (LowerSet.Order.UpperLower.lower_set.prod
              (Set.«term{_|_}»
               "{"
               (Std.ExtendedBinder.extBinder (Lean.binderIdent `a) [])
               "|"
               («term_=_» (Quotient.Init.Data.Quot.«term⟦_⟧» "⟦" `a "⟧") "=" `x)
               "}")
              " ×ˢ "
              (Set.«term{_|_}»
               "{"
               (Std.ExtendedBinder.extBinder (Lean.binderIdent `b) [])
               "|"
               («term_=_» (Quotient.Init.Data.Quot.«term⟦_⟧» "⟦" `b "⟧") "=" `y)
               "}")))
            "="
            (Set.Data.Set.Image.term_''_
             («term_∘_»
              (Term.fun
               "fun"
               (Term.basicFun
                [`p]
                [(Term.typeSpec
                  ":"
                  («term_×_»
                   (Term.app
                    `nonempty_compacts
                    [(Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ "ℓ_infty_ℝ")])
                   "×"
                   (Term.app
                    `nonempty_compacts
                    [(Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ "ℓ_infty_ℝ")])))]
                "=>"
                (Term.app
                 `Hausdorff_dist
                 [(Term.typeAscription
                   "("
                   (Term.proj `p "." (fieldIdx "1"))
                   ":"
                   [(Term.app
                     `Set
                     [(Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ "ℓ_infty_ℝ")])]
                   ")")
                  (Term.proj `p "." (fieldIdx "2"))])))
              "∘"
              `Prod.swap)
             " '' "
             (LowerSet.Order.UpperLower.lower_set.prod
              (Set.«term{_|_}»
               "{"
               (Std.ExtendedBinder.extBinder (Lean.binderIdent `a) [])
               "|"
               («term_=_» (Quotient.Init.Data.Quot.«term⟦_⟧» "⟦" `a "⟧") "=" `x)
               "}")
              " ×ˢ "
              (Set.«term{_|_}»
               "{"
               (Std.ExtendedBinder.extBinder (Lean.binderIdent `b) [])
               "|"
               («term_=_» (Quotient.Init.Data.Quot.«term⟦_⟧» "⟦" `b "⟧") "=" `y)
               "}")))))]
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.congr "congr" [])
             []
             (tacticFunext__ "funext" [])
             []
             (Tactic.simp
              "simp"
              []
              []
              ["only"]
              ["["
               [(Tactic.simpLemma [] [] `comp_app)
                ","
                (Tactic.simpLemma [] [] `Prod.fst_swap)
                ","
                (Tactic.simpLemma [] [] `Prod.snd_swap)]
               "]"]
              [])
             []
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Hausdorff_dist_comm)] "]")
              [])]))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.congr "congr" [])
          []
          (tacticFunext__ "funext" [])
          []
          (Tactic.simp
           "simp"
           []
           []
           ["only"]
           ["["
            [(Tactic.simpLemma [] [] `comp_app)
             ","
             (Tactic.simpLemma [] [] `Prod.fst_swap)
             ","
             (Tactic.simpLemma [] [] `Prod.snd_swap)]
            "]"]
           [])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Hausdorff_dist_comm)] "]")
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Hausdorff_dist_comm)] "]") [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Hausdorff_dist_comm
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
        [(Tactic.simpLemma [] [] `comp_app)
         ","
         (Tactic.simpLemma [] [] `Prod.fst_swap)
         ","
         (Tactic.simpLemma [] [] `Prod.snd_swap)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Prod.snd_swap
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Prod.fst_swap
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `comp_app
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tacticFunext__ "funext" [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.congr "congr" [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Set.Data.Set.Image.term_''_
        (Term.fun
         "fun"
         (Term.basicFun
          [`p]
          [(Term.typeSpec
            ":"
            («term_×_»
             (Term.app
              `nonempty_compacts
              [(Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ "ℓ_infty_ℝ")])
             "×"
             (Term.app
              `nonempty_compacts
              [(Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ "ℓ_infty_ℝ")])))]
          "=>"
          (Term.app
           `Hausdorff_dist
           [(Term.typeAscription
             "("
             (Term.proj `p "." (fieldIdx "1"))
             ":"
             [(Term.app `Set [(Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ "ℓ_infty_ℝ")])]
             ")")
            (Term.proj `p "." (fieldIdx "2"))])))
        " '' "
        (LowerSet.Order.UpperLower.lower_set.prod
         (Set.«term{_|_}»
          "{"
          (Std.ExtendedBinder.extBinder (Lean.binderIdent `a) [])
          "|"
          («term_=_» (Quotient.Init.Data.Quot.«term⟦_⟧» "⟦" `a "⟧") "=" `x)
          "}")
         " ×ˢ "
         (Set.«term{_|_}»
          "{"
          (Std.ExtendedBinder.extBinder (Lean.binderIdent `b) [])
          "|"
          («term_=_» (Quotient.Init.Data.Quot.«term⟦_⟧» "⟦" `b "⟧") "=" `y)
          "}")))
       "="
       (Set.Data.Set.Image.term_''_
        («term_∘_»
         (Term.fun
          "fun"
          (Term.basicFun
           [`p]
           [(Term.typeSpec
             ":"
             («term_×_»
              (Term.app
               `nonempty_compacts
               [(Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ "ℓ_infty_ℝ")])
              "×"
              (Term.app
               `nonempty_compacts
               [(Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ "ℓ_infty_ℝ")])))]
           "=>"
           (Term.app
            `Hausdorff_dist
            [(Term.typeAscription
              "("
              (Term.proj `p "." (fieldIdx "1"))
              ":"
              [(Term.app `Set [(Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ "ℓ_infty_ℝ")])]
              ")")
             (Term.proj `p "." (fieldIdx "2"))])))
         "∘"
         `Prod.swap)
        " '' "
        (LowerSet.Order.UpperLower.lower_set.prod
         (Set.«term{_|_}»
          "{"
          (Std.ExtendedBinder.extBinder (Lean.binderIdent `a) [])
          "|"
          («term_=_» (Quotient.Init.Data.Quot.«term⟦_⟧» "⟦" `a "⟧") "=" `x)
          "}")
         " ×ˢ "
         (Set.«term{_|_}»
          "{"
          (Std.ExtendedBinder.extBinder (Lean.binderIdent `b) [])
          "|"
          («term_=_» (Quotient.Init.Data.Quot.«term⟦_⟧» "⟦" `b "⟧") "=" `y)
          "}"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Set.Data.Set.Image.term_''_
       («term_∘_»
        (Term.fun
         "fun"
         (Term.basicFun
          [`p]
          [(Term.typeSpec
            ":"
            («term_×_»
             (Term.app
              `nonempty_compacts
              [(Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ "ℓ_infty_ℝ")])
             "×"
             (Term.app
              `nonempty_compacts
              [(Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ "ℓ_infty_ℝ")])))]
          "=>"
          (Term.app
           `Hausdorff_dist
           [(Term.typeAscription
             "("
             (Term.proj `p "." (fieldIdx "1"))
             ":"
             [(Term.app `Set [(Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ "ℓ_infty_ℝ")])]
             ")")
            (Term.proj `p "." (fieldIdx "2"))])))
        "∘"
        `Prod.swap)
       " '' "
       (LowerSet.Order.UpperLower.lower_set.prod
        (Set.«term{_|_}»
         "{"
         (Std.ExtendedBinder.extBinder (Lean.binderIdent `a) [])
         "|"
         («term_=_» (Quotient.Init.Data.Quot.«term⟦_⟧» "⟦" `a "⟧") "=" `x)
         "}")
        " ×ˢ "
        (Set.«term{_|_}»
         "{"
         (Std.ExtendedBinder.extBinder (Lean.binderIdent `b) [])
         "|"
         («term_=_» (Quotient.Init.Data.Quot.«term⟦_⟧» "⟦" `b "⟧") "=" `y)
         "}")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (LowerSet.Order.UpperLower.lower_set.prod
       (Set.«term{_|_}»
        "{"
        (Std.ExtendedBinder.extBinder (Lean.binderIdent `a) [])
        "|"
        («term_=_» (Quotient.Init.Data.Quot.«term⟦_⟧» "⟦" `a "⟧") "=" `x)
        "}")
       " ×ˢ "
       (Set.«term{_|_}»
        "{"
        (Std.ExtendedBinder.extBinder (Lean.binderIdent `b) [])
        "|"
        («term_=_» (Quotient.Init.Data.Quot.«term⟦_⟧» "⟦" `b "⟧") "=" `y)
        "}"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Set.«term{_|_}»
       "{"
       (Std.ExtendedBinder.extBinder (Lean.binderIdent `b) [])
       "|"
       («term_=_» (Quotient.Init.Data.Quot.«term⟦_⟧» "⟦" `b "⟧") "=" `y)
       "}")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_» (Quotient.Init.Data.Quot.«term⟦_⟧» "⟦" `b "⟧") "=" `y)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Quotient.Init.Data.Quot.«term⟦_⟧» "⟦" `b "⟧")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `b
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1023, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 82 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 82, term))
      (Set.«term{_|_}»
       "{"
       (Std.ExtendedBinder.extBinder (Lean.binderIdent `a) [])
       "|"
       («term_=_» (Quotient.Init.Data.Quot.«term⟦_⟧» "⟦" `a "⟧") "=" `x)
       "}")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_» (Quotient.Init.Data.Quot.«term⟦_⟧» "⟦" `a "⟧") "=" `x)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Quotient.Init.Data.Quot.«term⟦_⟧» "⟦" `a "⟧")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1023, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 83 >? 1024, (none, [anonymous]) <=? (some 82, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 82, (some 82, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      («term_∘_»
       (Term.fun
        "fun"
        (Term.basicFun
         [`p]
         [(Term.typeSpec
           ":"
           («term_×_»
            (Term.app
             `nonempty_compacts
             [(Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ "ℓ_infty_ℝ")])
            "×"
            (Term.app
             `nonempty_compacts
             [(Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ "ℓ_infty_ℝ")])))]
         "=>"
         (Term.app
          `Hausdorff_dist
          [(Term.typeAscription
            "("
            (Term.proj `p "." (fieldIdx "1"))
            ":"
            [(Term.app `Set [(Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ "ℓ_infty_ℝ")])]
            ")")
           (Term.proj `p "." (fieldIdx "2"))])))
       "∘"
       `Prod.swap)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Prod.swap
[PrettyPrinter.parenthesize] ...precedences are 90 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 90, term))
      (Term.fun
       "fun"
       (Term.basicFun
        [`p]
        [(Term.typeSpec
          ":"
          («term_×_»
           (Term.app
            `nonempty_compacts
            [(Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ "ℓ_infty_ℝ")])
           "×"
           (Term.app
            `nonempty_compacts
            [(Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ "ℓ_infty_ℝ")])))]
        "=>"
        (Term.app
         `Hausdorff_dist
         [(Term.typeAscription
           "("
           (Term.proj `p "." (fieldIdx "1"))
           ":"
           [(Term.app `Set [(Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ "ℓ_infty_ℝ")])]
           ")")
          (Term.proj `p "." (fieldIdx "2"))])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Hausdorff_dist
       [(Term.typeAscription
         "("
         (Term.proj `p "." (fieldIdx "1"))
         ":"
         [(Term.app `Set [(Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ "ℓ_infty_ℝ")])]
         ")")
        (Term.proj `p "." (fieldIdx "2"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `p "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.typeAscription
       "("
       (Term.proj `p "." (fieldIdx "1"))
       ":"
       [(Term.app `Set [(Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ "ℓ_infty_ℝ")])]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Set [(Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ "ℓ_infty_ℝ")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ "ℓ_infty_ℝ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ', expected 'Topology.MetricSpace.GromovHausdorff.termℓ_infty_ℝ._@.Topology.MetricSpace.GromovHausdorff._hyg.5'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.letPatDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveEqnsDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letIdDecl', expected 'Lean.Parser.Term.letPatDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letIdDecl', expected 'Lean.Parser.Term.letEqnsDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/-- The Gromov-Hausdorff distance defines a genuine distance on the Gromov-Hausdorff space. -/
  instance
    : MetricSpace GHSpace
    where
      dist := dist
        dist_self
          x
          :=
          by
            rcases exists_rep x with ⟨ y , hy ⟩
              refine' le_antisymm _ _
              ·
                apply cinfₛ_le
                  ·
                    exact
                      ⟨
                        0
                          ,
                          by rintro b ⟨ ⟨ u , v ⟩ , ⟨ hu , hv ⟩ , rfl ⟩ exact Hausdorff_dist_nonneg
                        ⟩
                  ·
                    simp only [ mem_image , mem_prod , mem_set_of_eq , Prod.exists ]
                      exists y , y
                      simpa
                        only
                          [
                            and_self_iff
                              ,
                              Hausdorff_dist_self_zero
                              ,
                              eq_self_iff_true
                              ,
                              and_true_iff
                            ]
              ·
                apply le_cinfₛ
                  · exact nonempty.prod ⟨ y , hy ⟩ ⟨ y , hy ⟩ . image _
                  · rintro b ⟨ ⟨ u , v ⟩ , ⟨ hu , hv ⟩ , rfl ⟩ exact Hausdorff_dist_nonneg
        dist_comm
          x y
          :=
          by
            have
                A
                  :
                    fun
                          p
                            : nonempty_compacts ℓ_infty_ℝ × nonempty_compacts ℓ_infty_ℝ
                            =>
                            Hausdorff_dist ( p . 1 : Set ℓ_infty_ℝ ) p . 2
                        ''
                        { a | ⟦ a ⟧ = x } ×ˢ { b | ⟦ b ⟧ = y }
                      =
                      fun
                            p
                              : nonempty_compacts ℓ_infty_ℝ × nonempty_compacts ℓ_infty_ℝ
                              =>
                              Hausdorff_dist ( p . 1 : Set ℓ_infty_ℝ ) p . 2
                          ∘
                          Prod.swap
                        ''
                        { a | ⟦ a ⟧ = x } ×ˢ { b | ⟦ b ⟧ = y }
                  :=
                  by
                    congr
                      funext
                      simp only [ comp_app , Prod.fst_swap , Prod.snd_swap ]
                      rw [ Hausdorff_dist_comm ]
              simp only [ dist , A , image_comp , image_swap_prod ]
        eq_of_dist_eq_zero
          x y hxy
          :=
          by
            rcases GH_dist_eq_Hausdorff_dist x.rep y.rep with ⟨ Φ , Ψ , Φisom , Ψisom , DΦΨ ⟩
              rw [ ← dist_GH_dist , hxy ] at DΦΨ
              have
                : range Φ = range Ψ
                  :=
                  by
                    have hΦ : IsCompact range Φ := is_compact_range Φisom.continuous
                      have hΨ : IsCompact range Ψ := is_compact_range Ψisom.continuous
                      apply IsClosed.Hausdorff_dist_zero_iff_eq _ _ _ . 1 DΦΨ.symm
                      · exact hΦ.is_closed
                      · exact hΨ.is_closed
                      ·
                        exact
                          Hausdorff_edist_ne_top_of_nonempty_of_bounded
                            range_nonempty _ range_nonempty _ hΦ.bounded hΨ.bounded
              have T : range Ψ ≃ᵢ y.rep = range Φ ≃ᵢ y.rep := by rw [ this ]
              have eΨ := cast T Ψisom.isometric_on_range.symm
              have e := Φisom.isometric_on_range.trans eΨ
              rw
                [
                  ← x.to_GH_space_rep
                    ,
                    ← y.to_GH_space_rep
                    ,
                    to_GH_space_eq_to_GH_space_iff_isometric
                  ]
              exact ⟨ e ⟩
        dist_triangle
          x y z
          :=
          by
            let X := x.rep
              let Y := y.rep
              let Z := z.rep
              let γ1 := optimal_GH_coupling X Y
              let γ2 := optimal_GH_coupling Y Z
              let Φ : Y → γ1 := optimal_GH_injr X Y
              have hΦ : Isometry Φ := isometry_optimal_GH_injr X Y
              let Ψ : Y → γ2 := optimal_GH_injl Y Z
              have hΨ : Isometry Ψ := isometry_optimal_GH_injl Y Z
              let γ := glue_space hΦ hΨ
              letI : MetricSpace γ := Metric.metricSpaceGlueSpace hΦ hΨ
              have
                Comm
                  : to_glue_l hΦ hΨ ∘ optimal_GH_injr X Y = to_glue_r hΦ hΨ ∘ optimal_GH_injl Y Z
                  :=
                  to_glue_commute hΦ hΨ
              calc
                dist x z = dist to_GH_space X to_GH_space Z
                  :=
                  by rw [ x.to_GH_space_rep , z.to_GH_space_rep ]
                _
                      ≤
                      Hausdorff_dist
                        range to_glue_l hΦ hΨ ∘ optimal_GH_injl X Y
                          range to_glue_r hΦ hΨ ∘ optimal_GH_injr Y Z
                    :=
                    GH_dist_le_Hausdorff_dist
                      to_glue_l_isometry hΦ hΨ . comp isometry_optimal_GH_injl X Y
                        to_glue_r_isometry hΦ hΨ . comp isometry_optimal_GH_injr Y Z
                  _
                      ≤
                      Hausdorff_dist
                          range to_glue_l hΦ hΨ ∘ optimal_GH_injl X Y
                            range to_glue_l hΦ hΨ ∘ optimal_GH_injr X Y
                        +
                        Hausdorff_dist
                          range to_glue_l hΦ hΨ ∘ optimal_GH_injr X Y
                            range to_glue_r hΦ hΨ ∘ optimal_GH_injr Y Z
                    :=
                    by
                      refine'
                          Hausdorff_dist_triangle
                            Hausdorff_edist_ne_top_of_nonempty_of_bounded
                              range_nonempty _ range_nonempty _ _ _
                        ·
                          exact
                            is_compact_range
                                Isometry.continuous
                                  to_glue_l_isometry hΦ hΨ . comp isometry_optimal_GH_injl X Y
                              .
                              Bounded
                        ·
                          exact
                            is_compact_range
                                Isometry.continuous
                                  to_glue_l_isometry hΦ hΨ . comp isometry_optimal_GH_injr X Y
                              .
                              Bounded
                  _
                      =
                      Hausdorff_dist
                          to_glue_l hΦ hΨ '' range optimal_GH_injl X Y
                            to_glue_l hΦ hΨ '' range optimal_GH_injr X Y
                        +
                        Hausdorff_dist
                          to_glue_r hΦ hΨ '' range optimal_GH_injl Y Z
                            to_glue_r hΦ hΨ '' range optimal_GH_injr Y Z
                    :=
                    by simp only [ ← range_comp , Comm , eq_self_iff_true , add_right_inj ]
                  _
                      =
                      Hausdorff_dist range optimal_GH_injl X Y range optimal_GH_injr X Y
                        +
                        Hausdorff_dist range optimal_GH_injl Y Z range optimal_GH_injr Y Z
                    :=
                    by
                      rw
                        [
                          Hausdorff_dist_image to_glue_l_isometry hΦ hΨ
                            ,
                            Hausdorff_dist_image to_glue_r_isometry hΦ hΨ
                          ]
                  _ = dist to_GH_space X to_GH_space Y + dist to_GH_space Y to_GH_space Z
                    :=
                    by rw [ Hausdorff_dist_optimal , Hausdorff_dist_optimal , GH_dist , GH_dist ]
                  _ = dist x y + dist y z
                    :=
                    by rw [ x.to_GH_space_rep , y.to_GH_space_rep , z.to_GH_space_rep ]

end GHSpace

--section
end GromovHausdorff

/-- In particular, nonempty compacts of a metric space map to `GH_space`. We register this
in the topological_space namespace to take advantage of the notation `p.to_GH_space`. -/
def TopologicalSpace.NonemptyCompacts.toGHSpace {X : Type u} [MetricSpace X]
    (p : NonemptyCompacts X) : GromovHausdorff.GHSpace :=
  GromovHausdorff.toGHSpace p
#align topological_space.nonempty_compacts.to_GH_space TopologicalSpace.NonemptyCompacts.toGHSpace

open TopologicalSpace

namespace GromovHausdorff

section NonemptyCompacts

variable {X : Type u} [MetricSpace X]

theorem GH_dist_le_nonempty_compacts_dist (p q : NonemptyCompacts X) :
    dist p.toGHSpace q.toGHSpace ≤ dist p q :=
  by
  have ha : Isometry (coe : p → X) := isometry_subtype_coe
  have hb : Isometry (coe : q → X) := isometry_subtype_coe
  have A : dist p q = Hausdorff_dist (p : Set X) q := rfl
  have I : ↑p = range (coe : p → X) := subtype.range_coe_subtype.symm
  have J : ↑q = range (coe : q → X) := subtype.range_coe_subtype.symm
  rw [A, I, J]
  exact GH_dist_le_Hausdorff_dist ha hb
#align
  Gromov_Hausdorff.GH_dist_le_nonempty_compacts_dist GromovHausdorff.GH_dist_le_nonempty_compacts_dist

theorem to_GH_space_lipschitz :
    LipschitzWith 1 (NonemptyCompacts.toGHSpace : NonemptyCompacts X → GHSpace) :=
  LipschitzWith.mk_one GH_dist_le_nonempty_compacts_dist
#align Gromov_Hausdorff.to_GH_space_lipschitz GromovHausdorff.to_GH_space_lipschitz

theorem to_GH_space_continuous :
    Continuous (NonemptyCompacts.toGHSpace : NonemptyCompacts X → GHSpace) :=
  to_GH_space_lipschitz.Continuous
#align Gromov_Hausdorff.to_GH_space_continuous GromovHausdorff.to_GH_space_continuous

end NonemptyCompacts

section

/- In this section, we show that if two metric spaces are isometric up to `ε₂`, then their
Gromov-Hausdorff distance is bounded by `ε₂ / 2`. More generally, if there are subsets which are
`ε₁`-dense and `ε₃`-dense in two spaces, and isometric up to `ε₂`, then the Gromov-Hausdorff
distance between the spaces is bounded by `ε₁ + ε₂/2 + ε₃`. For this, we construct a suitable
coupling between the two spaces, by gluing them (approximately) along the two matching subsets. -/
variable {X : Type u} [MetricSpace X] [CompactSpace X] [Nonempty X] {Y : Type v} [MetricSpace Y]
  [CompactSpace Y] [Nonempty Y]

-- we want to ignore these instances in the following theorem
attribute [local instance] Sum.topologicalSpace Sum.uniformSpace

/-- If there are subsets which are `ε₁`-dense and `ε₃`-dense in two spaces, and
isometric up to `ε₂`, then the Gromov-Hausdorff distance between the spaces is bounded by
`ε₁ + ε₂/2 + ε₃`. -/
theorem GH_dist_le_of_approx_subsets {s : Set X} (Φ : s → Y) {ε₁ ε₂ ε₃ : ℝ}
    (hs : ∀ x : X, ∃ y ∈ s, dist x y ≤ ε₁) (hs' : ∀ x : Y, ∃ y : s, dist x (Φ y) ≤ ε₃)
    (H : ∀ x y : s, |dist x y - dist (Φ x) (Φ y)| ≤ ε₂) : gHDist X Y ≤ ε₁ + ε₂ / 2 + ε₃ :=
  by
  refine' le_of_forall_pos_le_add fun δ δ0 => _
  rcases exists_mem_of_nonempty X with ⟨xX, _⟩
  rcases hs xX with ⟨xs, hxs, Dxs⟩
  have sne : s.nonempty := ⟨xs, hxs⟩
  letI : Nonempty s := sne.to_subtype
  have : 0 ≤ ε₂ := le_trans (abs_nonneg _) (H ⟨xs, hxs⟩ ⟨xs, hxs⟩)
  have : ∀ p q : s, |dist p q - dist (Φ p) (Φ q)| ≤ 2 * (ε₂ / 2 + δ) := fun p q =>
    calc
      |dist p q - dist (Φ p) (Φ q)| ≤ ε₂ := H p q
      _ ≤ 2 * (ε₂ / 2 + δ) := by linarith
      
  -- glue `X` and `Y` along the almost matching subsets
  letI : MetricSpace (Sum X Y) :=
    glue_metric_approx (fun x : s => (x : X)) (fun x => Φ x) (ε₂ / 2 + δ) (by linarith) this
  let Fl := @Sum.inl X Y
  let Fr := @Sum.inr X Y
  have Il : Isometry Fl := Isometry.of_dist_eq fun x y => rfl
  have Ir : Isometry Fr := Isometry.of_dist_eq fun x y => rfl
  /- The proof goes as follows : the `GH_dist` is bounded by the Hausdorff distance of the images
    in the coupling, which is bounded (using the triangular inequality) by the sum of the Hausdorff
    distances of `X` and `s` (in the coupling or, equivalently in the original space), of `s` and
    `Φ s`, and of `Φ s` and `Y` (in the coupling or, equivalently, in the original space). The first
    term is bounded by `ε₁`, by `ε₁`-density. The third one is bounded by `ε₃`. And the middle one is
    bounded by `ε₂/2` as in the coupling the points `x` and `Φ x` are at distance `ε₂/2` by
    construction of the coupling (in fact `ε₂/2 + δ` where `δ` is an arbitrarily small positive
    constant where positivity is used to ensure that the coupling is really a metric space and not a
    premetric space on `X ⊕ Y`). -/
  have : GH_dist X Y ≤ Hausdorff_dist (range Fl) (range Fr) := GH_dist_le_Hausdorff_dist Il Ir
  have :
    Hausdorff_dist (range Fl) (range Fr) ≤
      Hausdorff_dist (range Fl) (Fl '' s) + Hausdorff_dist (Fl '' s) (range Fr) :=
    haveI B : bounded (range Fl) := (is_compact_range Il.continuous).Bounded
    Hausdorff_dist_triangle
      (Hausdorff_edist_ne_top_of_nonempty_of_bounded (range_nonempty _) (sne.image _) B
        (B.mono (image_subset_range _ _)))
  have :
    Hausdorff_dist (Fl '' s) (range Fr) ≤
      Hausdorff_dist (Fl '' s) (Fr '' range Φ) + Hausdorff_dist (Fr '' range Φ) (range Fr) :=
    haveI B : bounded (range Fr) := (is_compact_range Ir.continuous).Bounded
    Hausdorff_dist_triangle'
      (Hausdorff_edist_ne_top_of_nonempty_of_bounded ((range_nonempty _).image _) (range_nonempty _)
        (bounded.mono (image_subset_range _ _) B) B)
  have : Hausdorff_dist (range Fl) (Fl '' s) ≤ ε₁ :=
    by
    rw [← image_univ, Hausdorff_dist_image Il]
    have : 0 ≤ ε₁ := le_trans dist_nonneg Dxs
    refine'
      Hausdorff_dist_le_of_mem_dist this (fun x hx => hs x) fun x hx =>
        ⟨x, mem_univ _, by simpa only [dist_self] ⟩
  have : Hausdorff_dist (Fl '' s) (Fr '' range Φ) ≤ ε₂ / 2 + δ :=
    by
    refine' Hausdorff_dist_le_of_mem_dist (by linarith) _ _
    · intro x' hx'
      rcases(Set.mem_image _ _ _).1 hx' with ⟨x, ⟨x_in_s, xx'⟩⟩
      rw [← xx']
      use Fr (Φ ⟨x, x_in_s⟩), mem_image_of_mem Fr (mem_range_self _)
      exact le_of_eq (glue_dist_glued_points (fun x : s => (x : X)) Φ (ε₂ / 2 + δ) ⟨x, x_in_s⟩)
    · intro x' hx'
      rcases(Set.mem_image _ _ _).1 hx' with ⟨y, ⟨y_in_s', yx'⟩⟩
      rcases mem_range.1 y_in_s' with ⟨x, xy⟩
      use Fl x, mem_image_of_mem _ x.2
      rw [← yx', ← xy, dist_comm]
      exact le_of_eq (glue_dist_glued_points (@Subtype.val X s) Φ (ε₂ / 2 + δ) x)
  have : Hausdorff_dist (Fr '' range Φ) (range Fr) ≤ ε₃ :=
    by
    rw [← @image_univ _ _ Fr, Hausdorff_dist_image Ir]
    rcases exists_mem_of_nonempty Y with ⟨xY, _⟩
    rcases hs' xY with ⟨xs', Dxs'⟩
    have : 0 ≤ ε₃ := le_trans dist_nonneg Dxs'
    refine'
      Hausdorff_dist_le_of_mem_dist this (fun x hx => ⟨x, mem_univ _, by simpa only [dist_self] ⟩)
        fun x _ => _
    rcases hs' x with ⟨y, Dy⟩
    exact ⟨Φ y, mem_range_self _, Dy⟩
  linarith
#align Gromov_Hausdorff.GH_dist_le_of_approx_subsets GromovHausdorff.GH_dist_le_of_approx_subsets

end

--section
/-- The Gromov-Hausdorff space is second countable. -/
instance : SecondCountableTopology GHSpace :=
  by
  refine' second_countable_of_countable_discretization fun δ δpos => _
  let ε := 2 / 5 * δ
  have εpos : 0 < ε := mul_pos (by norm_num) δpos
  have : ∀ p : GH_space, ∃ s : Set p.rep, s.Finite ∧ univ ⊆ ⋃ x ∈ s, ball x ε := fun p => by
    simpa only [subset_univ, exists_true_left] using
      finite_cover_balls_of_compact is_compact_univ εpos
  -- for each `p`, `s p` is a finite `ε`-dense subset of `p` (or rather the metric space
  -- `p.rep` representing `p`)
  choose s hs using this
  have : ∀ p : GH_space, ∀ t : Set p.rep, t.Finite → ∃ n : ℕ, ∃ e : Equiv t (Fin n), True :=
    by
    intro p t ht
    letI : Fintype t := finite.fintype ht
    exact ⟨Fintype.card t, Fintype.equivFin t, trivial⟩
  choose N e hne using this
  -- cardinality of the nice finite subset `s p` of `p.rep`, called `N p`
  let N := fun p : GH_space => N p (s p) (hs p).1
  -- equiv from `s p`, a nice finite subset of `p.rep`, to `fin (N p)`, called `E p`
  let E := fun p : GH_space => e p (s p) (hs p).1
  -- A function `F` associating to `p : GH_space` the data of all distances between points
  -- in the `ε`-dense set `s p`.
  let F : GH_space → Σn : ℕ, Fin n → Fin n → ℤ := fun p =>
    ⟨N p, fun a b => ⌊ε⁻¹ * dist ((E p).symm a) ((E p).symm b)⌋⟩
  refine' ⟨Σn, Fin n → Fin n → ℤ, by infer_instance, F, fun p q hpq => _⟩
  /- As the target space of F is countable, it suffices to show that two points
    `p` and `q` with `F p = F q` are at distance `≤ δ`.
    For this, we construct a map `Φ` from `s p ⊆ p.rep` (representing `p`)
    to `q.rep` (representing `q`) which is almost an isometry on `s p`, and
    with image `s q`. For this, we compose the identification of `s p` with `fin (N p)`
    and the inverse of the identification of `s q` with `fin (N q)`. Together with
    the fact that `N p = N q`, this constructs `Ψ` between `s p` and `s q`, and then
    composing with the canonical inclusion we get `Φ`. -/
  have Npq : N p = N q := (Sigma.mk.inj_iff.1 hpq).1
  let Ψ : s p → s q := fun x => (E q).symm (Fin.cast Npq ((E p) x))
  let Φ : s p → q.rep := fun x => Ψ x
  -- Use the almost isometry `Φ` to show that `p.rep` and `q.rep`
  -- are within controlled Gromov-Hausdorff distance.
  have main : GH_dist p.rep q.rep ≤ ε + ε / 2 + ε :=
    by
    refine' GH_dist_le_of_approx_subsets Φ _ _ _
    show ∀ x : p.rep, ∃ (y : p.rep)(H : y ∈ s p), dist x y ≤ ε
    · -- by construction, `s p` is `ε`-dense
      intro x
      have : x ∈ ⋃ y ∈ s p, ball y ε := (hs p).2 (mem_univ _)
      rcases mem_Union₂.1 this with ⟨y, ys, hy⟩
      exact ⟨y, ys, le_of_lt hy⟩
    show ∀ x : q.rep, ∃ z : s p, dist x (Φ z) ≤ ε
    · -- by construction, `s q` is `ε`-dense, and it is the range of `Φ`
      intro x
      have : x ∈ ⋃ y ∈ s q, ball y ε := (hs q).2 (mem_univ _)
      rcases mem_Union₂.1 this with ⟨y, ys, hy⟩
      let i : ℕ := E q ⟨y, ys⟩
      let hi := ((E q) ⟨y, ys⟩).is_lt
      have ihi_eq : (⟨i, hi⟩ : Fin (N q)) = (E q) ⟨y, ys⟩ := by rw [Fin.ext_iff, Fin.coe_mk]
      have hiq : i < N q := hi
      have hip : i < N p := by rwa [Npq.symm] at hiq
      let z := (E p).symm ⟨i, hip⟩
      use z
      have C1 : (E p) z = ⟨i, hip⟩ := (E p).apply_symm_apply ⟨i, hip⟩
      have C2 : Fin.cast Npq ⟨i, hip⟩ = ⟨i, hi⟩ := rfl
      have C3 : (E q).symm ⟨i, hi⟩ = ⟨y, ys⟩ :=
        by
        rw [ihi_eq]
        exact (E q).symm_apply_apply ⟨y, ys⟩
      have : Φ z = y := by
        simp only [Φ, Ψ]
        rw [C1, C2, C3]
        rfl
      rw [this]
      exact le_of_lt hy
    show ∀ x y : s p, |dist x y - dist (Φ x) (Φ y)| ≤ ε
    · /- the distance between `x` and `y` is encoded in `F p`, and the distance between
            `Φ x` and `Φ y` (two points of `s q`) is encoded in `F q`, all this up to `ε`.
            As `F p = F q`, the distances are almost equal. -/
      intro x y
      have : dist (Φ x) (Φ y) = dist (Ψ x) (Ψ y) := rfl
      rw [this]
      -- introduce `i`, that codes both `x` and `Φ x` in `fin (N p) = fin (N q)`
      let i : ℕ := E p x
      have hip : i < N p := ((E p) x).2
      have hiq : i < N q := by rwa [Npq] at hip
      have i' : i = (E q) (Ψ x) := by simp only [Equiv.apply_symm_apply, Fin.coe_cast]
      -- introduce `j`, that codes both `y` and `Φ y` in `fin (N p) = fin (N q)`
      let j : ℕ := E p y
      have hjp : j < N p := ((E p) y).2
      have hjq : j < N q := by rwa [Npq] at hjp
      have j' : j = ((E q) (Ψ y)).1 := by
        simp only [Equiv.apply_symm_apply, Fin.val_eq_coe, Fin.coe_cast]
      -- Express `dist x y` in terms of `F p`
      have : (F p).2 ((E p) x) ((E p) y) = floor (ε⁻¹ * dist x y) := by
        simp only [F, (E p).symm_apply_apply]
      have Ap : (F p).2 ⟨i, hip⟩ ⟨j, hjp⟩ = floor (ε⁻¹ * dist x y) :=
        by
        rw [← this]
        congr <;> apply Fin.ext_iff.2 <;> rfl
      -- Express `dist (Φ x) (Φ y)` in terms of `F q`
      have : (F q).2 ((E q) (Ψ x)) ((E q) (Ψ y)) = floor (ε⁻¹ * dist (Ψ x) (Ψ y)) := by
        simp only [F, (E q).symm_apply_apply]
      have Aq : (F q).2 ⟨i, hiq⟩ ⟨j, hjq⟩ = floor (ε⁻¹ * dist (Ψ x) (Ψ y)) :=
        by
        rw [← this]
        congr <;> apply Fin.ext_iff.2 <;> [exact i', exact j']
      -- use the equality between `F p` and `F q` to deduce that the distances have equal
      -- integer parts
      have : (F p).2 ⟨i, hip⟩ ⟨j, hjp⟩ = (F q).2 ⟨i, hiq⟩ ⟨j, hjq⟩ :=
        by
        -- we want to `subst hpq` where `hpq : F p = F q`, except that `subst` only works
        -- with a constant, so replace `F q` (and everything that depends on it) by a constant `f`
        -- then `subst`
        revert hiq hjq
        change N q with (F q).1
        generalize F q = f at hpq⊢
        subst hpq
        intros
        rfl
      rw [Ap, Aq] at this
      -- deduce that the distances coincide up to `ε`, by a straightforward computation
      -- that should be automated
      have I :=
        calc
          |ε⁻¹| * |dist x y - dist (Ψ x) (Ψ y)| = |ε⁻¹ * (dist x y - dist (Ψ x) (Ψ y))| :=
            (abs_mul _ _).symm
          _ = |ε⁻¹ * dist x y - ε⁻¹ * dist (Ψ x) (Ψ y)| :=
            by
            congr
            ring
          _ ≤ 1 := le_of_lt (abs_sub_lt_one_of_floor_eq_floor this)
          
      calc
        |dist x y - dist (Ψ x) (Ψ y)| = ε * ε⁻¹ * |dist x y - dist (Ψ x) (Ψ y)| := by
          rw [mul_inv_cancel (ne_of_gt εpos), one_mul]
        _ = ε * (|ε⁻¹| * |dist x y - dist (Ψ x) (Ψ y)|) := by
          rw [abs_of_nonneg (le_of_lt (inv_pos.2 εpos)), mul_assoc]
        _ ≤ ε * 1 := mul_le_mul_of_nonneg_left I (le_of_lt εpos)
        _ = ε := mul_one _
        
  calc
    dist p q = GH_dist p.rep q.rep := dist_GH_dist p q
    _ ≤ ε + ε / 2 + ε := main
    _ = δ := by
      simp only [ε]
      ring
    

/-- Compactness criterion: a closed set of compact metric spaces is compact if the spaces have
a uniformly bounded diameter, and for all `ε` the number of balls of radius `ε` required
to cover the spaces is uniformly bounded. This is an equivalence, but we only prove the
interesting direction that these conditions imply compactness. -/
theorem totally_bounded {t : Set GHSpace} {C : ℝ} {u : ℕ → ℝ} {K : ℕ → ℕ}
    (ulim : Tendsto u atTop (𝓝 0)) (hdiam : ∀ p ∈ t, diam (univ : Set (GHSpace.Rep p)) ≤ C)
    (hcov :
      ∀ p ∈ t,
        ∀ n : ℕ, ∃ s : Set (GHSpace.Rep p), Cardinal.mk s ≤ K n ∧ univ ⊆ ⋃ x ∈ s, ball x (u n)) :
    TotallyBounded t :=
  by
  /- Let `δ>0`, and `ε = δ/5`. For each `p`, we construct a finite subset `s p` of `p`, which
    is `ε`-dense and has cardinality at most `K n`. Encoding the mutual distances of points in `s p`,
    up to `ε`, we will get a map `F` associating to `p` finitely many data, and making it possible to
    reconstruct `p` up to `ε`. This is enough to prove total boundedness. -/
  refine' Metric.totally_bounded_of_finite_discretization fun δ δpos => _
  let ε := 1 / 5 * δ
  have εpos : 0 < ε := mul_pos (by norm_num) δpos
  -- choose `n` for which `u n < ε`
  rcases Metric.tendsto_at_top.1 ulim ε εpos with ⟨n, hn⟩
  have u_le_ε : u n ≤ ε := by
    have := hn n le_rfl
    simp only [Real.dist_eq, add_zero, sub_eq_add_neg, neg_zero] at this
    exact le_of_lt (lt_of_le_of_lt (le_abs_self _) this)
  -- construct a finite subset `s p` of `p` which is `ε`-dense and has cardinal `≤ K n`
  have :
    ∀ p : GH_space,
      ∃ s : Set p.rep, ∃ N ≤ K n, ∃ E : Equiv s (Fin N), p ∈ t → univ ⊆ ⋃ x ∈ s, ball x (u n) :=
    by
    intro p
    by_cases hp : p ∉ t
    · have : Nonempty (Equiv (∅ : Set p.rep) (Fin 0)) :=
        by
        rw [← Fintype.card_eq]
        simp only [empty_card', Fintype.card_fin]
      use ∅, 0, bot_le, choice this
    · rcases hcov _ (Set.not_not_mem.1 hp) n with ⟨s, ⟨scard, scover⟩⟩
      rcases Cardinal.lt_aleph_0.1 (lt_of_le_of_lt scard (Cardinal.nat_lt_aleph_0 _)) with ⟨N, hN⟩
      rw [hN, Cardinal.nat_cast_le] at scard
      have : Cardinal.mk s = Cardinal.mk (Fin N) := by rw [hN, Cardinal.mk_fin]
      cases' Quotient.exact this with E
      use s, N, scard, E
      simp only [scover, imp_true_iff]
  choose s N hN E hs using this
  -- Define a function `F` taking values in a finite type and associating to `p` enough data
  -- to reconstruct it up to `ε`, namely the (discretized) distances between elements of `s p`.
  let M := ⌊ε⁻¹ * max C 0⌋₊
  let F : GH_space → Σk : Fin (K n).succ, Fin k → Fin k → Fin M.succ := fun p =>
    ⟨⟨N p, lt_of_le_of_lt (hN p) (Nat.lt_succ_self _)⟩, fun a b =>
      ⟨min M ⌊ε⁻¹ * dist ((E p).symm a) ((E p).symm b)⌋₊,
        (min_le_left _ _).trans_lt (Nat.lt_succ_self _)⟩⟩
  refine' ⟨_, _, fun p => F p, _⟩
  infer_instance
  -- It remains to show that if `F p = F q`, then `p` and `q` are `ε`-close
  rintro ⟨p, pt⟩ ⟨q, qt⟩ hpq
  have Npq : N p = N q := Fin.ext_iff.1 (Sigma.mk.inj_iff.1 hpq).1
  let Ψ : s p → s q := fun x => (E q).symm (Fin.cast Npq ((E p) x))
  let Φ : s p → q.rep := fun x => Ψ x
  have main : GH_dist p.rep q.rep ≤ ε + ε / 2 + ε :=
    by
    -- to prove the main inequality, argue that `s p` is `ε`-dense in `p`, and `s q` is `ε`-dense
    -- in `q`, and `s p` and `s q` are almost isometric. Then closeness follows
    -- from `GH_dist_le_of_approx_subsets`
    refine' GH_dist_le_of_approx_subsets Φ _ _ _
    show ∀ x : p.rep, ∃ (y : p.rep)(H : y ∈ s p), dist x y ≤ ε
    · -- by construction, `s p` is `ε`-dense
      intro x
      have : x ∈ ⋃ y ∈ s p, ball y (u n) := (hs p pt) (mem_univ _)
      rcases mem_Union₂.1 this with ⟨y, ys, hy⟩
      exact ⟨y, ys, le_trans (le_of_lt hy) u_le_ε⟩
    show ∀ x : q.rep, ∃ z : s p, dist x (Φ z) ≤ ε
    · -- by construction, `s q` is `ε`-dense, and it is the range of `Φ`
      intro x
      have : x ∈ ⋃ y ∈ s q, ball y (u n) := (hs q qt) (mem_univ _)
      rcases mem_Union₂.1 this with ⟨y, ys, hy⟩
      let i : ℕ := E q ⟨y, ys⟩
      let hi := ((E q) ⟨y, ys⟩).2
      have ihi_eq : (⟨i, hi⟩ : Fin (N q)) = (E q) ⟨y, ys⟩ := by rw [Fin.ext_iff, Fin.coe_mk]
      have hiq : i < N q := hi
      have hip : i < N p := by rwa [Npq.symm] at hiq
      let z := (E p).symm ⟨i, hip⟩
      use z
      have C1 : (E p) z = ⟨i, hip⟩ := (E p).apply_symm_apply ⟨i, hip⟩
      have C2 : Fin.cast Npq ⟨i, hip⟩ = ⟨i, hi⟩ := rfl
      have C3 : (E q).symm ⟨i, hi⟩ = ⟨y, ys⟩ :=
        by
        rw [ihi_eq]
        exact (E q).symm_apply_apply ⟨y, ys⟩
      have : Φ z = y := by
        simp only [Φ, Ψ]
        rw [C1, C2, C3]
        rfl
      rw [this]
      exact le_trans (le_of_lt hy) u_le_ε
    show ∀ x y : s p, |dist x y - dist (Φ x) (Φ y)| ≤ ε
    · /- the distance between `x` and `y` is encoded in `F p`, and the distance between
            `Φ x` and `Φ y` (two points of `s q`) is encoded in `F q`, all this up to `ε`.
            As `F p = F q`, the distances are almost equal. -/
      intro x y
      have : dist (Φ x) (Φ y) = dist (Ψ x) (Ψ y) := rfl
      rw [this]
      -- introduce `i`, that codes both `x` and `Φ x` in `fin (N p) = fin (N q)`
      let i : ℕ := E p x
      have hip : i < N p := ((E p) x).2
      have hiq : i < N q := by rwa [Npq] at hip
      have i' : i = (E q) (Ψ x) := by simp only [Equiv.apply_symm_apply, Fin.coe_cast]
      -- introduce `j`, that codes both `y` and `Φ y` in `fin (N p) = fin (N q)`
      let j : ℕ := E p y
      have hjp : j < N p := ((E p) y).2
      have hjq : j < N q := by rwa [Npq] at hjp
      have j' : j = (E q) (Ψ y) := by simp only [Equiv.apply_symm_apply, Fin.coe_cast]
      -- Express `dist x y` in terms of `F p`
      have Ap : ((F p).2 ⟨i, hip⟩ ⟨j, hjp⟩).1 = ⌊ε⁻¹ * dist x y⌋₊ :=
        calc
          ((F p).2 ⟨i, hip⟩ ⟨j, hjp⟩).1 = ((F p).2 ((E p) x) ((E p) y)).1 := by
            congr <;> apply Fin.ext_iff.2 <;> rfl
          _ = min M ⌊ε⁻¹ * dist x y⌋₊ := by simp only [F, (E p).symm_apply_apply]
          _ = ⌊ε⁻¹ * dist x y⌋₊ := by
            refine' min_eq_right (Nat.floor_mono _)
            refine' mul_le_mul_of_nonneg_left (le_trans _ (le_max_left _ _)) (inv_pos.2 εpos).le
            change dist (x : p.rep) y ≤ C
            refine'
              le_trans (dist_le_diam_of_mem is_compact_univ.bounded (mem_univ _) (mem_univ _)) _
            exact hdiam p pt
          
      -- Express `dist (Φ x) (Φ y)` in terms of `F q`
      have Aq : ((F q).2 ⟨i, hiq⟩ ⟨j, hjq⟩).1 = ⌊ε⁻¹ * dist (Ψ x) (Ψ y)⌋₊ :=
        calc
          ((F q).2 ⟨i, hiq⟩ ⟨j, hjq⟩).1 = ((F q).2 ((E q) (Ψ x)) ((E q) (Ψ y))).1 := by
            congr <;> apply Fin.ext_iff.2 <;> [exact i', exact j']
          _ = min M ⌊ε⁻¹ * dist (Ψ x) (Ψ y)⌋₊ := by simp only [F, (E q).symm_apply_apply]
          _ = ⌊ε⁻¹ * dist (Ψ x) (Ψ y)⌋₊ :=
            by
            refine' min_eq_right (Nat.floor_mono _)
            refine' mul_le_mul_of_nonneg_left (le_trans _ (le_max_left _ _)) (inv_pos.2 εpos).le
            change dist (Ψ x : q.rep) (Ψ y) ≤ C
            refine'
              le_trans (dist_le_diam_of_mem is_compact_univ.bounded (mem_univ _) (mem_univ _)) _
            exact hdiam q qt
          
      -- use the equality between `F p` and `F q` to deduce that the distances have equal
      -- integer parts
      have : ((F p).2 ⟨i, hip⟩ ⟨j, hjp⟩).1 = ((F q).2 ⟨i, hiq⟩ ⟨j, hjq⟩).1 :=
        by
        -- we want to `subst hpq` where `hpq : F p = F q`, except that `subst` only works
        -- with a constant, so replace `F q` (and everything that depends on it) by a constant `f`
        -- then `subst`
        revert hiq hjq
        change N q with (F q).1
        generalize F q = f at hpq⊢
        subst hpq
        intros
        rfl
      have : ⌊ε⁻¹ * dist x y⌋ = ⌊ε⁻¹ * dist (Ψ x) (Ψ y)⌋ :=
        by
        rw [Ap, Aq] at this
        have D : 0 ≤ ⌊ε⁻¹ * dist x y⌋ :=
          floor_nonneg.2 (mul_nonneg (le_of_lt (inv_pos.2 εpos)) dist_nonneg)
        have D' : 0 ≤ ⌊ε⁻¹ * dist (Ψ x) (Ψ y)⌋ :=
          floor_nonneg.2 (mul_nonneg (le_of_lt (inv_pos.2 εpos)) dist_nonneg)
        rw [← Int.toNat_of_nonneg D, ← Int.toNat_of_nonneg D', Int.floor_to_nat, Int.floor_to_nat,
          this]
      -- deduce that the distances coincide up to `ε`, by a straightforward computation
      -- that should be automated
      have I :=
        calc
          |ε⁻¹| * |dist x y - dist (Ψ x) (Ψ y)| = |ε⁻¹ * (dist x y - dist (Ψ x) (Ψ y))| :=
            (abs_mul _ _).symm
          _ = |ε⁻¹ * dist x y - ε⁻¹ * dist (Ψ x) (Ψ y)| :=
            by
            congr
            ring
          _ ≤ 1 := le_of_lt (abs_sub_lt_one_of_floor_eq_floor this)
          
      calc
        |dist x y - dist (Ψ x) (Ψ y)| = ε * ε⁻¹ * |dist x y - dist (Ψ x) (Ψ y)| := by
          rw [mul_inv_cancel (ne_of_gt εpos), one_mul]
        _ = ε * (|ε⁻¹| * |dist x y - dist (Ψ x) (Ψ y)|) := by
          rw [abs_of_nonneg (le_of_lt (inv_pos.2 εpos)), mul_assoc]
        _ ≤ ε * 1 := mul_le_mul_of_nonneg_left I (le_of_lt εpos)
        _ = ε := mul_one _
        
  calc
    dist p q = GH_dist p.rep q.rep := dist_GH_dist p q
    _ ≤ ε + ε / 2 + ε := main
    _ = δ / 2 := by
      simp only [ε, one_div]
      ring
    _ < δ := half_lt_self δpos
    
#align Gromov_Hausdorff.totally_bounded GromovHausdorff.totally_bounded

section Complete

/- We will show that a sequence `u n` of compact metric spaces satisfying
`dist (u n) (u (n+1)) < 1/2^n` converges, which implies completeness of the Gromov-Hausdorff space.
We need to exhibit the limiting compact metric space. For this, start from
a sequence `X n` of representatives of `u n`, and glue in an optimal way `X n` to `X (n+1)`
for all `n`, in a common metric space. Formally, this is done as follows.
Start from `Y 0 = X 0`. Then, glue `X 0` to `X 1` in an optimal way, yielding a space
`Y 1` (with an embedding of `X 1`). Then, consider an optimal gluing of `X 1` and `X 2`, and
glue it to `Y 1` along their common subspace `X 1`. This gives a new space `Y 2`, with an
embedding of `X 2`. Go on, to obtain a sequence of spaces `Y n`. Let `Z0` be the inductive
limit of the `Y n`, and finally let `Z` be the completion of `Z0`.
The images `X2 n` of `X n` in `Z` are at Hausdorff distance `< 1/2^n` by construction, hence they
form a Cauchy sequence for the Hausdorff distance. By completeness (of `Z`, and therefore of its
set of nonempty compact subsets), they converge to a limit `L`. This is the nonempty
compact metric space we are looking for.  -/
variable (X : ℕ → Type) [∀ n, MetricSpace (X n)] [∀ n, CompactSpace (X n)] [∀ n, Nonempty (X n)]

/-- Auxiliary structure used to glue metric spaces below, recording an isometric embedding
of a type `A` in another metric space. -/
structure AuxGluingStruct (A : Type) [MetricSpace A] : Type 1 where
  Space : Type
  metric : MetricSpace space
  embed : A → space
  isom : Isometry embed
#align Gromov_Hausdorff.aux_gluing_struct GromovHausdorff.AuxGluingStruct

instance (A : Type) [MetricSpace A] : Inhabited (AuxGluingStruct A) :=
  ⟨{  Space := A
      metric := by infer_instance
      embed := id
      isom := fun x y => rfl }⟩

/-- Auxiliary sequence of metric spaces, containing copies of `X 0`, ..., `X n`, where each
`X i` is glued to `X (i+1)` in an optimal way. The space at step `n+1` is obtained from the space
at step `n` by adding `X (n+1)`, glued in an optimal way to the `X n` already sitting there. -/
def auxGluing (n : ℕ) : AuxGluingStruct (X n) :=
  Nat.recOn n
    { Space := X 0
      metric := by infer_instance
      embed := id
      isom := fun x y => rfl } fun n Y =>
    letI : MetricSpace Y.space := Y.metric
    { Space := glue_space Y.isom (isometry_optimal_GH_injl (X n) (X (n + 1)))
      metric := by infer_instance
      embed :=
        to_glue_r Y.isom (isometry_optimal_GH_injl (X n) (X (n + 1))) ∘
          optimal_GH_injr (X n) (X (n + 1))
      isom := (to_glue_r_isometry _ _).comp (isometry_optimal_GH_injr (X n) (X (n + 1))) }
#align Gromov_Hausdorff.aux_gluing GromovHausdorff.auxGluing

/-- The Gromov-Hausdorff space is complete. -/
instance : CompleteSpace GHSpace :=
  by
  have : ∀ n : ℕ, 0 < ((1 : ℝ) / 2) ^ n := by
    apply pow_pos
    norm_num
  -- start from a sequence of nonempty compact metric spaces within distance `1/2^n` of each other
  refine'
    Metric.complete_of_convergent_controlled_sequences (fun n => (1 / 2) ^ n) this fun u hu => _
  -- `X n` is a representative of `u n`
  let X n := (u n).rep
  -- glue them together successively in an optimal way, getting a sequence of metric spaces `Y n`
  let Y := aux_gluing X
  letI : ∀ n, MetricSpace (Y n).Space := fun n => (Y n).metric
  have E :
    ∀ n : ℕ, glue_space (Y n).isom (isometry_optimal_GH_injl (X n) (X n.succ)) = (Y n.succ).Space :=
    fun n => by
    simp only [Y, aux_gluing]
    rfl
  let c n := cast (E n)
  have ic : ∀ n, Isometry (c n) := fun n x y => rfl
  -- there is a canonical embedding of `Y n` in `Y (n+1)`, by construction
  let f : ∀ n, (Y n).Space → (Y n.succ).Space := fun n =>
    c n ∘ to_glue_l (aux_gluing X n).isom (isometry_optimal_GH_injl (X n) (X n.succ))
  have I : ∀ n, Isometry (f n) := by
    intro n
    apply Isometry.comp
    · intro x y
      rfl
    · apply to_glue_l_isometry
  -- consider the inductive limit `Z0` of the `Y n`, and then its completion `Z`
  let Z0 := Metric.InductiveLimit I
  let Z := UniformSpace.Completion Z0
  let Φ := to_inductive_limit I
  let coeZ := (coe : Z0 → Z)
  -- let `X2 n` be the image of `X n` in the space `Z`
  let X2 n := range (coeZ ∘ Φ n ∘ (Y n).embed)
  have isom : ∀ n, Isometry (coeZ ∘ Φ n ∘ (Y n).embed) :=
    by
    intro n
    refine' uniform_space.completion.coe_isometry.comp _
    exact (to_inductive_limit_isometry _ _).comp (Y n).isom
  -- The Hausdorff distance of `X2 n` and `X2 (n+1)` is by construction the distance between
  -- `u n` and `u (n+1)`, therefore bounded by `1/2^n`
  have D2 : ∀ n, Hausdorff_dist (X2 n) (X2 n.succ) < (1 / 2) ^ n :=
    by
    intro n
    have X2n :
      X2 n =
        range
          ((coeZ ∘
              Φ n.succ ∘ c n ∘ to_glue_r (Y n).isom (isometry_optimal_GH_injl (X n) (X n.succ))) ∘
            optimal_GH_injl (X n) (X n.succ)) :=
      by
      change
        X2 n =
          range
            (coeZ ∘
              Φ n.succ ∘
                c n ∘
                  to_glue_r (Y n).isom (isometry_optimal_GH_injl (X n) (X n.succ)) ∘
                    optimal_GH_injl (X n) (X n.succ))
      simp only [X2, Φ]
      rw [← to_inductive_limit_commute I]
      simp only [f]
      rw [← to_glue_commute]
    rw [range_comp] at X2n
    have X2nsucc :
      X2 n.succ =
        range
          ((coeZ ∘
              Φ n.succ ∘ c n ∘ to_glue_r (Y n).isom (isometry_optimal_GH_injl (X n) (X n.succ))) ∘
            optimal_GH_injr (X n) (X n.succ)) :=
      by rfl
    rw [range_comp] at X2nsucc
    rw [X2n, X2nsucc, Hausdorff_dist_image, Hausdorff_dist_optimal, ← dist_GH_dist]
    · exact hu n n n.succ (le_refl n) (le_succ n)
    · apply uniform_space.completion.coe_isometry.comp _
      exact (to_inductive_limit_isometry _ _).comp ((ic n).comp (to_glue_r_isometry _ _))
  -- consider `X2 n` as a member `X3 n` of the type of nonempty compact subsets of `Z`, which
  -- is a metric space
  let X3 : ℕ → nonempty_compacts Z := fun n =>
    ⟨⟨X2 n, is_compact_range (isom n).Continuous⟩, range_nonempty _⟩
  -- `X3 n` is a Cauchy sequence by construction, as the successive distances are
  -- bounded by `(1/2)^n`
  have : CauchySeq X3 :=
    by
    refine' cauchy_seq_of_le_geometric (1 / 2) 1 (by norm_num) fun n => _
    rw [one_mul]
    exact le_of_lt (D2 n)
  -- therefore, it converges to a limit `L`
  rcases cauchy_seq_tendsto_of_complete this with ⟨L, hL⟩
  -- the images of `X3 n` in the Gromov-Hausdorff space converge to the image of `L`
  have M : tendsto (fun n => (X3 n).toGHSpace) at_top (𝓝 L.to_GH_space) :=
    tendsto.comp (to_GH_space_continuous.tendsto _) hL
  -- By construction, the image of `X3 n` in the Gromov-Hausdorff space is `u n`.
  have : ∀ n, (X3 n).toGHSpace = u n := by
    intro n
    rw [nonempty_compacts.to_GH_space, ← (u n).to_GH_space_rep,
      to_GH_space_eq_to_GH_space_iff_isometric]
    constructor
    convert (isom n).isometricOnRange.symm
  -- Finally, we have proved the convergence of `u n`
  exact ⟨L.to_GH_space, by simpa only [this] using M⟩

end Complete

--section
end GromovHausdorff

--namespace
