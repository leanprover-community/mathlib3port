/-
Copyright (c) 2019 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot

! This file was ported from Lean 3 source module topology.uniform_space.abstract_completion
! leanprover-community/mathlib commit 26f081a2fb920140ed5bc5cc5344e84bcc7cb2b2
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.UniformSpace.UniformEmbedding
import Mathbin.Topology.UniformSpace.Equiv

/-!
# Abstract theory of Hausdorff completions of uniform spaces

This file characterizes Hausdorff completions of a uniform space α as complete Hausdorff spaces
equipped with a map from α which has dense image and induce the original uniform structure on α.
Assuming these properties we "extend" uniformly continuous maps from α to complete Hausdorff spaces
to the completions of α. This is the universal property expected from a completion.
It is then used to extend uniformly continuous maps from α to α' to maps between
completions of α and α'.

This file does not construct any such completion, it only study consequences of their existence.
The first advantage is that formal properties are clearly highlighted without interference from
construction details. The second advantage is that this framework can then be used to compare
different completion constructions. See `topology/uniform_space/compare_reals` for an example.
Of course the comparison comes from the universal property as usual.

A general explicit construction of completions is done in `uniform_space/completion`, leading
to a functor from uniform spaces to complete Hausdorff uniform spaces that is left adjoint to the
inclusion, see `uniform_space/UniformSpace` for the category packaging.

## Implementation notes

A tiny technical advantage of using a characteristic predicate such as the properties listed in
`abstract_completion` instead of stating the universal property is that the universal property
derived from the predicate is more universe polymorphic.

## References

We don't know any traditional text discussing this. Real world mathematics simply silently
identify the results of any two constructions that lead to something one could reasonnably
call a completion.

## Tags

uniform spaces, completion, universal property
-/


noncomputable section

attribute [local instance] Classical.propDecidable

open Filter Set Function

universe u

/-- A completion of `α` is the data of a complete separated uniform space (from the same universe)
and a map from `α` with dense range and inducing the original uniform structure on `α`. -/
structure AbstractCompletion (α : Type u) [UniformSpace α] where
  Space : Type u
  coe : α → space
  uniformStruct : UniformSpace space
  complete : CompleteSpace space
  separation : SeparatedSpace space
  UniformInducing : UniformInducing coe
  dense : DenseRange coe
#align abstract_completion AbstractCompletion

attribute [local instance]
  AbstractCompletion.uniformStruct AbstractCompletion.complete AbstractCompletion.separation

namespace AbstractCompletion

variable {α : Type _} [UniformSpace α] (pkg : AbstractCompletion α)

-- mathport name: exprhatα
local notation "hatα" => pkg.Space

-- mathport name: exprι
local notation "ι" => pkg.coe

/-- If `α` is complete, then it is an abstract completion of itself. -/
def ofComplete [SeparatedSpace α] [CompleteSpace α] : AbstractCompletion α :=
  mk α id inferInstance inferInstance inferInstance uniform_inducing_id dense_range_id
#align abstract_completion.of_complete AbstractCompletion.ofComplete

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `closure_range [])
      (Command.declSig
       []
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app
          `closure
          [(Term.app
            `range
            [(AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termι "ι")])])
         "="
         `univ)))
      (Command.declValSimple ":=" (Term.proj (Term.proj `pkg "." `dense) "." `closure_range) [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.proj `pkg "." `dense) "." `closure_range)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj `pkg "." `dense)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `pkg
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app
        `closure
        [(Term.app
          `range
          [(AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termι "ι")])])
       "="
       `univ)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `univ
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app
       `closure
       [(Term.app
         `range
         [(AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termι "ι")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `range [(AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termι "ι")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termι', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termι', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termι "ι")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termι', expected 'AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termι._@.Topology.UniformSpace.AbstractCompletion._hyg.50'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem closure_range : closure range ι = univ := pkg . dense . closure_range
#align abstract_completion.closure_range AbstractCompletion.closure_range

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `dense_inducing [])
      (Command.declSig
       []
       (Term.typeSpec
        ":"
        (Term.app
         `DenseInducing
         [(AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termι "ι")])))
      (Command.declValSimple
       ":="
       (Term.anonymousCtor
        "⟨"
        [(Term.proj (Term.proj `pkg "." `UniformInducing) "." `Inducing)
         ","
         (Term.proj `pkg "." `dense)]
        "⟩")
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.proj (Term.proj `pkg "." `UniformInducing) "." `Inducing)
        ","
        (Term.proj `pkg "." `dense)]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `pkg "." `dense)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `pkg
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.proj `pkg "." `UniformInducing) "." `Inducing)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj `pkg "." `UniformInducing)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `pkg
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app
       `DenseInducing
       [(AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termι "ι")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termι', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termι', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termι "ι")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termι', expected 'AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termι._@.Topology.UniformSpace.AbstractCompletion._hyg.50'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem dense_inducing : DenseInducing ι := ⟨ pkg . UniformInducing . Inducing , pkg . dense ⟩
#align abstract_completion.dense_inducing AbstractCompletion.dense_inducing

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `uniform_continuous_coe [])
      (Command.declSig
       []
       (Term.typeSpec
        ":"
        (Term.app
         `UniformContinuous
         [(AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termι "ι")])))
      (Command.declValSimple
       ":="
       (Term.app `UniformInducing.uniform_continuous [(Term.proj `pkg "." `UniformInducing)])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `UniformInducing.uniform_continuous [(Term.proj `pkg "." `UniformInducing)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `pkg "." `UniformInducing)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `pkg
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `UniformInducing.uniform_continuous
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app
       `UniformContinuous
       [(AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termι "ι")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termι', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termι', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termι "ι")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termι', expected 'AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termι._@.Topology.UniformSpace.AbstractCompletion._hyg.50'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  uniform_continuous_coe
  : UniformContinuous ι
  := UniformInducing.uniform_continuous pkg . UniformInducing
#align abstract_completion.uniform_continuous_coe AbstractCompletion.uniform_continuous_coe

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `continuous_coe [])
      (Command.declSig
       []
       (Term.typeSpec
        ":"
        (Term.app
         `Continuous
         [(AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termι "ι")])))
      (Command.declValSimple
       ":="
       (Term.proj (Term.proj `pkg "." `uniform_continuous_coe) "." `Continuous)
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.proj `pkg "." `uniform_continuous_coe) "." `Continuous)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj `pkg "." `uniform_continuous_coe)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `pkg
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app
       `Continuous
       [(AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termι "ι")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termι', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termι', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termι "ι")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termι', expected 'AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termι._@.Topology.UniformSpace.AbstractCompletion._hyg.50'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem continuous_coe : Continuous ι := pkg . uniform_continuous_coe . Continuous
#align abstract_completion.continuous_coe AbstractCompletion.continuous_coe

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      []
      [(Term.attributes
        "@["
        [(Term.attrInstance (Term.attrKind []) (Attr.simple `elab_as_elim []))]
        "]")]
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `induction_on [])
      (Command.declSig
       [(Term.implicitBinder
         "{"
         [`p]
         [":"
          (Term.arrow
           (AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termhatα "hatα")
           "→"
           (Term.prop "Prop"))]
         "}")
        (Term.explicitBinder
         "("
         [`a]
         [":" (AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termhatα "hatα")]
         []
         ")")
        (Term.explicitBinder
         "("
         [`hp]
         [":"
          (Term.app
           `IsClosed
           [(Set.«term{_|_}»
             "{"
             (Std.ExtendedBinder.extBinder (Lean.binderIdent `a) [])
             "|"
             (Term.app `p [`a])
             "}")])]
         []
         ")")
        (Term.explicitBinder
         "("
         [`ih]
         [":"
          (Term.forall
           "∀"
           [`a]
           []
           ","
           (Term.app
            `p
            [(Term.app
              (AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termι "ι")
              [`a])]))]
         []
         ")")]
       (Term.typeSpec ":" (Term.app `p [`a])))
      (Command.declValSimple
       ":="
       (Term.app `is_closed_property [(Term.proj `pkg "." `dense) `hp `ih `a])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `is_closed_property [(Term.proj `pkg "." `dense) `hp `ih `a])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `ih
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hp
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj `pkg "." `dense)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `pkg
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `is_closed_property
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app `p [`a])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.forall
       "∀"
       [`a]
       []
       ","
       (Term.app
        `p
        [(Term.app (AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termι "ι") [`a])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `p
       [(Term.app (AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termι "ι") [`a])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termι "ι") [`a])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termι "ι")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termι', expected 'AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termι._@.Topology.UniformSpace.AbstractCompletion._hyg.50'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ elab_as_elim ]
  theorem
    induction_on
    { p : hatα → Prop } ( a : hatα ) ( hp : IsClosed { a | p a } ) ( ih : ∀ a , p ι a ) : p a
    := is_closed_property pkg . dense hp ih a
#align abstract_completion.induction_on AbstractCompletion.induction_on

variable {β : Type _}

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [(Command.protected "protected")] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `funext [])
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `TopologicalSpace [`β]) "]")
        (Term.instBinder "[" [] (Term.app `T2Space [`β]) "]")
        (Term.implicitBinder
         "{"
         [`f `g]
         [":"
          (Term.arrow
           (AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termhatα "hatα")
           "→"
           `β)]
         "}")
        (Term.explicitBinder "(" [`hf] [":" (Term.app `Continuous [`f])] [] ")")
        (Term.explicitBinder "(" [`hg] [":" (Term.app `Continuous [`g])] [] ")")
        (Term.explicitBinder
         "("
         [`h]
         [":"
          (Term.forall
           "∀"
           [`a]
           []
           ","
           («term_=_»
            (Term.app
             `f
             [(Term.app
               (AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termι "ι")
               [`a])])
            "="
            (Term.app
             `g
             [(Term.app
               (AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termι "ι")
               [`a])])))]
         []
         ")")]
       (Term.typeSpec ":" («term_=_» `f "=" `g)))
      (Command.declValSimple
       ":="
       (Term.app
        `funext
        [(Term.fun
          "fun"
          (Term.basicFun
           [`a]
           []
           "=>"
           (Term.app
            (Term.proj `pkg "." `induction_on)
            [`a (Term.app `is_closed_eq [`hf `hg]) `h])))])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `funext
       [(Term.fun
         "fun"
         (Term.basicFun
          [`a]
          []
          "=>"
          (Term.app
           (Term.proj `pkg "." `induction_on)
           [`a (Term.app `is_closed_eq [`hf `hg]) `h])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`a]
        []
        "=>"
        (Term.app (Term.proj `pkg "." `induction_on) [`a (Term.app `is_closed_eq [`hf `hg]) `h])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj `pkg "." `induction_on) [`a (Term.app `is_closed_eq [`hf `hg]) `h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `is_closed_eq [`hf `hg])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hg
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hf
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `is_closed_eq
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `is_closed_eq [`hf `hg]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `pkg "." `induction_on)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `pkg
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `funext
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_» `f "=" `g)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.forall
       "∀"
       [`a]
       []
       ","
       («term_=_»
        (Term.app
         `f
         [(Term.app (AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termι "ι") [`a])])
        "="
        (Term.app
         `g
         [(Term.app
           (AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termι "ι")
           [`a])])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Term.app
        `f
        [(Term.app (AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termι "ι") [`a])])
       "="
       (Term.app
        `g
        [(Term.app (AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termι "ι") [`a])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `g
       [(Term.app (AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termι "ι") [`a])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termι "ι") [`a])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termι "ι")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termι', expected 'AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termι._@.Topology.UniformSpace.AbstractCompletion._hyg.50'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
protected
  theorem
    funext
    [ TopologicalSpace β ]
        [ T2Space β ]
        { f g : hatα → β }
        ( hf : Continuous f )
        ( hg : Continuous g )
        ( h : ∀ a , f ι a = g ι a )
      : f = g
    := funext fun a => pkg . induction_on a is_closed_eq hf hg h
#align abstract_completion.funext AbstractCompletion.funext

variable [UniformSpace β]

section Extend

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment "/--" "Extension of maps to completions -/")]
      []
      [(Command.protected "protected")]
      []
      []
      [])
     (Command.def
      "def"
      (Command.declId `extend [])
      (Command.optDeclSig
       [(Term.explicitBinder "(" [`f] [":" (Term.arrow `α "→" `β)] [] ")")]
       [(Term.typeSpec
         ":"
         (Term.arrow
          (AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termhatα "hatα")
          "→"
          `β))])
      (Command.declValSimple
       ":="
       (termIfThenElse
        "if"
        (Term.app `UniformContinuous [`f])
        "then"
        (Term.app (Term.proj (Term.proj `pkg "." `DenseInducing) "." `extend) [`f])
        "else"
        (Term.fun
         "fun"
         (Term.basicFun
          [`x]
          []
          "=>"
          (Term.app `f [(Term.app (Term.proj (Term.proj `pkg "." `dense) "." `some) [`x])]))))
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (termIfThenElse
       "if"
       (Term.app `UniformContinuous [`f])
       "then"
       (Term.app (Term.proj (Term.proj `pkg "." `DenseInducing) "." `extend) [`f])
       "else"
       (Term.fun
        "fun"
        (Term.basicFun
         [`x]
         []
         "=>"
         (Term.app `f [(Term.app (Term.proj (Term.proj `pkg "." `dense) "." `some) [`x])]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`x]
        []
        "=>"
        (Term.app `f [(Term.app (Term.proj (Term.proj `pkg "." `dense) "." `some) [`x])])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `f [(Term.app (Term.proj (Term.proj `pkg "." `dense) "." `some) [`x])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj (Term.proj `pkg "." `dense) "." `some) [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.proj `pkg "." `dense) "." `some)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj `pkg "." `dense)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `pkg
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.proj (Term.proj `pkg "." `dense) "." `some) [`x])
     ")")
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
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj (Term.proj `pkg "." `DenseInducing) "." `extend) [`f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.proj `pkg "." `DenseInducing) "." `extend)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj `pkg "." `DenseInducing)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `pkg
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `UniformContinuous [`f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `UniformContinuous
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.arrow
       (AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termhatα "hatα")
       "→"
       `β)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `β
[PrettyPrinter.parenthesize] ...precedences are 25 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
      (AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termhatα "hatα")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termhatα', expected 'AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termhatα._@.Topology.UniformSpace.AbstractCompletion._hyg.7'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/-- Extension of maps to completions -/ protected
  def
    extend
    ( f : α → β ) : hatα → β
    :=
      if
        UniformContinuous f
        then
        pkg . DenseInducing . extend f
        else
        fun x => f pkg . dense . some x
#align abstract_completion.extend AbstractCompletion.extend

variable {f : α → β}

theorem extend_def (hf : UniformContinuous f) : pkg.extend f = pkg.DenseInducing.extend f :=
  if_pos hf
#align abstract_completion.extend_def AbstractCompletion.extend_def

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `extend_coe [])
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `T2Space [`β]) "]")
        (Term.explicitBinder "(" [`hf] [":" (Term.app `UniformContinuous [`f])] [] ")")
        (Term.explicitBinder "(" [`a] [":" `α] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app
          (Term.app (Term.proj `pkg "." `extend) [`f])
          [(Term.app (AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termι "ι") [`a])])
         "="
         (Term.app `f [`a]))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `pkg.extend_def [`hf]))] "]")
            [])
           []
           (Tactic.exact "exact" (Term.app `pkg.dense_inducing.extend_eq [`hf.continuous `a]))])))
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
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `pkg.extend_def [`hf]))] "]")
           [])
          []
          (Tactic.exact "exact" (Term.app `pkg.dense_inducing.extend_eq [`hf.continuous `a]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" (Term.app `pkg.dense_inducing.extend_eq [`hf.continuous `a]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `pkg.dense_inducing.extend_eq [`hf.continuous `a])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hf.continuous
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `pkg.dense_inducing.extend_eq
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `pkg.extend_def [`hf]))] "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `pkg.extend_def [`hf])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hf
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `pkg.extend_def
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app
        (Term.app (Term.proj `pkg "." `extend) [`f])
        [(Term.app (AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termι "ι") [`a])])
       "="
       (Term.app `f [`a]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `f [`a])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app
       (Term.app (Term.proj `pkg "." `extend) [`f])
       [(Term.app (AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termι "ι") [`a])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termι "ι") [`a])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termι "ι")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termι', expected 'AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termι._@.Topology.UniformSpace.AbstractCompletion._hyg.50'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  extend_coe
  [ T2Space β ] ( hf : UniformContinuous f ) ( a : α ) : pkg . extend f ι a = f a
  := by rw [ pkg.extend_def hf ] exact pkg.dense_inducing.extend_eq hf.continuous a
#align abstract_completion.extend_coe AbstractCompletion.extend_coe

variable [CompleteSpace β]

theorem uniform_continuous_extend : UniformContinuous (pkg.extend f) :=
  by
  by_cases hf : UniformContinuous f
  · rw [pkg.extend_def hf]
    exact uniform_continuous_uniformly_extend pkg.uniform_inducing pkg.dense hf
  · change UniformContinuous (ite _ _ _)
    rw [if_neg hf]
    exact uniform_continuous_of_const fun a b => by congr
#align abstract_completion.uniform_continuous_extend AbstractCompletion.uniform_continuous_extend

theorem continuous_extend : Continuous (pkg.extend f) :=
  pkg.uniform_continuous_extend.Continuous
#align abstract_completion.continuous_extend AbstractCompletion.continuous_extend

variable [SeparatedSpace β]

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `extend_unique [])
      (Command.declSig
       [(Term.explicitBinder "(" [`hf] [":" (Term.app `UniformContinuous [`f])] [] ")")
        (Term.implicitBinder
         "{"
         [`g]
         [":"
          (Term.arrow
           (AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termhatα "hatα")
           "→"
           `β)]
         "}")
        (Term.explicitBinder "(" [`hg] [":" (Term.app `UniformContinuous [`g])] [] ")")
        (Term.explicitBinder
         "("
         [`h]
         [":"
          (Term.forall
           "∀"
           [`a]
           [(Term.typeSpec ":" `α)]
           ","
           («term_=_»
            (Term.app `f [`a])
            "="
            (Term.app
             `g
             [(Term.app
               (AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termι "ι")
               [`a])])))]
         []
         ")")]
       (Term.typeSpec ":" («term_=_» (Term.app (Term.proj `pkg "." `extend) [`f]) "=" `g)))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.apply "apply" (Term.app `pkg.funext [`pkg.continuous_extend `hg.continuous]))
           []
           (Std.Tactic.Simpa.simpa
            "simpa"
            []
            []
            (Std.Tactic.Simpa.simpaArgsRest
             []
             []
             ["only"]
             [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] (Term.app `pkg.extend_coe [`hf]))] "]")]
             ["using" `h]))])))
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
         [(Tactic.apply "apply" (Term.app `pkg.funext [`pkg.continuous_extend `hg.continuous]))
          []
          (Std.Tactic.Simpa.simpa
           "simpa"
           []
           []
           (Std.Tactic.Simpa.simpaArgsRest
            []
            []
            ["only"]
            [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] (Term.app `pkg.extend_coe [`hf]))] "]")]
            ["using" `h]))])))
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
        [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] (Term.app `pkg.extend_coe [`hf]))] "]")]
        ["using" `h]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `pkg.extend_coe [`hf])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hf
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `pkg.extend_coe
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.apply "apply" (Term.app `pkg.funext [`pkg.continuous_extend `hg.continuous]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `pkg.funext [`pkg.continuous_extend `hg.continuous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hg.continuous
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `pkg.continuous_extend
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `pkg.funext
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_» (Term.app (Term.proj `pkg "." `extend) [`f]) "=" `g)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app (Term.proj `pkg "." `extend) [`f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `pkg "." `extend)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `pkg
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.forall
       "∀"
       [`a]
       [(Term.typeSpec ":" `α)]
       ","
       («term_=_»
        (Term.app `f [`a])
        "="
        (Term.app
         `g
         [(Term.app
           (AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termι "ι")
           [`a])])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Term.app `f [`a])
       "="
       (Term.app
        `g
        [(Term.app (AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termι "ι") [`a])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `g
       [(Term.app (AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termι "ι") [`a])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termι "ι") [`a])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termι "ι")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termι', expected 'AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termι._@.Topology.UniformSpace.AbstractCompletion._hyg.50'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  extend_unique
  ( hf : UniformContinuous f )
      { g : hatα → β }
      ( hg : UniformContinuous g )
      ( h : ∀ a : α , f a = g ι a )
    : pkg . extend f = g
  :=
    by apply pkg.funext pkg.continuous_extend hg.continuous simpa only [ pkg.extend_coe hf ] using h
#align abstract_completion.extend_unique AbstractCompletion.extend_unique

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
      (Command.declId `extend_comp_coe [])
      (Command.declSig
       [(Term.implicitBinder
         "{"
         [`f]
         [":"
          (Term.arrow
           (AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termhatα "hatα")
           "→"
           `β)]
         "}")
        (Term.explicitBinder "(" [`hf] [":" (Term.app `UniformContinuous [`f])] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app
          (Term.proj `pkg "." `extend)
          [(«term_∘_»
            `f
            "∘"
            (AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termι "ι"))])
         "="
         `f)))
      (Command.declValSimple
       ":="
       (Term.app
        `funext
        [(Term.fun
          "fun"
          (Term.basicFun
           [`x]
           []
           "=>"
           (Term.app
            (Term.proj `pkg "." `induction_on)
            [`x
             (Term.app
              `is_closed_eq
              [(Term.proj `pkg "." `continuous_extend) (Term.proj `hf "." `Continuous)])
             (Term.fun
              "fun"
              (Term.basicFun
               [`y]
               []
               "=>"
               (Term.app
                (Term.proj `pkg "." `extend_coe)
                [(«term_<|_»
                  (Term.proj `hf "." `comp)
                  "<|"
                  (Term.proj `pkg "." `uniform_continuous_coe))
                 `y])))])))])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `funext
       [(Term.fun
         "fun"
         (Term.basicFun
          [`x]
          []
          "=>"
          (Term.app
           (Term.proj `pkg "." `induction_on)
           [`x
            (Term.app
             `is_closed_eq
             [(Term.proj `pkg "." `continuous_extend) (Term.proj `hf "." `Continuous)])
            (Term.fun
             "fun"
             (Term.basicFun
              [`y]
              []
              "=>"
              (Term.app
               (Term.proj `pkg "." `extend_coe)
               [(«term_<|_»
                 (Term.proj `hf "." `comp)
                 "<|"
                 (Term.proj `pkg "." `uniform_continuous_coe))
                `y])))])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`x]
        []
        "=>"
        (Term.app
         (Term.proj `pkg "." `induction_on)
         [`x
          (Term.app
           `is_closed_eq
           [(Term.proj `pkg "." `continuous_extend) (Term.proj `hf "." `Continuous)])
          (Term.fun
           "fun"
           (Term.basicFun
            [`y]
            []
            "=>"
            (Term.app
             (Term.proj `pkg "." `extend_coe)
             [(«term_<|_»
               (Term.proj `hf "." `comp)
               "<|"
               (Term.proj `pkg "." `uniform_continuous_coe))
              `y])))])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj `pkg "." `induction_on)
       [`x
        (Term.app
         `is_closed_eq
         [(Term.proj `pkg "." `continuous_extend) (Term.proj `hf "." `Continuous)])
        (Term.fun
         "fun"
         (Term.basicFun
          [`y]
          []
          "=>"
          (Term.app
           (Term.proj `pkg "." `extend_coe)
           [(«term_<|_» (Term.proj `hf "." `comp) "<|" (Term.proj `pkg "." `uniform_continuous_coe))
            `y])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`y]
        []
        "=>"
        (Term.app
         (Term.proj `pkg "." `extend_coe)
         [(«term_<|_» (Term.proj `hf "." `comp) "<|" (Term.proj `pkg "." `uniform_continuous_coe))
          `y])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj `pkg "." `extend_coe)
       [(«term_<|_» (Term.proj `hf "." `comp) "<|" (Term.proj `pkg "." `uniform_continuous_coe))
        `y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_<|_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_<|_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      («term_<|_» (Term.proj `hf "." `comp) "<|" (Term.proj `pkg "." `uniform_continuous_coe))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `pkg "." `uniform_continuous_coe)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `pkg
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      (Term.proj `hf "." `comp)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hf
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 10, (some 10, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_<|_» (Term.proj `hf "." `comp) "<|" (Term.proj `pkg "." `uniform_continuous_coe))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `pkg "." `extend_coe)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `pkg
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
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
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.app
       `is_closed_eq
       [(Term.proj `pkg "." `continuous_extend) (Term.proj `hf "." `Continuous)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `hf "." `Continuous)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hf
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj `pkg "." `continuous_extend)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `pkg
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `is_closed_eq
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `is_closed_eq
      [(Term.proj `pkg "." `continuous_extend) (Term.proj `hf "." `Continuous)])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `pkg "." `induction_on)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `pkg
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `funext
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app
        (Term.proj `pkg "." `extend)
        [(«term_∘_»
          `f
          "∘"
          (AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termι "ι"))])
       "="
       `f)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app
       (Term.proj `pkg "." `extend)
       [(«term_∘_» `f "∘" (AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termι "ι"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_∘_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_∘_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∘_» `f "∘" (AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termι "ι"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termι "ι")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termι', expected 'AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termι._@.Topology.UniformSpace.AbstractCompletion._hyg.50'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ simp ]
  theorem
    extend_comp_coe
    { f : hatα → β } ( hf : UniformContinuous f ) : pkg . extend f ∘ ι = f
    :=
      funext
        fun
          x
            =>
            pkg . induction_on
              x
                is_closed_eq pkg . continuous_extend hf . Continuous
                fun y => pkg . extend_coe hf . comp <| pkg . uniform_continuous_coe y
#align abstract_completion.extend_comp_coe AbstractCompletion.extend_comp_coe

end Extend

section MapSec

variable (pkg' : AbstractCompletion β)

-- mathport name: exprhatβ
local notation "hatβ" => pkg'.Space

-- mathport name: exprι'
local notation "ι'" => pkg'.coe

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment "/--" "Lifting maps to completions -/")]
      []
      [(Command.protected "protected")]
      []
      []
      [])
     (Command.def
      "def"
      (Command.declId `map [])
      (Command.optDeclSig
       [(Term.explicitBinder "(" [`f] [":" (Term.arrow `α "→" `β)] [] ")")]
       [(Term.typeSpec
         ":"
         (Term.arrow
          (AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termhatα "hatα")
          "→"
          (AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termhatβ "hatβ")))])
      (Command.declValSimple
       ":="
       (Term.app
        (Term.proj `pkg "." `extend)
        [(«term_∘_»
          (AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termι' "ι'")
          "∘"
          `f)])
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj `pkg "." `extend)
       [(«term_∘_»
         (AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termι' "ι'")
         "∘"
         `f)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_∘_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_∘_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∘_» (AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termι' "ι'") "∘" `f)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 90 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 90, term))
      (AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termι' "ι'")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termι'', expected 'AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termι'._@.Topology.UniformSpace.AbstractCompletion._hyg.131'
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
/-- Lifting maps to completions -/ protected
  def map ( f : α → β ) : hatα → hatβ := pkg . extend ι' ∘ f
#align abstract_completion.map AbstractCompletion.map

-- mathport name: exprmap
local notation "map" => pkg.map pkg'

variable (f : α → β)

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `uniform_continuous_map [])
      (Command.declSig
       []
       (Term.typeSpec
        ":"
        (Term.app
         `UniformContinuous
         [(Term.app
           (AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termmap "map")
           [`f])])))
      (Command.declValSimple ":=" (Term.proj `pkg "." `uniform_continuous_extend) [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `pkg "." `uniform_continuous_extend)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `pkg
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app
       `UniformContinuous
       [(Term.app
         (AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termmap "map")
         [`f])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termmap "map") [`f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termmap "map")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termmap', expected 'AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termmap._@.Topology.UniformSpace.AbstractCompletion._hyg.170'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem uniform_continuous_map : UniformContinuous map f := pkg . uniform_continuous_extend
#align abstract_completion.uniform_continuous_map AbstractCompletion.uniform_continuous_map

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `continuous_map [])
      (Command.declSig
       []
       (Term.typeSpec
        ":"
        (Term.app
         `Continuous
         [(Term.app
           (AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termmap "map")
           [`f])])))
      (Command.declValSimple ":=" (Term.proj `pkg "." `continuous_extend) [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `pkg "." `continuous_extend)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `pkg
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app
       `Continuous
       [(Term.app
         (AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termmap "map")
         [`f])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termmap "map") [`f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termmap "map")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termmap', expected 'AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termmap._@.Topology.UniformSpace.AbstractCompletion._hyg.170'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem continuous_map : Continuous map f := pkg . continuous_extend
#align abstract_completion.continuous_map AbstractCompletion.continuous_map

variable {f}

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
      (Command.declId `map_coe [])
      (Command.declSig
       [(Term.explicitBinder "(" [`hf] [":" (Term.app `UniformContinuous [`f])] [] ")")
        (Term.explicitBinder "(" [`a] [":" `α] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app
          (AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termmap "map")
          [`f
           (Term.app (AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termι "ι") [`a])])
         "="
         (Term.app
          (AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termι' "ι'")
          [(Term.app `f [`a])]))))
      (Command.declValSimple
       ":="
       (Term.app
        (Term.proj `pkg "." `extend_coe)
        [(Term.app (Term.proj (Term.proj `pkg' "." `uniform_continuous_coe) "." `comp) [`hf]) `a])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj `pkg "." `extend_coe)
       [(Term.app (Term.proj (Term.proj `pkg' "." `uniform_continuous_coe) "." `comp) [`hf]) `a])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app (Term.proj (Term.proj `pkg' "." `uniform_continuous_coe) "." `comp) [`hf])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hf
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.proj `pkg' "." `uniform_continuous_coe) "." `comp)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj `pkg' "." `uniform_continuous_coe)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `pkg'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.proj (Term.proj `pkg' "." `uniform_continuous_coe) "." `comp) [`hf])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `pkg "." `extend_coe)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `pkg
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app
        (AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termmap "map")
        [`f
         (Term.app (AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termι "ι") [`a])])
       "="
       (Term.app
        (AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termι' "ι'")
        [(Term.app `f [`a])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termι' "ι'")
       [(Term.app `f [`a])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `f [`a])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `f [`a]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termι' "ι'")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termι'', expected 'AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termι'._@.Topology.UniformSpace.AbstractCompletion._hyg.131'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ simp ]
  theorem
    map_coe
    ( hf : UniformContinuous f ) ( a : α ) : map f ι a = ι' f a
    := pkg . extend_coe pkg' . uniform_continuous_coe . comp hf a
#align abstract_completion.map_coe AbstractCompletion.map_coe

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `map_unique [])
      (Command.declSig
       [(Term.implicitBinder "{" [`f] [":" (Term.arrow `α "→" `β)] "}")
        (Term.implicitBinder
         "{"
         [`g]
         [":"
          (Term.arrow
           (AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termhatα "hatα")
           "→"
           (AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termhatβ "hatβ"))]
         "}")
        (Term.explicitBinder "(" [`hg] [":" (Term.app `UniformContinuous [`g])] [] ")")
        (Term.explicitBinder
         "("
         [`h]
         [":"
          (Term.forall
           "∀"
           [`a]
           []
           ","
           («term_=_»
            (Term.app
             (AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termι' "ι'")
             [(Term.app `f [`a])])
            "="
            (Term.app
             `g
             [(Term.app
               (AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termι "ι")
               [`a])])))]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app (AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termmap "map") [`f])
         "="
         `g)))
      (Command.declValSimple
       ":="
       («term_<|_»
        (Term.app
         (Term.proj `pkg "." `funext)
         [(Term.app (Term.proj `pkg "." `continuous_map) [(Term.hole "_") (Term.hole "_")])
          (Term.proj `hg "." `Continuous)])
        "<|"
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Tactic.intro "intro" [`a])
            []
            (Tactic.change
             "change"
             («term_=_»
              (Term.app
               `pkg.extend
               [(«term_∘_»
                 (AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termι' "ι'")
                 "∘"
                 `f)
                (Term.hole "_")])
              "="
              (Term.hole "_"))
             [])
            []
            (Tactic.simp
             "simp"
             []
             []
             ["only"]
             ["["
              [(Tactic.simpLemma
                []
                []
                (Term.paren "(" («term_∘_» (Term.cdot "·") "∘" (Term.cdot "·")) ")"))
               ","
               (Tactic.simpLemma [] [] `h)]
              "]"]
             [])
            []
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule
                []
                (Term.app `pkg.extend_coe [(Term.app `hg.comp [`pkg.uniform_continuous_coe])]))]
              "]")
             [])]))))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_»
       (Term.app
        (Term.proj `pkg "." `funext)
        [(Term.app (Term.proj `pkg "." `continuous_map) [(Term.hole "_") (Term.hole "_")])
         (Term.proj `hg "." `Continuous)])
       "<|"
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.intro "intro" [`a])
           []
           (Tactic.change
            "change"
            («term_=_»
             (Term.app
              `pkg.extend
              [(«term_∘_»
                (AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termι' "ι'")
                "∘"
                `f)
               (Term.hole "_")])
             "="
             (Term.hole "_"))
            [])
           []
           (Tactic.simp
            "simp"
            []
            []
            ["only"]
            ["["
             [(Tactic.simpLemma
               []
               []
               (Term.paren "(" («term_∘_» (Term.cdot "·") "∘" (Term.cdot "·")) ")"))
              ","
              (Tactic.simpLemma [] [] `h)]
             "]"]
            [])
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule
               []
               (Term.app `pkg.extend_coe [(Term.app `hg.comp [`pkg.uniform_continuous_coe])]))]
             "]")
            [])]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.intro "intro" [`a])
          []
          (Tactic.change
           "change"
           («term_=_»
            (Term.app
             `pkg.extend
             [(«term_∘_»
               (AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termι' "ι'")
               "∘"
               `f)
              (Term.hole "_")])
            "="
            (Term.hole "_"))
           [])
          []
          (Tactic.simp
           "simp"
           []
           []
           ["only"]
           ["["
            [(Tactic.simpLemma
              []
              []
              (Term.paren "(" («term_∘_» (Term.cdot "·") "∘" (Term.cdot "·")) ")"))
             ","
             (Tactic.simpLemma [] [] `h)]
            "]"]
           [])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule
              []
              (Term.app `pkg.extend_coe [(Term.app `hg.comp [`pkg.uniform_continuous_coe])]))]
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
          (Term.app `pkg.extend_coe [(Term.app `hg.comp [`pkg.uniform_continuous_coe])]))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `pkg.extend_coe [(Term.app `hg.comp [`pkg.uniform_continuous_coe])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `hg.comp [`pkg.uniform_continuous_coe])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `pkg.uniform_continuous_coe
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `hg.comp
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `hg.comp [`pkg.uniform_continuous_coe])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `pkg.extend_coe
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
        [(Tactic.simpLemma
          []
          []
          (Term.paren "(" («term_∘_» (Term.cdot "·") "∘" (Term.cdot "·")) ")"))
         ","
         (Tactic.simpLemma [] [] `h)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.paren "(" («term_∘_» (Term.cdot "·") "∘" (Term.cdot "·")) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∘_» (Term.cdot "·") "∘" (Term.cdot "·"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.cdot "·")
[PrettyPrinter.parenthesize] ...precedences are 90 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 90, term))
      (Term.cdot "·")
[PrettyPrinter.parenthesize] ...precedences are 91 >? 1024, (none, [anonymous]) <=? (some 90, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 90, (some 90, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.change
       "change"
       («term_=_»
        (Term.app
         `pkg.extend
         [(«term_∘_»
           (AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termι' "ι'")
           "∘"
           `f)
          (Term.hole "_")])
        "="
        (Term.hole "_"))
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Term.app
        `pkg.extend
        [(«term_∘_»
          (AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termι' "ι'")
          "∘"
          `f)
         (Term.hole "_")])
       "="
       (Term.hole "_"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app
       `pkg.extend
       [(«term_∘_» (AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termι' "ι'") "∘" `f)
        (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_∘_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_∘_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      («term_∘_» (AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termι' "ι'") "∘" `f)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 90 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 90, term))
      (AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termι' "ι'")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termι'', expected 'AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termι'._@.Topology.UniformSpace.AbstractCompletion._hyg.131'
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
  map_unique
  { f : α → β } { g : hatα → hatβ } ( hg : UniformContinuous g ) ( h : ∀ a , ι' f a = g ι a )
    : map f = g
  :=
    pkg . funext pkg . continuous_map _ _ hg . Continuous
      <|
      by
        intro a
          change pkg.extend ι' ∘ f _ = _
          simp only [ ( · ∘ · ) , h ]
          rw [ pkg.extend_coe hg.comp pkg.uniform_continuous_coe ]
#align abstract_completion.map_unique AbstractCompletion.map_unique

@[simp]
theorem map_id : pkg.map pkg id = id :=
  pkg.map_unique pkg uniform_continuous_id fun a => rfl
#align abstract_completion.map_id AbstractCompletion.map_id

variable {γ : Type _} [UniformSpace γ]

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `extend_map [])
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `CompleteSpace [`γ]) "]")
        (Term.instBinder "[" [] (Term.app `SeparatedSpace [`γ]) "]")
        (Term.implicitBinder "{" [`f] [":" (Term.arrow `β "→" `γ)] "}")
        (Term.implicitBinder "{" [`g] [":" (Term.arrow `α "→" `β)] "}")
        (Term.explicitBinder "(" [`hf] [":" (Term.app `UniformContinuous [`f])] [] ")")
        (Term.explicitBinder "(" [`hg] [":" (Term.app `UniformContinuous [`g])] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         («term_∘_»
          (Term.app (Term.proj `pkg' "." `extend) [`f])
          "∘"
          (Term.app
           (AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termmap "map")
           [`g]))
         "="
         (Term.app (Term.proj `pkg "." `extend) [(«term_∘_» `f "∘" `g)]))))
      (Command.declValSimple
       ":="
       (Term.app
        (Term.app
         (Term.proj `pkg "." `funext)
         [(Term.app
           (Term.proj (Term.proj `pkg' "." `continuous_extend) "." `comp)
           [(Term.app (Term.proj `pkg "." `continuous_map) [`pkg' (Term.hole "_")])])
          (Term.proj `pkg "." `continuous_extend)])
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
              [(Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule [] (Term.app `pkg.extend_coe [(Term.app `hf.comp [`hg])]))
                  ","
                  (Tactic.rwRule [] `comp_app)
                  ","
                  (Tactic.rwRule [] (Term.app `pkg.map_coe [`pkg' `hg]))
                  ","
                  (Tactic.rwRule [] (Term.app `pkg'.extend_coe [`hf]))]
                 "]")
                [])])))))])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.app
        (Term.proj `pkg "." `funext)
        [(Term.app
          (Term.proj (Term.proj `pkg' "." `continuous_extend) "." `comp)
          [(Term.app (Term.proj `pkg "." `continuous_map) [`pkg' (Term.hole "_")])])
         (Term.proj `pkg "." `continuous_extend)])
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
             [(Tactic.rwSeq
               "rw"
               []
               (Tactic.rwRuleSeq
                "["
                [(Tactic.rwRule [] (Term.app `pkg.extend_coe [(Term.app `hf.comp [`hg])]))
                 ","
                 (Tactic.rwRule [] `comp_app)
                 ","
                 (Tactic.rwRule [] (Term.app `pkg.map_coe [`pkg' `hg]))
                 ","
                 (Tactic.rwRule [] (Term.app `pkg'.extend_coe [`hf]))]
                "]")
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
           [(Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] (Term.app `pkg.extend_coe [(Term.app `hf.comp [`hg])]))
               ","
               (Tactic.rwRule [] `comp_app)
               ","
               (Tactic.rwRule [] (Term.app `pkg.map_coe [`pkg' `hg]))
               ","
               (Tactic.rwRule [] (Term.app `pkg'.extend_coe [`hf]))]
              "]")
             [])])))))
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
            [(Tactic.rwRule [] (Term.app `pkg.extend_coe [(Term.app `hf.comp [`hg])]))
             ","
             (Tactic.rwRule [] `comp_app)
             ","
             (Tactic.rwRule [] (Term.app `pkg.map_coe [`pkg' `hg]))
             ","
             (Tactic.rwRule [] (Term.app `pkg'.extend_coe [`hf]))]
            "]")
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] (Term.app `pkg.extend_coe [(Term.app `hf.comp [`hg])]))
         ","
         (Tactic.rwRule [] `comp_app)
         ","
         (Tactic.rwRule [] (Term.app `pkg.map_coe [`pkg' `hg]))
         ","
         (Tactic.rwRule [] (Term.app `pkg'.extend_coe [`hf]))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `pkg'.extend_coe [`hf])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hf
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `pkg'.extend_coe
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `pkg.map_coe [`pkg' `hg])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hg
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `pkg'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `pkg.map_coe
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `comp_app
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `pkg.extend_coe [(Term.app `hf.comp [`hg])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `hf.comp [`hg])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hg
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `hf.comp
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `hf.comp [`hg]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `pkg.extend_coe
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.app
       (Term.proj `pkg "." `funext)
       [(Term.app
         (Term.proj (Term.proj `pkg' "." `continuous_extend) "." `comp)
         [(Term.app (Term.proj `pkg "." `continuous_map) [`pkg' (Term.hole "_")])])
        (Term.proj `pkg "." `continuous_extend)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `pkg "." `continuous_extend)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `pkg
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       (Term.proj (Term.proj `pkg' "." `continuous_extend) "." `comp)
       [(Term.app (Term.proj `pkg "." `continuous_map) [`pkg' (Term.hole "_")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj `pkg "." `continuous_map) [`pkg' (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      `pkg'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `pkg "." `continuous_map)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `pkg
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.proj `pkg "." `continuous_map) [`pkg' (Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.proj `pkg' "." `continuous_extend) "." `comp)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj `pkg' "." `continuous_extend)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `pkg'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      (Term.proj (Term.proj `pkg' "." `continuous_extend) "." `comp)
      [(Term.paren
        "("
        (Term.app (Term.proj `pkg "." `continuous_map) [`pkg' (Term.hole "_")])
        ")")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `pkg "." `funext)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `pkg
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1022, (some 1023,
     term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      (Term.proj `pkg "." `funext)
      [(Term.paren
        "("
        (Term.app
         (Term.proj (Term.proj `pkg' "." `continuous_extend) "." `comp)
         [(Term.paren
           "("
           (Term.app (Term.proj `pkg "." `continuous_map) [`pkg' (Term.hole "_")])
           ")")])
        ")")
       (Term.proj `pkg "." `continuous_extend)])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       («term_∘_»
        (Term.app (Term.proj `pkg' "." `extend) [`f])
        "∘"
        (Term.app (AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termmap "map") [`g]))
       "="
       (Term.app (Term.proj `pkg "." `extend) [(«term_∘_» `f "∘" `g)]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj `pkg "." `extend) [(«term_∘_» `f "∘" `g)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_∘_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_∘_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∘_» `f "∘" `g)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g
[PrettyPrinter.parenthesize] ...precedences are 90 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 90, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 91 >? 1024, (none, [anonymous]) <=? (some 90, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 90, (some 90, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_∘_» `f "∘" `g) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `pkg "." `extend)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `pkg
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      («term_∘_»
       (Term.app (Term.proj `pkg' "." `extend) [`f])
       "∘"
       (Term.app (AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termmap "map") [`g]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termmap "map") [`g])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termmap "map")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termmap', expected 'AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termmap._@.Topology.UniformSpace.AbstractCompletion._hyg.170'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  extend_map
  [ CompleteSpace γ ]
      [ SeparatedSpace γ ]
      { f : β → γ }
      { g : α → β }
      ( hf : UniformContinuous f )
      ( hg : UniformContinuous g )
    : pkg' . extend f ∘ map g = pkg . extend f ∘ g
  :=
    pkg . funext pkg' . continuous_extend . comp pkg . continuous_map pkg' _ pkg . continuous_extend
      fun
        a
          =>
          by rw [ pkg.extend_coe hf.comp hg , comp_app , pkg.map_coe pkg' hg , pkg'.extend_coe hf ]
#align abstract_completion.extend_map AbstractCompletion.extend_map

variable (pkg'' : AbstractCompletion γ)

theorem map_comp {g : β → γ} {f : α → β} (hg : UniformContinuous g) (hf : UniformContinuous f) :
    pkg'.map pkg'' g ∘ pkg.map pkg' f = pkg.map pkg'' (g ∘ f) :=
  pkg.extend_map pkg' (pkg''.uniform_continuous_coe.comp hg) hf
#align abstract_completion.map_comp AbstractCompletion.map_comp

end MapSec

section Compare

-- We can now compare two completion packages for the same uniform space
variable (pkg' : AbstractCompletion α)

/-- The comparison map between two completions of the same uniform space. -/
def compare : pkg.Space → pkg'.Space :=
  pkg.extend pkg'.coe
#align abstract_completion.compare AbstractCompletion.compare

theorem uniform_continuous_compare : UniformContinuous (pkg.compare pkg') :=
  pkg.uniform_continuous_extend
#align abstract_completion.uniform_continuous_compare AbstractCompletion.uniform_continuous_compare

theorem compare_coe (a : α) : pkg.compare pkg' (pkg.coe a) = pkg'.coe a :=
  pkg.extend_coe pkg'.uniform_continuous_coe a
#align abstract_completion.compare_coe AbstractCompletion.compare_coe

theorem inverse_compare : pkg.compare pkg' ∘ pkg'.compare pkg = id :=
  by
  have uc := pkg.uniform_continuous_compare pkg'
  have uc' := pkg'.uniform_continuous_compare pkg
  apply pkg'.funext (uc.comp uc').Continuous continuous_id
  intro a
  rw [comp_app, pkg'.compare_coe pkg, pkg.compare_coe pkg']
  rfl
#align abstract_completion.inverse_compare AbstractCompletion.inverse_compare

/-- The uniform bijection between two completions of the same uniform space. -/
def compareEquiv : pkg.Space ≃ᵤ pkg'.Space
    where
  toFun := pkg.compare pkg'
  invFun := pkg'.compare pkg
  left_inv := congr_fun (pkg'.inverse_compare pkg)
  right_inv := congr_fun (pkg.inverse_compare pkg')
  uniform_continuous_to_fun := uniform_continuous_compare _ _
  uniform_continuous_inv_fun := uniform_continuous_compare _ _
#align abstract_completion.compare_equiv AbstractCompletion.compareEquiv

theorem uniform_continuous_compare_equiv : UniformContinuous (pkg.compareEquiv pkg') :=
  pkg.uniform_continuous_compare pkg'
#align
  abstract_completion.uniform_continuous_compare_equiv AbstractCompletion.uniform_continuous_compare_equiv

theorem uniform_continuous_compare_equiv_symm : UniformContinuous (pkg.compareEquiv pkg').symm :=
  pkg'.uniform_continuous_compare pkg
#align
  abstract_completion.uniform_continuous_compare_equiv_symm AbstractCompletion.uniform_continuous_compare_equiv_symm

end Compare

section Prod

variable (pkg' : AbstractCompletion β)

-- mathport name: exprhatβ
local notation "hatβ" => pkg'.Space

-- mathport name: exprι'
local notation "ι'" => pkg'.coe

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment "/--" "Products of completions -/")]
      []
      [(Command.protected "protected")]
      []
      []
      [])
     (Command.def
      "def"
      (Command.declId `prod [])
      (Command.optDeclSig
       []
       [(Term.typeSpec ":" (Term.app `AbstractCompletion [(«term_×_» `α "×" `β)]))])
      (Command.whereStructInst
       "where"
       [(Command.whereStructField
         (Term.letDecl
          (Term.letIdDecl
           `Space
           []
           []
           ":="
           («term_×_»
            (AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termhatα "hatα")
            "×"
            (AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termhatβ_1 "hatβ")))))
        []
        (Command.whereStructField
         (Term.letDecl
          (Term.letIdDecl
           `coe
           [`p]
           []
           ":="
           (Term.anonymousCtor
            "⟨"
            [(Term.app
              (AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termι "ι")
              [(Term.proj `p "." (fieldIdx "1"))])
             ","
             (Term.app
              (AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termι'_1 "ι'")
              [(Term.proj `p "." (fieldIdx "2"))])]
            "⟩"))))
        []
        (Command.whereStructField
         (Term.letDecl (Term.letIdDecl `uniformStruct [] [] ":=" `Prod.uniformSpace)))
        []
        (Command.whereStructField
         (Term.letDecl
          (Term.letIdDecl
           `complete
           []
           []
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented [(Tactic.tacticInfer_instance "infer_instance")]))))))
        []
        (Command.whereStructField
         (Term.letDecl
          (Term.letIdDecl
           `separation
           []
           []
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented [(Tactic.tacticInfer_instance "infer_instance")]))))))
        []
        (Command.whereStructField
         (Term.letDecl
          (Term.letIdDecl
           `UniformInducing
           []
           []
           ":="
           (Term.app
            `UniformInducing.prod
            [(Term.proj `pkg "." `UniformInducing) (Term.proj `pkg' "." `UniformInducing)]))))
        []
        (Command.whereStructField
         (Term.letDecl
          (Term.letIdDecl
           `dense
           []
           []
           ":="
           (Term.app
            (Term.proj (Term.proj `pkg "." `dense) "." `prod_map)
            [(Term.proj `pkg' "." `dense)]))))]
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.whereStructInst', expected 'Lean.Parser.Command.declValSimple'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.whereStructInst', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj (Term.proj `pkg "." `dense) "." `prod_map)
       [(Term.proj `pkg' "." `dense)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `pkg' "." `dense)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `pkg'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.proj `pkg "." `dense) "." `prod_map)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj `pkg "." `dense)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `pkg
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `UniformInducing.prod
       [(Term.proj `pkg "." `UniformInducing) (Term.proj `pkg' "." `UniformInducing)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `pkg' "." `UniformInducing)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `pkg'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj `pkg "." `UniformInducing)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `pkg
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `UniformInducing.prod
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented [(Tactic.tacticInfer_instance "infer_instance")])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticInfer_instance "infer_instance")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented [(Tactic.tacticInfer_instance "infer_instance")])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticInfer_instance "infer_instance")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Prod.uniformSpace
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.app
         (AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termι "ι")
         [(Term.proj `p "." (fieldIdx "1"))])
        ","
        (Term.app
         (AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termι'_1 "ι'")
         [(Term.proj `p "." (fieldIdx "2"))])]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termι'_1 "ι'")
       [(Term.proj `p "." (fieldIdx "2"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `p "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termι'_1 "ι'")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termι'_1', expected 'AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termι'_1._@.Topology.UniformSpace.AbstractCompletion._hyg.252'
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
/-- Products of completions -/ protected
  def
    prod
    : AbstractCompletion α × β
    where
      Space := hatα × hatβ
        coe p := ⟨ ι p . 1 , ι' p . 2 ⟩
        uniformStruct := Prod.uniformSpace
        complete := by infer_instance
        separation := by infer_instance
        UniformInducing := UniformInducing.prod pkg . UniformInducing pkg' . UniformInducing
        dense := pkg . dense . prod_map pkg' . dense
#align abstract_completion.prod AbstractCompletion.prod

end Prod

section Extension₂

variable (pkg' : AbstractCompletion β)

-- mathport name: exprhatβ
local notation "hatβ" => pkg'.Space

-- mathport name: exprι'
local notation "ι'" => pkg'.coe

variable {γ : Type _} [UniformSpace γ]

open Function

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment "/--" "Extend two variable map to completions. -/")]
      []
      [(Command.protected "protected")]
      []
      []
      [])
     (Command.def
      "def"
      (Command.declId `extend₂ [])
      (Command.optDeclSig
       [(Term.explicitBinder "(" [`f] [":" (Term.arrow `α "→" (Term.arrow `β "→" `γ))] [] ")")]
       [(Term.typeSpec
         ":"
         (Term.arrow
          (AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termhatα "hatα")
          "→"
          (Term.arrow
           (AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termhatβ_2 "hatβ")
           "→"
           `γ)))])
      (Command.declValSimple
       ":="
       («term_<|_»
        `curry
        "<|"
        (Term.app
         (Term.proj (Term.app (Term.proj `pkg "." `Prod) [`pkg']) "." `extend)
         [(Term.app `uncurry [`f])]))
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_»
       `curry
       "<|"
       (Term.app
        (Term.proj (Term.app (Term.proj `pkg "." `Prod) [`pkg']) "." `extend)
        [(Term.app `uncurry [`f])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj (Term.app (Term.proj `pkg "." `Prod) [`pkg']) "." `extend)
       [(Term.app `uncurry [`f])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `uncurry [`f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `uncurry
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `uncurry [`f]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app (Term.proj `pkg "." `Prod) [`pkg']) "." `extend)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app (Term.proj `pkg "." `Prod) [`pkg'])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `pkg'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `pkg "." `Prod)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `pkg
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.proj `pkg "." `Prod) [`pkg'])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      `curry
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 10, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.arrow
       (AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termhatα "hatα")
       "→"
       (Term.arrow
        (AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termhatβ_2 "hatβ")
        "→"
        `γ))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.arrow
       (AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termhatβ_2 "hatβ")
       "→"
       `γ)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `γ
[PrettyPrinter.parenthesize] ...precedences are 25 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
      (AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termhatβ_2 "hatβ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termhatβ_2', expected 'AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termhatβ_2._@.Topology.UniformSpace.AbstractCompletion._hyg.293'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/-- Extend two variable map to completions. -/ protected
  def extend₂ ( f : α → β → γ ) : hatα → hatβ → γ := curry <| pkg . Prod pkg' . extend uncurry f
#align abstract_completion.extend₂ AbstractCompletion.extend₂

section SeparatedSpace

variable [SeparatedSpace γ] {f : α → β → γ}

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `extension₂_coe_coe [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`hf]
         [":" («term_<|_» `UniformContinuous "<|" (Term.app `uncurry [`f]))]
         []
         ")")
        (Term.explicitBinder "(" [`a] [":" `α] [] ")")
        (Term.explicitBinder "(" [`b] [":" `β] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app
          (Term.proj `pkg "." `extend₂)
          [`pkg'
           `f
           (Term.app (AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termι "ι") [`a])
           (Term.app
            (AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termι'_2 "ι'")
            [`b])])
         "="
         (Term.app `f [`a `b]))))
      (Command.declValSimple
       ":="
       (Term.show
        "show"
        («term_=_»
         (Term.app
          (Term.proj (Term.app (Term.proj `pkg "." `Prod) [`pkg']) "." `extend)
          [(Term.app `uncurry [`f])
           (Term.app
            (Term.proj (Term.app (Term.proj `pkg "." `Prod) [`pkg']) "." `coe)
            [(Term.tuple "(" [`a "," [`b]] ")")])])
         "="
         (Term.app `uncurry [`f (Term.tuple "(" [`a "," [`b]] ")")]))
        (Term.fromTerm
         "from"
         (Term.app
          (Term.proj (Term.app (Term.proj `pkg "." `Prod) [`pkg']) "." `extend_coe)
          [`hf (Term.hole "_")])))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.show
       "show"
       («term_=_»
        (Term.app
         (Term.proj (Term.app (Term.proj `pkg "." `Prod) [`pkg']) "." `extend)
         [(Term.app `uncurry [`f])
          (Term.app
           (Term.proj (Term.app (Term.proj `pkg "." `Prod) [`pkg']) "." `coe)
           [(Term.tuple "(" [`a "," [`b]] ")")])])
        "="
        (Term.app `uncurry [`f (Term.tuple "(" [`a "," [`b]] ")")]))
       (Term.fromTerm
        "from"
        (Term.app
         (Term.proj (Term.app (Term.proj `pkg "." `Prod) [`pkg']) "." `extend_coe)
         [`hf (Term.hole "_")])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj (Term.app (Term.proj `pkg "." `Prod) [`pkg']) "." `extend_coe)
       [`hf (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      `hf
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app (Term.proj `pkg "." `Prod) [`pkg']) "." `extend_coe)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app (Term.proj `pkg "." `Prod) [`pkg'])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `pkg'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `pkg "." `Prod)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `pkg
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.proj `pkg "." `Prod) [`pkg'])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app
        (Term.proj (Term.app (Term.proj `pkg "." `Prod) [`pkg']) "." `extend)
        [(Term.app `uncurry [`f])
         (Term.app
          (Term.proj (Term.app (Term.proj `pkg "." `Prod) [`pkg']) "." `coe)
          [(Term.tuple "(" [`a "," [`b]] ")")])])
       "="
       (Term.app `uncurry [`f (Term.tuple "(" [`a "," [`b]] ")")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `uncurry [`f (Term.tuple "(" [`a "," [`b]] ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.tuple', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.tuple', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.tuple "(" [`a "," [`b]] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `b
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `uncurry
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app
       (Term.proj (Term.app (Term.proj `pkg "." `Prod) [`pkg']) "." `extend)
       [(Term.app `uncurry [`f])
        (Term.app
         (Term.proj (Term.app (Term.proj `pkg "." `Prod) [`pkg']) "." `coe)
         [(Term.tuple "(" [`a "," [`b]] ")")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj (Term.app (Term.proj `pkg "." `Prod) [`pkg']) "." `coe)
       [(Term.tuple "(" [`a "," [`b]] ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.tuple', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.tuple', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.tuple "(" [`a "," [`b]] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `b
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app (Term.proj `pkg "." `Prod) [`pkg']) "." `coe)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app (Term.proj `pkg "." `Prod) [`pkg'])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `pkg'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `pkg "." `Prod)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `pkg
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.proj `pkg "." `Prod) [`pkg'])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      (Term.proj (Term.paren "(" (Term.app (Term.proj `pkg "." `Prod) [`pkg']) ")") "." `coe)
      [(Term.tuple "(" [`a "," [`b]] ")")])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `uncurry [`f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `uncurry
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `uncurry [`f]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app (Term.proj `pkg "." `Prod) [`pkg']) "." `extend)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app (Term.proj `pkg "." `Prod) [`pkg'])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `pkg'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `pkg "." `Prod)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `pkg
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.proj `pkg "." `Prod) [`pkg'])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app
        (Term.proj `pkg "." `extend₂)
        [`pkg'
         `f
         (Term.app (AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termι "ι") [`a])
         (Term.app
          (AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termι'_2 "ι'")
          [`b])])
       "="
       (Term.app `f [`a `b]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `f [`a `b])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `b
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app
       (Term.proj `pkg "." `extend₂)
       [`pkg'
        `f
        (Term.app (AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termι "ι") [`a])
        (Term.app
         (AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termι'_2 "ι'")
         [`b])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termι'_2 "ι'") [`b])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `b
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termι'_2 "ι'")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termι'_2', expected 'AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termι'_2._@.Topology.UniformSpace.AbstractCompletion._hyg.332'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  extension₂_coe_coe
  ( hf : UniformContinuous <| uncurry f ) ( a : α ) ( b : β )
    : pkg . extend₂ pkg' f ι a ι' b = f a b
  :=
    show
      pkg . Prod pkg' . extend uncurry f pkg . Prod pkg' . coe ( a , b ) = uncurry f ( a , b )
      from pkg . Prod pkg' . extend_coe hf _
#align abstract_completion.extension₂_coe_coe AbstractCompletion.extension₂_coe_coe

end SeparatedSpace

variable {f : α → β → γ}

variable [CompleteSpace γ] (f)

theorem uniform_continuous_extension₂ : UniformContinuous₂ (pkg.extend₂ pkg' f) :=
  by
  rw [uniform_continuous₂_def, AbstractCompletion.extend₂, uncurry_curry]
  apply uniform_continuous_extend
#align
  abstract_completion.uniform_continuous_extension₂ AbstractCompletion.uniform_continuous_extension₂

end Extension₂

section Map₂

variable (pkg' : AbstractCompletion β)

-- mathport name: exprhatβ
local notation "hatβ" => pkg'.Space

-- mathport name: exprι'
local notation "ι'" => pkg'.coe

variable {γ : Type _} [UniformSpace γ] (pkg'' : AbstractCompletion γ)

-- mathport name: exprhatγ
local notation "hatγ" => pkg''.Space

-- mathport name: exprι''
local notation "ι''" => pkg''.coe

-- mathport name: «expr ∘₂ »
local notation f " ∘₂ " g => bicompr f g

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment "/--" "Lift two variable maps to completions. -/")]
      []
      [(Command.protected "protected")]
      []
      []
      [])
     (Command.def
      "def"
      (Command.declId `map₂ [])
      (Command.optDeclSig
       [(Term.explicitBinder "(" [`f] [":" (Term.arrow `α "→" (Term.arrow `β "→" `γ))] [] ")")]
       [(Term.typeSpec
         ":"
         (Term.arrow
          (AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termhatα "hatα")
          "→"
          (Term.arrow
           (AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termhatβ_3 "hatβ")
           "→"
           (AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termhatγ "hatγ"))))])
      (Command.declValSimple
       ":="
       (Term.app
        (Term.proj `pkg "." `extend₂)
        [`pkg'
         (AbstractCompletion.Topology.UniformSpace.AbstractCompletion.«term_∘₂_»
          (Term.proj `pkg'' "." `coe)
          " ∘₂ "
          `f)])
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj `pkg "." `extend₂)
       [`pkg'
        (AbstractCompletion.Topology.UniformSpace.AbstractCompletion.«term_∘₂_»
         (Term.proj `pkg'' "." `coe)
         " ∘₂ "
         `f)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AbstractCompletion.Topology.UniformSpace.AbstractCompletion.«term_∘₂_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AbstractCompletion.Topology.UniformSpace.AbstractCompletion.«term_∘₂_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (AbstractCompletion.Topology.UniformSpace.AbstractCompletion.«term_∘₂_»
       (Term.proj `pkg'' "." `coe)
       " ∘₂ "
       `f)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AbstractCompletion.Topology.UniformSpace.AbstractCompletion.«term_∘₂_»', expected 'AbstractCompletion.Topology.UniformSpace.AbstractCompletion.term_∘₂_._@.Topology.UniformSpace.AbstractCompletion._hyg.532'
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
/-- Lift two variable maps to completions. -/ protected
  def map₂ ( f : α → β → γ ) : hatα → hatβ → hatγ := pkg . extend₂ pkg' pkg'' . coe ∘₂ f
#align abstract_completion.map₂ AbstractCompletion.map₂

theorem uniform_continuous_map₂ (f : α → β → γ) : UniformContinuous₂ (pkg.map₂ pkg' pkg'' f) :=
  pkg.uniform_continuous_extension₂ pkg' _
#align abstract_completion.uniform_continuous_map₂ AbstractCompletion.uniform_continuous_map₂

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `continuous_map₂ [])
      (Command.declSig
       [(Term.implicitBinder "{" [`δ] [] "}")
        (Term.instBinder "[" [] (Term.app `TopologicalSpace [`δ]) "]")
        (Term.implicitBinder "{" [`f] [":" (Term.arrow `α "→" (Term.arrow `β "→" `γ))] "}")
        (Term.implicitBinder
         "{"
         [`a]
         [":"
          (Term.arrow
           `δ
           "→"
           (AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termhatα "hatα"))]
         "}")
        (Term.implicitBinder
         "{"
         [`b]
         [":"
          (Term.arrow
           `δ
           "→"
           (AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termhatβ_3 "hatβ"))]
         "}")
        (Term.explicitBinder "(" [`ha] [":" (Term.app `Continuous [`a])] [] ")")
        (Term.explicitBinder "(" [`hb] [":" (Term.app `Continuous [`b])] [] ")")]
       (Term.typeSpec
        ":"
        (Term.app
         `Continuous
         [(Term.fun
           "fun"
           (Term.basicFun
            [`d]
            [(Term.typeSpec ":" `δ)]
            "=>"
            (Term.app
             (Term.proj `pkg "." `map₂)
             [`pkg' `pkg'' `f (Term.app `a [`d]) (Term.app `b [`d])])))])))
      (Command.declValSimple
       ":="
       (Term.typeAscription
        "("
        (Term.app
         (Term.proj
          (Term.proj
           (Term.app (Term.proj `pkg "." `uniform_continuous_map₂) [`pkg' `pkg'' `f])
           "."
           `Continuous)
          "."
          `comp)
         [(Term.app `Continuous.prod_mk [`ha `hb])])
        ":"
        [(Term.hole "_")]
        ")")
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription
       "("
       (Term.app
        (Term.proj
         (Term.proj
          (Term.app (Term.proj `pkg "." `uniform_continuous_map₂) [`pkg' `pkg'' `f])
          "."
          `Continuous)
         "."
         `comp)
        [(Term.app `Continuous.prod_mk [`ha `hb])])
       ":"
       [(Term.hole "_")]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (Term.proj
         (Term.app (Term.proj `pkg "." `uniform_continuous_map₂) [`pkg' `pkg'' `f])
         "."
         `Continuous)
        "."
        `comp)
       [(Term.app `Continuous.prod_mk [`ha `hb])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Continuous.prod_mk [`ha `hb])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hb
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `ha
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Continuous.prod_mk
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `Continuous.prod_mk [`ha `hb])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (Term.proj
        (Term.app (Term.proj `pkg "." `uniform_continuous_map₂) [`pkg' `pkg'' `f])
        "."
        `Continuous)
       "."
       `comp)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj
       (Term.app (Term.proj `pkg "." `uniform_continuous_map₂) [`pkg' `pkg'' `f])
       "."
       `Continuous)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app (Term.proj `pkg "." `uniform_continuous_map₂) [`pkg' `pkg'' `f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `pkg''
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `pkg'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `pkg "." `uniform_continuous_map₂)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `pkg
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.proj `pkg "." `uniform_continuous_map₂) [`pkg' `pkg'' `f])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app
       `Continuous
       [(Term.fun
         "fun"
         (Term.basicFun
          [`d]
          [(Term.typeSpec ":" `δ)]
          "=>"
          (Term.app
           (Term.proj `pkg "." `map₂)
           [`pkg' `pkg'' `f (Term.app `a [`d]) (Term.app `b [`d])])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`d]
        [(Term.typeSpec ":" `δ)]
        "=>"
        (Term.app
         (Term.proj `pkg "." `map₂)
         [`pkg' `pkg'' `f (Term.app `a [`d]) (Term.app `b [`d])])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj `pkg "." `map₂) [`pkg' `pkg'' `f (Term.app `a [`d]) (Term.app `b [`d])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `b [`d])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `d
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `b
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `b [`d]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `a [`d])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `d
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `a [`d]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `pkg''
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `pkg'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `pkg "." `map₂)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `pkg
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `δ
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      `d
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Continuous
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Continuous [`b])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `b
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Continuous
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Continuous [`a])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Continuous
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.implicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.implicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.implicitBinder', expected 'Lean.Parser.Term.explicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.implicitBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.arrow
       `δ
       "→"
       (AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termhatβ_3 "hatβ"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termhatβ_3 "hatβ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termhatβ_3', expected 'AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termhatβ_3._@.Topology.UniformSpace.AbstractCompletion._hyg.376'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.implicitBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  continuous_map₂
  { δ }
      [ TopologicalSpace δ ]
      { f : α → β → γ }
      { a : δ → hatα }
      { b : δ → hatβ }
      ( ha : Continuous a )
      ( hb : Continuous b )
    : Continuous fun d : δ => pkg . map₂ pkg' pkg'' f a d b d
  := ( pkg . uniform_continuous_map₂ pkg' pkg'' f . Continuous . comp Continuous.prod_mk ha hb : _ )
#align abstract_completion.continuous_map₂ AbstractCompletion.continuous_map₂

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `map₂_coe_coe [])
      (Command.declSig
       [(Term.explicitBinder "(" [`a] [":" `α] [] ")")
        (Term.explicitBinder "(" [`b] [":" `β] [] ")")
        (Term.explicitBinder "(" [`f] [":" (Term.arrow `α "→" (Term.arrow `β "→" `γ))] [] ")")
        (Term.explicitBinder "(" [`hf] [":" (Term.app `UniformContinuous₂ [`f])] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app
          (Term.proj `pkg "." `map₂)
          [`pkg'
           `pkg''
           `f
           (Term.app (AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termι "ι") [`a])
           (Term.app
            (AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termι'_3 "ι'")
            [`b])])
         "="
         (Term.app
          (AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termι'' "ι''")
          [(Term.app `f [`a `b])]))))
      (Command.declValSimple
       ":="
       (Term.app
        (Term.proj `pkg "." `extension₂_coe_coe)
        [`pkg'
         (Term.app (Term.proj (Term.proj `pkg'' "." `uniform_continuous_coe) "." `comp) [`hf])
         `a
         `b])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj `pkg "." `extension₂_coe_coe)
       [`pkg'
        (Term.app (Term.proj (Term.proj `pkg'' "." `uniform_continuous_coe) "." `comp) [`hf])
        `a
        `b])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `b
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app (Term.proj (Term.proj `pkg'' "." `uniform_continuous_coe) "." `comp) [`hf])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hf
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.proj `pkg'' "." `uniform_continuous_coe) "." `comp)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj `pkg'' "." `uniform_continuous_coe)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `pkg''
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.proj (Term.proj `pkg'' "." `uniform_continuous_coe) "." `comp) [`hf])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `pkg'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `pkg "." `extension₂_coe_coe)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `pkg
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app
        (Term.proj `pkg "." `map₂)
        [`pkg'
         `pkg''
         `f
         (Term.app (AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termι "ι") [`a])
         (Term.app
          (AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termι'_3 "ι'")
          [`b])])
       "="
       (Term.app
        (AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termι'' "ι''")
        [(Term.app `f [`a `b])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termι'' "ι''")
       [(Term.app `f [`a `b])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `f [`a `b])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `b
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `f [`a `b]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termι'' "ι''")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termι''', expected 'AbstractCompletion.Topology.UniformSpace.AbstractCompletion.termι''._@.Topology.UniformSpace.AbstractCompletion._hyg.493'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  map₂_coe_coe
  ( a : α ) ( b : β ) ( f : α → β → γ ) ( hf : UniformContinuous₂ f )
    : pkg . map₂ pkg' pkg'' f ι a ι' b = ι'' f a b
  := pkg . extension₂_coe_coe pkg' pkg'' . uniform_continuous_coe . comp hf a b
#align abstract_completion.map₂_coe_coe AbstractCompletion.map₂_coe_coe

end Map₂

end AbstractCompletion

