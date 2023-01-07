/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang

! This file was ported from Lean 3 source module algebraic_geometry.open_immersion
! leanprover-community/mathlib commit 6afc9b06856ad973f6a2619e3e8a0a8d537a58f2
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.AlgebraicGeometry.PresheafedSpace.HasColimits
import Mathbin.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathbin.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
import Mathbin.Topology.Sheaves.Functors
import Mathbin.AlgebraicGeometry.SchemeCat
import Mathbin.CategoryTheory.Limits.Shapes.StrictInitial
import Mathbin.CategoryTheory.Limits.Shapes.CommSq
import Mathbin.Algebra.Category.RingCat.Instances
import Mathbin.Topology.LocalAtTarget

/-!
# Open immersions of structured spaces

We say that a morphism of presheafed spaces `f : X ⟶ Y` is an open immersions if
the underlying map of spaces is an open embedding `f : X ⟶ U ⊆ Y`,
and the sheaf map `Y(V) ⟶ f _* X(V)` is an iso for each `V ⊆ U`.

Abbreviations are also provided for `SheafedSpace`, `LocallyRingedSpace` and `Scheme`.

## Main definitions

* `algebraic_geometry.PresheafedSpace.is_open_immersion`: the `Prop`-valued typeclass asserting
  that a PresheafedSpace hom `f` is an open_immersion.
* `algebraic_geometry.is_open_immersion`: the `Prop`-valued typeclass asserting
  that a Scheme morphism `f` is an open_immersion.
* `algebraic_geometry.PresheafedSpace.is_open_immersion.iso_restrict`: The source of an
  open immersion is isomorphic to the restriction of the target onto the image.
* `algebraic_geometry.PresheafedSpace.is_open_immersion.lift`: Any morphism whose range is
  contained in an open immersion factors though the open immersion.
* `algebraic_geometry.PresheafedSpace.is_open_immersion.to_SheafedSpace`: If `f : X ⟶ Y` is an
  open immersion of presheafed spaces, and `Y` is a sheafed space, then `X` is also a sheafed
  space. The morphism as morphisms of sheafed spaces is given by `to_SheafedSpace_hom`.
* `algebraic_geometry.PresheafedSpace.is_open_immersion.to_LocallyRingedSpace`: If `f : X ⟶ Y` is
  an open immersion of presheafed spaces, and `Y` is a locally ringed space, then `X` is also a
  locally ringed space. The morphism as morphisms of locally ringed spaces is given by
  `to_LocallyRingedSpace_hom`.

## Main results

* `algebraic_geometry.PresheafedSpace.is_open_immersion.comp`: The composition of two open
  immersions is an open immersion.
* `algebraic_geometry.PresheafedSpace.is_open_immersion.of_iso`: An iso is an open immersion.
* `algebraic_geometry.PresheafedSpace.is_open_immersion.to_iso`:
  A surjective open immersion is an isomorphism.
* `algebraic_geometry.PresheafedSpace.is_open_immersion.stalk_iso`: An open immersion induces
  an isomorphism on stalks.
* `algebraic_geometry.PresheafedSpace.is_open_immersion.has_pullback_of_left`: If `f` is an open
  immersion, then the pullback `(f, g)` exists (and the forgetful functor to `Top` preserves it).
* `algebraic_geometry.PresheafedSpace.is_open_immersion.pullback_snd_of_left`: Open immersions
  are stable under pullbacks.
* `algebraic_geometry.SheafedSpace.is_open_immersion.of_stalk_iso` An (topological) open embedding
  between two sheafed spaces is an open immersion if all the stalk maps are isomorphisms.

-/


open TopologicalSpace CategoryTheory Opposite

open CategoryTheory.Limits

namespace AlgebraicGeometry

universe v v₁ v₂ u

variable {C : Type u} [Category.{v} C]

/-- An open immersion of PresheafedSpaces is an open embedding `f : X ⟶ U ⊆ Y` of the underlying
spaces, such that the sheaf map `Y(V) ⟶ f _* X(V)` is an iso for each `V ⊆ U`.
-/
class PresheafedSpaceCat.IsOpenImmersion {X Y : PresheafedSpaceCat.{v} C} (f : X ⟶ Y) : Prop where
  base_open : OpenEmbedding f.base
  c_iso : ∀ U : Opens X, IsIso (f.c.app (op (base_open.IsOpenMap.Functor.obj U)))
#align
  algebraic_geometry.PresheafedSpace.is_open_immersion AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion

/-- A morphism of SheafedSpaces is an open immersion if it is an open immersion as a morphism
of PresheafedSpaces
-/
abbrev SheafedSpaceCat.IsOpenImmersion {X Y : SheafedSpaceCat.{v} C} (f : X ⟶ Y) : Prop :=
  PresheafedSpaceCat.IsOpenImmersion f
#align
  algebraic_geometry.SheafedSpace.is_open_immersion AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion

/-- A morphism of LocallyRingedSpaces is an open immersion if it is an open immersion as a morphism
of SheafedSpaces
-/
abbrev LocallyRingedSpaceCat.IsOpenImmersion {X Y : LocallyRingedSpaceCat} (f : X ⟶ Y) : Prop :=
  SheafedSpaceCat.IsOpenImmersion f.1
#align
  algebraic_geometry.LocallyRingedSpace.is_open_immersion AlgebraicGeometry.LocallyRingedSpaceCat.IsOpenImmersion

/-- A morphism of Schemes is an open immersion if it is an open immersion as a morphism
of LocallyRingedSpaces
-/
abbrev IsOpenImmersion {X Y : SchemeCat} (f : X ⟶ Y) : Prop :=
  LocallyRingedSpaceCat.IsOpenImmersion f
#align algebraic_geometry.is_open_immersion AlgebraicGeometry.IsOpenImmersion

namespace PresheafedSpaceCat.IsOpenImmersion

open PresheafedSpaceCat

-- mathport name: expris_open_immersion
local notation "is_open_immersion" => PresheafedSpaceCat.IsOpenImmersion

attribute [instance] is_open_immersion.c_iso

section

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.variable
     "variable"
     [(Term.implicitBinder
       "{"
       [`X `Y]
       [":" (Term.app (Term.explicitUniv `PresheafedSpaceCat ".{" [`v] "}") [`C])]
       "}")
      (Term.implicitBinder "{" [`f] [":" (Combinatorics.Quiver.Basic.«term_⟶_» `X " ⟶ " `Y)] "}")
      (Term.explicitBinder
       "("
       [`H]
       [":"
        (Term.app
         (AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termis_open_immersion
          "is_open_immersion")
         [`f])]
       []
       ")")])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termis_open_immersion
        "is_open_immersion")
       [`f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termis_open_immersion
       "is_open_immersion")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termis_open_immersion', expected 'AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termis_open_immersion._@.AlgebraicGeometry.OpenImmersion._hyg.21'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.instBinder'-/-- failed to format: format: uncaught backtrack exception
variable { X Y : PresheafedSpaceCat .{ v } C } { f : X ⟶ Y } ( H : is_open_immersion f )

/-- The functor `opens X ⥤ opens Y` associated with an open immersion `f : X ⟶ Y`. -/
abbrev openFunctor :=
  H.base_open.IsOpenMap.Functor
#align
  algebraic_geometry.PresheafedSpace.is_open_immersion.open_functor AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.openFunctor

/-- An open immersion `f : X ⟶ Y` induces an isomorphism `X ≅ Y|_{f(X)}`. -/
@[simps hom_c_app]
noncomputable def isoRestrict : X ≅ Y.restrict H.base_open :=
  PresheafedSpaceCat.isoOfComponents (Iso.refl _)
    (by
      symm
      fapply nat_iso.of_components
      intro U
      refine'
        as_iso (f.c.app (op (H.open_functor.obj (unop U)))) ≪≫ X.presheaf.map_iso (eq_to_iso _)
      · induction U using Opposite.rec
        cases U
        dsimp only [IsOpenMap.functor, functor.op, opens.map]
        congr 2
        erw [Set.preimage_image_eq _ H.base_open.inj]
        rfl
      · intro U V i
        simp only [CategoryTheory.eqToIso.hom, TopCat.Presheaf.pushforward_obj_map, category.assoc,
          functor.op_map, iso.trans_hom, as_iso_hom, functor.map_iso_hom, ← X.presheaf.map_comp]
        erw [f.c.naturality_assoc, ← X.presheaf.map_comp]
        congr )
#align
  algebraic_geometry.PresheafedSpace.is_open_immersion.iso_restrict AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.isoRestrict

@[simp]
theorem iso_restrict_hom_of_restrict : H.isoRestrict.Hom ≫ Y.of_restrict _ = f :=
  by
  ext
  · simp only [comp_c_app, iso_restrict_hom_c_app, nat_trans.comp_app, eq_to_hom_refl,
      of_restrict_c_app, category.assoc, whisker_right_id']
    erw [category.comp_id, f.c.naturality_assoc, ← X.presheaf.map_comp]
    trans f.c.app x ≫ X.presheaf.map (𝟙 _)
    · congr
    · erw [X.presheaf.map_id, category.comp_id]
  · rfl
#align
  algebraic_geometry.PresheafedSpace.is_open_immersion.iso_restrict_hom_of_restrict AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.iso_restrict_hom_of_restrict

@[simp]
theorem iso_restrict_inv_of_restrict : H.isoRestrict.inv ≫ f = Y.of_restrict _ := by
  rw [iso.inv_comp_eq, iso_restrict_hom_of_restrict]
#align
  algebraic_geometry.PresheafedSpace.is_open_immersion.iso_restrict_inv_of_restrict AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.iso_restrict_inv_of_restrict

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.instance
      (Term.attrKind [])
      "instance"
      []
      [(Command.declId `mono [])]
      (Command.declSig
       [(Term.instBinder
         "["
         [`H ":"]
         (Term.app
          (AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termis_open_immersion
           "is_open_immersion")
          [`f])
         "]")]
       (Term.typeSpec ":" (Term.app `Mono [`f])))
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
             [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `H.iso_restrict_hom_of_restrict)]
             "]")
            [])
           []
           (Tactic.apply "apply" `mono_comp)])))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.opaque'
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
            [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `H.iso_restrict_hom_of_restrict)]
            "]")
           [])
          []
          (Tactic.apply "apply" `mono_comp)])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.apply "apply" `mono_comp)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mono_comp
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `H.iso_restrict_hom_of_restrict)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `H.iso_restrict_hom_of_restrict
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app `Mono [`f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Mono
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.instBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.instBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.instBinder', expected 'Lean.Parser.Term.explicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.instBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.instBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termis_open_immersion
        "is_open_immersion")
       [`f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termis_open_immersion
       "is_open_immersion")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termis_open_immersion', expected 'AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termis_open_immersion._@.AlgebraicGeometry.OpenImmersion._hyg.21'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
instance
  mono
  [ H : is_open_immersion f ] : Mono f
  := by rw [ ← H.iso_restrict_hom_of_restrict ] apply mono_comp
#align
  algebraic_geometry.PresheafedSpace.is_open_immersion.mono AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.mono

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment "/--" "The composition of two open immersions is an open immersion. -/")]
      []
      []
      []
      []
      [])
     (Command.instance
      (Term.attrKind [])
      "instance"
      []
      [(Command.declId `comp [])]
      (Command.declSig
       [(Term.implicitBinder "{" [`Z] [":" (Term.app `PresheafedSpaceCat [`C])] "}")
        (Term.explicitBinder
         "("
         [`f]
         [":" (Combinatorics.Quiver.Basic.«term_⟶_» `X " ⟶ " `Y)]
         []
         ")")
        (Term.instBinder
         "["
         [`hf ":"]
         (Term.app
          (AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termis_open_immersion
           "is_open_immersion")
          [`f])
         "]")
        (Term.explicitBinder
         "("
         [`g]
         [":" (Combinatorics.Quiver.Basic.«term_⟶_» `Y " ⟶ " `Z)]
         []
         ")")
        (Term.instBinder
         "["
         [`hg ":"]
         (Term.app
          (AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termis_open_immersion
           "is_open_immersion")
          [`g])
         "]")]
       (Term.typeSpec
        ":"
        (Term.app
         (AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termis_open_immersion
          "is_open_immersion")
         [(CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» `f " ≫ " `g)])))
      (Command.whereStructInst
       "where"
       [(Command.whereStructField
         (Term.letDecl
          (Term.letIdDecl
           `base_open
           []
           []
           ":="
           (Term.app
            (Term.proj (Term.proj `hg "." `base_open) "." `comp)
            [(Term.proj `hf "." `base_open)]))))
        []
        (Command.whereStructField
         (Term.letDecl
          (Term.letIdDecl
           `c_iso
           [`U]
           []
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Mathlib.Tactic.GeneralizeProofs.generalizeProofs
                "generalize_proofs"
                [(Lean.binderIdent `h)]
                [])
               []
               (Tactic.dsimp
                "dsimp"
                []
                []
                ["only"]
                ["["
                 [(Tactic.simpLemma [] [] `AlgebraicGeometry.PresheafedSpaceCat.comp_c_app)
                  ","
                  (Tactic.simpLemma [] [] `unop_op)
                  ","
                  (Tactic.simpLemma [] [] `functor.op)
                  ","
                  (Tactic.simpLemma [] [] `comp_base)
                  ","
                  (Tactic.simpLemma [] [] `TopCat.Presheaf.pushforward_obj_obj)
                  ","
                  (Tactic.simpLemma [] [] `opens.map_comp_obj)]
                 "]"]
                [])
               []
               (Mathlib.Tactic.applyWith
                "apply"
                "("
                "config"
                ":="
                (Term.structInst
                 "{"
                 []
                 [(Term.structInstField (Term.structInstLVal `instances []) ":=" `false)]
                 (Term.optEllipsis [])
                 []
                 "}")
                ")"
                `is_iso.comp_is_iso)
               []
               (Mathlib.Tactic.tacticSwap "swap")
               []
               (tactic__
                (cdotTk (patternIgnore (token.«· » "·")))
                [(Tactic.tacticHave_
                  "have"
                  (Term.haveDecl
                   (Term.haveIdDecl
                    []
                    [(Term.typeSpec
                      ":"
                      («term_=_»
                       (Term.app
                        (Term.proj (Term.app `opens.map [`g.base]) "." `obj)
                        [(Term.app `h.functor.obj [`U])])
                       "="
                       (Term.app `hf.open_functor.obj [`U])))]
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
                         ["["
                          [(Tactic.simpLemma [] [] `opens.map)
                           ","
                           (Tactic.simpLemma [] [] `IsOpenMap.functor)
                           ","
                           (Tactic.simpLemma [] [] `PresheafedSpace.comp_base)]
                          "]"]
                         [])
                        []
                        (Tactic.congr "congr" [(num "1")])
                        []
                        (Tactic.rwSeq
                         "rw"
                         []
                         (Tactic.rwRuleSeq
                          "["
                          [(Tactic.rwRule [] `coe_comp)
                           ","
                           (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Set.image_image)
                           ","
                           (Tactic.rwRule
                            []
                            (Term.app `Set.preimage_image_eq [(Term.hole "_") `hg.base_open.inj]))]
                          "]")
                         [])]))))))
                 []
                 (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `this)] "]") [])
                 []
                 (Tactic.tacticInfer_instance "infer_instance")])
               []
               (tactic__
                (cdotTk (patternIgnore (token.«· » "·")))
                [(Tactic.tacticHave_
                  "have"
                  (Term.haveDecl
                   (Term.haveIdDecl
                    []
                    [(Term.typeSpec
                      ":"
                      («term_=_»
                       (Term.app `h.functor.obj [`U])
                       "="
                       (Term.app `hg.open_functor.obj [(Term.app `hf.open_functor.obj [`U])])))]
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
                         ["[" [(Tactic.simpLemma [] [] `IsOpenMap.functor)] "]"]
                         [])
                        []
                        (Tactic.congr "congr" [(num "1")])
                        []
                        (Tactic.rwSeq
                         "rw"
                         []
                         (Tactic.rwRuleSeq
                          "["
                          [(Tactic.rwRule [] `comp_base)
                           ","
                           (Tactic.rwRule [] `coe_comp)
                           ","
                           (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Set.image_image)]
                          "]")
                         [])
                        []
                        (Tactic.congr "congr" [])]))))))
                 []
                 (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `this)] "]") [])
                 []
                 (Tactic.tacticInfer_instance "infer_instance")])]))))))]
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
         [(Mathlib.Tactic.GeneralizeProofs.generalizeProofs
           "generalize_proofs"
           [(Lean.binderIdent `h)]
           [])
          []
          (Tactic.dsimp
           "dsimp"
           []
           []
           ["only"]
           ["["
            [(Tactic.simpLemma [] [] `AlgebraicGeometry.PresheafedSpaceCat.comp_c_app)
             ","
             (Tactic.simpLemma [] [] `unop_op)
             ","
             (Tactic.simpLemma [] [] `functor.op)
             ","
             (Tactic.simpLemma [] [] `comp_base)
             ","
             (Tactic.simpLemma [] [] `TopCat.Presheaf.pushforward_obj_obj)
             ","
             (Tactic.simpLemma [] [] `opens.map_comp_obj)]
            "]"]
           [])
          []
          (Mathlib.Tactic.applyWith
           "apply"
           "("
           "config"
           ":="
           (Term.structInst
            "{"
            []
            [(Term.structInstField (Term.structInstLVal `instances []) ":=" `false)]
            (Term.optEllipsis [])
            []
            "}")
           ")"
           `is_iso.comp_is_iso)
          []
          (Mathlib.Tactic.tacticSwap "swap")
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               []
               [(Term.typeSpec
                 ":"
                 («term_=_»
                  (Term.app
                   (Term.proj (Term.app `opens.map [`g.base]) "." `obj)
                   [(Term.app `h.functor.obj [`U])])
                  "="
                  (Term.app `hf.open_functor.obj [`U])))]
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
                    ["["
                     [(Tactic.simpLemma [] [] `opens.map)
                      ","
                      (Tactic.simpLemma [] [] `IsOpenMap.functor)
                      ","
                      (Tactic.simpLemma [] [] `PresheafedSpace.comp_base)]
                     "]"]
                    [])
                   []
                   (Tactic.congr "congr" [(num "1")])
                   []
                   (Tactic.rwSeq
                    "rw"
                    []
                    (Tactic.rwRuleSeq
                     "["
                     [(Tactic.rwRule [] `coe_comp)
                      ","
                      (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Set.image_image)
                      ","
                      (Tactic.rwRule
                       []
                       (Term.app `Set.preimage_image_eq [(Term.hole "_") `hg.base_open.inj]))]
                     "]")
                    [])]))))))
            []
            (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `this)] "]") [])
            []
            (Tactic.tacticInfer_instance "infer_instance")])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               []
               [(Term.typeSpec
                 ":"
                 («term_=_»
                  (Term.app `h.functor.obj [`U])
                  "="
                  (Term.app `hg.open_functor.obj [(Term.app `hf.open_functor.obj [`U])])))]
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
                    ["[" [(Tactic.simpLemma [] [] `IsOpenMap.functor)] "]"]
                    [])
                   []
                   (Tactic.congr "congr" [(num "1")])
                   []
                   (Tactic.rwSeq
                    "rw"
                    []
                    (Tactic.rwRuleSeq
                     "["
                     [(Tactic.rwRule [] `comp_base)
                      ","
                      (Tactic.rwRule [] `coe_comp)
                      ","
                      (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Set.image_image)]
                     "]")
                    [])
                   []
                   (Tactic.congr "congr" [])]))))))
            []
            (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `this)] "]") [])
            []
            (Tactic.tacticInfer_instance "infer_instance")])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           []
           [(Term.typeSpec
             ":"
             («term_=_»
              (Term.app `h.functor.obj [`U])
              "="
              (Term.app `hg.open_functor.obj [(Term.app `hf.open_functor.obj [`U])])))]
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
                ["[" [(Tactic.simpLemma [] [] `IsOpenMap.functor)] "]"]
                [])
               []
               (Tactic.congr "congr" [(num "1")])
               []
               (Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule [] `comp_base)
                  ","
                  (Tactic.rwRule [] `coe_comp)
                  ","
                  (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Set.image_image)]
                 "]")
                [])
               []
               (Tactic.congr "congr" [])]))))))
        []
        (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `this)] "]") [])
        []
        (Tactic.tacticInfer_instance "infer_instance")])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticInfer_instance "infer_instance")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `this)] "]") [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `this
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         []
         [(Term.typeSpec
           ":"
           («term_=_»
            (Term.app `h.functor.obj [`U])
            "="
            (Term.app `hg.open_functor.obj [(Term.app `hf.open_functor.obj [`U])])))]
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
              ["[" [(Tactic.simpLemma [] [] `IsOpenMap.functor)] "]"]
              [])
             []
             (Tactic.congr "congr" [(num "1")])
             []
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [] `comp_base)
                ","
                (Tactic.rwRule [] `coe_comp)
                ","
                (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Set.image_image)]
               "]")
              [])
             []
             (Tactic.congr "congr" [])]))))))
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
           ["[" [(Tactic.simpLemma [] [] `IsOpenMap.functor)] "]"]
           [])
          []
          (Tactic.congr "congr" [(num "1")])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `comp_base)
             ","
             (Tactic.rwRule [] `coe_comp)
             ","
             (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Set.image_image)]
            "]")
           [])
          []
          (Tactic.congr "congr" [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.congr "congr" [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `comp_base)
         ","
         (Tactic.rwRule [] `coe_comp)
         ","
         (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Set.image_image)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Set.image_image
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `coe_comp
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `comp_base
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.congr "congr" [(num "1")])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.dsimp
       "dsimp"
       []
       []
       ["only"]
       ["[" [(Tactic.simpLemma [] [] `IsOpenMap.functor)] "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `IsOpenMap.functor
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Term.app `h.functor.obj [`U])
       "="
       (Term.app `hg.open_functor.obj [(Term.app `hf.open_functor.obj [`U])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `hg.open_functor.obj [(Term.app `hf.open_functor.obj [`U])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `hf.open_functor.obj [`U])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `U
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `hf.open_functor.obj
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `hf.open_functor.obj [`U])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `hg.open_functor.obj
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app `h.functor.obj [`U])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `U
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `h.functor.obj
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           []
           [(Term.typeSpec
             ":"
             («term_=_»
              (Term.app
               (Term.proj (Term.app `opens.map [`g.base]) "." `obj)
               [(Term.app `h.functor.obj [`U])])
              "="
              (Term.app `hf.open_functor.obj [`U])))]
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
                ["["
                 [(Tactic.simpLemma [] [] `opens.map)
                  ","
                  (Tactic.simpLemma [] [] `IsOpenMap.functor)
                  ","
                  (Tactic.simpLemma [] [] `PresheafedSpace.comp_base)]
                 "]"]
                [])
               []
               (Tactic.congr "congr" [(num "1")])
               []
               (Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule [] `coe_comp)
                  ","
                  (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Set.image_image)
                  ","
                  (Tactic.rwRule
                   []
                   (Term.app `Set.preimage_image_eq [(Term.hole "_") `hg.base_open.inj]))]
                 "]")
                [])]))))))
        []
        (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `this)] "]") [])
        []
        (Tactic.tacticInfer_instance "infer_instance")])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticInfer_instance "infer_instance")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `this)] "]") [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `this
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         []
         [(Term.typeSpec
           ":"
           («term_=_»
            (Term.app
             (Term.proj (Term.app `opens.map [`g.base]) "." `obj)
             [(Term.app `h.functor.obj [`U])])
            "="
            (Term.app `hf.open_functor.obj [`U])))]
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
              ["["
               [(Tactic.simpLemma [] [] `opens.map)
                ","
                (Tactic.simpLemma [] [] `IsOpenMap.functor)
                ","
                (Tactic.simpLemma [] [] `PresheafedSpace.comp_base)]
               "]"]
              [])
             []
             (Tactic.congr "congr" [(num "1")])
             []
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [] `coe_comp)
                ","
                (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Set.image_image)
                ","
                (Tactic.rwRule
                 []
                 (Term.app `Set.preimage_image_eq [(Term.hole "_") `hg.base_open.inj]))]
               "]")
              [])]))))))
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
           ["["
            [(Tactic.simpLemma [] [] `opens.map)
             ","
             (Tactic.simpLemma [] [] `IsOpenMap.functor)
             ","
             (Tactic.simpLemma [] [] `PresheafedSpace.comp_base)]
            "]"]
           [])
          []
          (Tactic.congr "congr" [(num "1")])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `coe_comp)
             ","
             (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Set.image_image)
             ","
             (Tactic.rwRule
              []
              (Term.app `Set.preimage_image_eq [(Term.hole "_") `hg.base_open.inj]))]
            "]")
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `coe_comp)
         ","
         (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Set.image_image)
         ","
         (Tactic.rwRule [] (Term.app `Set.preimage_image_eq [(Term.hole "_") `hg.base_open.inj]))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Set.preimage_image_eq [(Term.hole "_") `hg.base_open.inj])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hg.base_open.inj
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Set.preimage_image_eq
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Set.image_image
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `coe_comp
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.congr "congr" [(num "1")])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.dsimp
       "dsimp"
       []
       []
       ["only"]
       ["["
        [(Tactic.simpLemma [] [] `opens.map)
         ","
         (Tactic.simpLemma [] [] `IsOpenMap.functor)
         ","
         (Tactic.simpLemma [] [] `PresheafedSpace.comp_base)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `PresheafedSpace.comp_base
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `IsOpenMap.functor
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `opens.map
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Term.app
        (Term.proj (Term.app `opens.map [`g.base]) "." `obj)
        [(Term.app `h.functor.obj [`U])])
       "="
       (Term.app `hf.open_functor.obj [`U]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `hf.open_functor.obj [`U])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `U
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `hf.open_functor.obj
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app
       (Term.proj (Term.app `opens.map [`g.base]) "." `obj)
       [(Term.app `h.functor.obj [`U])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `h.functor.obj [`U])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `U
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `h.functor.obj
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `h.functor.obj [`U]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app `opens.map [`g.base]) "." `obj)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `opens.map [`g.base])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g.base
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `opens.map
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `opens.map [`g.base]) ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.tacticSwap "swap")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.applyWith
       "apply"
       "("
       "config"
       ":="
       (Term.structInst
        "{"
        []
        [(Term.structInstField (Term.structInstLVal `instances []) ":=" `false)]
        (Term.optEllipsis [])
        []
        "}")
       ")"
       `is_iso.comp_is_iso)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `is_iso.comp_is_iso
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.structInst
       "{"
       []
       [(Term.structInstField (Term.structInstLVal `instances []) ":=" `false)]
       (Term.optEllipsis [])
       []
       "}")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `false
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.dsimp
       "dsimp"
       []
       []
       ["only"]
       ["["
        [(Tactic.simpLemma [] [] `AlgebraicGeometry.PresheafedSpaceCat.comp_c_app)
         ","
         (Tactic.simpLemma [] [] `unop_op)
         ","
         (Tactic.simpLemma [] [] `functor.op)
         ","
         (Tactic.simpLemma [] [] `comp_base)
         ","
         (Tactic.simpLemma [] [] `TopCat.Presheaf.pushforward_obj_obj)
         ","
         (Tactic.simpLemma [] [] `opens.map_comp_obj)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `opens.map_comp_obj
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `TopCat.Presheaf.pushforward_obj_obj
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `comp_base
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `functor.op
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `unop_op
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `AlgebraicGeometry.PresheafedSpaceCat.comp_c_app
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.GeneralizeProofs.generalizeProofs
       "generalize_proofs"
       [(Lean.binderIdent `h)]
       [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj (Term.proj `hg "." `base_open) "." `comp)
       [(Term.proj `hf "." `base_open)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `hf "." `base_open)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hf
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.proj `hg "." `base_open) "." `comp)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj `hg "." `base_open)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hg
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app
       (AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termis_open_immersion
        "is_open_immersion")
       [(CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» `f " ≫ " `g)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» `f " ≫ " `g)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» `f " ≫ " `g)
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termis_open_immersion
       "is_open_immersion")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termis_open_immersion', expected 'AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termis_open_immersion._@.AlgebraicGeometry.OpenImmersion._hyg.21'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/-- The composition of two open immersions is an open immersion. -/
  instance
    comp
    { Z : PresheafedSpaceCat C }
        ( f : X ⟶ Y )
        [ hf : is_open_immersion f ]
        ( g : Y ⟶ Z )
        [ hg : is_open_immersion g ]
      : is_open_immersion f ≫ g
    where
      base_open := hg . base_open . comp hf . base_open
        c_iso
          U
          :=
          by
            generalize_proofs h
              dsimp
                only
                [
                  AlgebraicGeometry.PresheafedSpaceCat.comp_c_app
                    ,
                    unop_op
                    ,
                    functor.op
                    ,
                    comp_base
                    ,
                    TopCat.Presheaf.pushforward_obj_obj
                    ,
                    opens.map_comp_obj
                  ]
              apply ( config := { instances := false } ) is_iso.comp_is_iso
              swap
              ·
                have
                    : opens.map g.base . obj h.functor.obj U = hf.open_functor.obj U
                      :=
                      by
                        dsimp only [ opens.map , IsOpenMap.functor , PresheafedSpace.comp_base ]
                          congr 1
                          rw
                            [
                              coe_comp
                                ,
                                ← Set.image_image
                                ,
                                Set.preimage_image_eq _ hg.base_open.inj
                              ]
                  rw [ this ]
                  infer_instance
              ·
                have
                    : h.functor.obj U = hg.open_functor.obj hf.open_functor.obj U
                      :=
                      by
                        dsimp only [ IsOpenMap.functor ]
                          congr 1
                          rw [ comp_base , coe_comp , ← Set.image_image ]
                          congr
                  rw [ this ]
                  infer_instance
#align
  algebraic_geometry.PresheafedSpace.is_open_immersion.comp AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.comp

/-- For an open immersion `f : X ⟶ Y` and an open set `U ⊆ X`, we have the map `X(U) ⟶ Y(U)`. -/
noncomputable def invApp (U : Opens X) :
    X.Presheaf.obj (op U) ⟶ Y.Presheaf.obj (op (H.openFunctor.obj U)) :=
  X.Presheaf.map (eqToHom (by simp [opens.map, Set.preimage_image_eq _ H.base_open.inj])) ≫
    inv (f.c.app (op (H.openFunctor.obj U)))
#align
  algebraic_geometry.PresheafedSpace.is_open_immersion.inv_app AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.invApp

@[simp, reassoc.1]
theorem inv_naturality {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) :
    X.Presheaf.map i ≫ H.invApp (unop V) =
      H.invApp (unop U) ≫ Y.Presheaf.map (H.openFunctor.op.map i) :=
  by
  simp only [inv_app, ← category.assoc]
  rw [is_iso.comp_inv_eq]
  simp only [category.assoc, f.c.naturality, is_iso.inv_hom_id_assoc, ← X.presheaf.map_comp]
  erw [← X.presheaf.map_comp]
  congr
#align
  algebraic_geometry.PresheafedSpace.is_open_immersion.inv_naturality AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.inv_naturality

instance (U : Opens X) : IsIso (H.invApp U) :=
  by
  delta inv_app
  infer_instance

theorem inv_inv_app (U : Opens X) :
    inv (H.invApp U) =
      f.c.app (op (H.openFunctor.obj U)) ≫
        X.Presheaf.map (eqToHom (by simp [opens.map, Set.preimage_image_eq _ H.base_open.inj])) :=
  by
  rw [← cancel_epi (H.inv_app U)]
  rw [is_iso.hom_inv_id]
  delta inv_app
  simp [← functor.map_comp]
#align
  algebraic_geometry.PresheafedSpace.is_open_immersion.inv_inv_app AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.inv_inv_app

@[simp, reassoc.1, elementwise]
theorem inv_app_app (U : Opens X) :
    H.invApp U ≫ f.c.app (op (H.openFunctor.obj U)) =
      X.Presheaf.map (eqToHom (by simp [opens.map, Set.preimage_image_eq _ H.base_open.inj])) :=
  by rw [inv_app, category.assoc, is_iso.inv_hom_id, category.comp_id]
#align
  algebraic_geometry.PresheafedSpace.is_open_immersion.inv_app_app AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.inv_app_app

@[simp, reassoc.1]
theorem app_inv_app (U : Opens Y) :
    f.c.app (op U) ≫ H.invApp ((Opens.map f.base).obj U) =
      Y.Presheaf.map
        ((homOfLe (Set.image_preimage_subset f.base U)).op :
          op U ⟶ op (H.openFunctor.obj ((Opens.map f.base).obj U))) :=
  by
  erw [← category.assoc]
  rw [is_iso.comp_inv_eq, f.c.naturality]
  congr
#align
  algebraic_geometry.PresheafedSpace.is_open_immersion.app_inv_app AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.app_inv_app

/-- A variant of `app_inv_app` that gives an `eq_to_hom` instead of `hom_of_le`. -/
@[reassoc.1]
theorem app_inv_app' (U : Opens Y) (hU : (U : Set Y) ⊆ Set.range f.base) :
    f.c.app (op U) ≫ H.invApp ((Opens.map f.base).obj U) =
      Y.Presheaf.map
        (eqToHom
            (by
              apply LE.le.antisymm
              · exact Set.image_preimage_subset f.base U.1
              · change U ⊆ _
                refine' LE.le.trans_eq _ (@Set.image_preimage_eq_inter_range _ _ f.base U.1).symm
                exact set.subset_inter_iff.mpr ⟨fun _ h => h, hU⟩)).op :=
  by
  erw [← category.assoc]
  rw [is_iso.comp_inv_eq, f.c.naturality]
  congr
#align
  algebraic_geometry.PresheafedSpace.is_open_immersion.app_inv_app' AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.app_inv_app'

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment "/--" "An isomorphism is an open immersion. -/")]
      []
      []
      []
      []
      [])
     (Command.instance
      (Term.attrKind [])
      "instance"
      []
      [(Command.declId `ofIso [])]
      (Command.declSig
       [(Term.implicitBinder
         "{"
         [`X `Y]
         [":" (Term.app (Term.explicitUniv `PresheafedSpaceCat ".{" [`v] "}") [`C])]
         "}")
        (Term.explicitBinder
         "("
         [`H]
         [":" (CategoryTheory.CategoryTheory.Isomorphism.«term_≅_» `X " ≅ " `Y)]
         []
         ")")]
       (Term.typeSpec
        ":"
        (Term.app
         (AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termis_open_immersion
          "is_open_immersion")
         [(Term.proj `H "." `Hom)])))
      (Command.whereStructInst
       "where"
       [(Command.whereStructField
         (Term.letDecl
          (Term.letIdDecl
           `base_open
           []
           []
           ":="
           (Term.proj
            (Term.app
             `TopCat.homeoOfIso
             [(Term.app (Term.proj (Term.app `forget [`C]) "." `mapIso) [`H])])
            "."
            `OpenEmbedding))))
        []
        (Command.whereStructField
         (Term.letDecl (Term.letIdDecl `c_iso [(Term.hole "_")] [] ":=" `inferInstance)))]
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
      `inferInstance
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'ident'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj
       (Term.app
        `TopCat.homeoOfIso
        [(Term.app (Term.proj (Term.app `forget [`C]) "." `mapIso) [`H])])
       "."
       `OpenEmbedding)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       `TopCat.homeoOfIso
       [(Term.app (Term.proj (Term.app `forget [`C]) "." `mapIso) [`H])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj (Term.app `forget [`C]) "." `mapIso) [`H])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `H
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app `forget [`C]) "." `mapIso)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `forget [`C])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `C
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `forget
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `forget [`C]) ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.proj (Term.paren "(" (Term.app `forget [`C]) ")") "." `mapIso) [`H])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `TopCat.homeoOfIso
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `TopCat.homeoOfIso
      [(Term.paren
        "("
        (Term.app (Term.proj (Term.paren "(" (Term.app `forget [`C]) ")") "." `mapIso) [`H])
        ")")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app
       (AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termis_open_immersion
        "is_open_immersion")
       [(Term.proj `H "." `Hom)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `H "." `Hom)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `H
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termis_open_immersion
       "is_open_immersion")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termis_open_immersion', expected 'AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termis_open_immersion._@.AlgebraicGeometry.OpenImmersion._hyg.21'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/-- An isomorphism is an open immersion. -/
  instance
    ofIso
    { X Y : PresheafedSpaceCat .{ v } C } ( H : X ≅ Y ) : is_open_immersion H . Hom
    where
      base_open := TopCat.homeoOfIso forget C . mapIso H . OpenEmbedding c_iso _ := inferInstance
#align
  algebraic_geometry.PresheafedSpace.is_open_immersion.of_iso AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.ofIso

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.instance
      (Term.attrKind [])
      "instance"
      [(Command.namedPrio "(" "priority" ":=" (num "100") ")")]
      [(Command.declId `ofIsIso [])]
      (Command.declSig
       [(Term.implicitBinder
         "{"
         [`X `Y]
         [":" (Term.app (Term.explicitUniv `PresheafedSpaceCat ".{" [`v] "}") [`C])]
         "}")
        (Term.explicitBinder
         "("
         [`f]
         [":" (Combinatorics.Quiver.Basic.«term_⟶_» `X " ⟶ " `Y)]
         []
         ")")
        (Term.instBinder "[" [] (Term.app `IsIso [`f]) "]")]
       (Term.typeSpec
        ":"
        (Term.app
         (AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termis_open_immersion
          "is_open_immersion")
         [`f])))
      (Command.declValSimple
       ":="
       (Term.app
        `AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.ofIso
        [(Term.app `asIso [`f])])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.ofIso
       [(Term.app `asIso [`f])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `asIso [`f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `asIso
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `asIso [`f]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.ofIso
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app
       (AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termis_open_immersion
        "is_open_immersion")
       [`f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termis_open_immersion
       "is_open_immersion")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termis_open_immersion', expected 'AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termis_open_immersion._@.AlgebraicGeometry.OpenImmersion._hyg.21'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
instance
  ( priority := 100 )
  ofIsIso
  { X Y : PresheafedSpaceCat .{ v } C } ( f : X ⟶ Y ) [ IsIso f ] : is_open_immersion f
  := AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.ofIso asIso f
#align
  algebraic_geometry.PresheafedSpace.is_open_immersion.of_is_iso AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.ofIsIso

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.instance
      (Term.attrKind [])
      "instance"
      []
      [(Command.declId `ofRestrict [])]
      (Command.declSig
       [(Term.implicitBinder "{" [`X] [":" `TopCat] "}")
        (Term.explicitBinder "(" [`Y] [":" (Term.app `PresheafedSpaceCat [`C])] [] ")")
        (Term.implicitBinder
         "{"
         [`f]
         [":" (Combinatorics.Quiver.Basic.«term_⟶_» `X " ⟶ " (Term.proj `Y "." `carrier))]
         "}")
        (Term.explicitBinder "(" [`hf] [":" (Term.app `OpenEmbedding [`f])] [] ")")]
       (Term.typeSpec
        ":"
        (Term.app
         (AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termis_open_immersion
          "is_open_immersion")
         [(Term.app (Term.proj `Y "." `of_restrict) [`hf])])))
      (Command.whereStructInst
       "where"
       [(Command.whereStructField (Term.letDecl (Term.letIdDecl `base_open [] [] ":=" `hf)))
        []
        (Command.whereStructField
         (Term.letDecl
          (Term.letIdDecl
           `c_iso
           [`U]
           []
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.dsimp "dsimp" [] [] [] [] [])
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
                      (Term.proj (Term.app `opens.map [`f]) "." `obj)
                      [(Term.app `hf.is_open_map.functor.obj [`U])])
                     "="
                     `U))]
                  ":="
                  (Term.byTactic
                   "by"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented
                     [(Tactic.cases "cases" [(Tactic.casesTarget [] `U)] [] [])
                      []
                      (Tactic.dsimp
                       "dsimp"
                       []
                       []
                       ["only"]
                       ["["
                        [(Tactic.simpLemma [] [] `opens.map)
                         ","
                         (Tactic.simpLemma [] [] `IsOpenMap.functor)]
                        "]"]
                       [])
                      []
                      (Tactic.congr "congr" [(num "1")])
                      []
                      (Tactic.rwSeq
                       "rw"
                       []
                       (Tactic.rwRuleSeq
                        "["
                        [(Tactic.rwRule
                          []
                          (Term.app `Set.preimage_image_eq [(Term.hole "_") `hf.inj]))]
                        "]")
                       [])
                      []
                      (Tactic.tacticRfl "rfl")]))))))
               []
               (convert
                "convert"
                []
                (Term.show
                 "show"
                 (Term.app
                  `is_iso
                  [(Term.app
                    `Y.presheaf.map
                    [(Term.app
                      (CategoryTheory.CategoryTheory.Category.Basic.«term𝟙» "𝟙")
                      [(Term.hole "_")])])])
                 (Term.fromTerm "from" `inferInstance))
                [])
               []
               (tactic__
                (cdotTk (patternIgnore (token.«· » "·")))
                [(Tactic.apply "apply" `Subsingleton.helim)
                 []
                 (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `this)] "]") [])])
               []
               (tactic__
                (cdotTk (patternIgnore (token.«· » "·")))
                [(Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Y.presheaf.map_id)] "]")
                  [])
                 []
                 (Tactic.tacticInfer_instance "infer_instance")])]))))))]
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
         [(Tactic.dsimp "dsimp" [] [] [] [] [])
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
                 (Term.proj (Term.app `opens.map [`f]) "." `obj)
                 [(Term.app `hf.is_open_map.functor.obj [`U])])
                "="
                `U))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.cases "cases" [(Tactic.casesTarget [] `U)] [] [])
                 []
                 (Tactic.dsimp
                  "dsimp"
                  []
                  []
                  ["only"]
                  ["["
                   [(Tactic.simpLemma [] [] `opens.map)
                    ","
                    (Tactic.simpLemma [] [] `IsOpenMap.functor)]
                   "]"]
                  [])
                 []
                 (Tactic.congr "congr" [(num "1")])
                 []
                 (Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule [] (Term.app `Set.preimage_image_eq [(Term.hole "_") `hf.inj]))]
                   "]")
                  [])
                 []
                 (Tactic.tacticRfl "rfl")]))))))
          []
          (convert
           "convert"
           []
           (Term.show
            "show"
            (Term.app
             `is_iso
             [(Term.app
               `Y.presheaf.map
               [(Term.app
                 (CategoryTheory.CategoryTheory.Category.Basic.«term𝟙» "𝟙")
                 [(Term.hole "_")])])])
            (Term.fromTerm "from" `inferInstance))
           [])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.apply "apply" `Subsingleton.helim)
            []
            (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `this)] "]") [])])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Y.presheaf.map_id)] "]")
             [])
            []
            (Tactic.tacticInfer_instance "infer_instance")])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Y.presheaf.map_id)] "]") [])
        []
        (Tactic.tacticInfer_instance "infer_instance")])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticInfer_instance "infer_instance")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Y.presheaf.map_id)] "]") [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Y.presheaf.map_id
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.apply "apply" `Subsingleton.helim)
        []
        (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `this)] "]") [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `this)] "]") [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `this
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.apply "apply" `Subsingleton.helim)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Subsingleton.helim
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (convert
       "convert"
       []
       (Term.show
        "show"
        (Term.app
         `is_iso
         [(Term.app
           `Y.presheaf.map
           [(Term.app
             (CategoryTheory.CategoryTheory.Category.Basic.«term𝟙» "𝟙")
             [(Term.hole "_")])])])
        (Term.fromTerm "from" `inferInstance))
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.show
       "show"
       (Term.app
        `is_iso
        [(Term.app
          `Y.presheaf.map
          [(Term.app
            (CategoryTheory.CategoryTheory.Category.Basic.«term𝟙» "𝟙")
            [(Term.hole "_")])])])
       (Term.fromTerm "from" `inferInstance))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `inferInstance
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app
       `is_iso
       [(Term.app
         `Y.presheaf.map
         [(Term.app
           (CategoryTheory.CategoryTheory.Category.Basic.«term𝟙» "𝟙")
           [(Term.hole "_")])])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Y.presheaf.map
       [(Term.app (CategoryTheory.CategoryTheory.Category.Basic.«term𝟙» "𝟙") [(Term.hole "_")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (CategoryTheory.CategoryTheory.Category.Basic.«term𝟙» "𝟙") [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (CategoryTheory.CategoryTheory.Category.Basic.«term𝟙» "𝟙")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (CategoryTheory.CategoryTheory.Category.Basic.«term𝟙» "𝟙") [(Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Y.presheaf.map
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `Y.presheaf.map
      [(Term.paren
        "("
        (Term.app (CategoryTheory.CategoryTheory.Category.Basic.«term𝟙» "𝟙") [(Term.hole "_")])
        ")")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `is_iso
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         []
         [(Term.typeSpec
           ":"
           («term_=_»
            (Term.app
             (Term.proj (Term.app `opens.map [`f]) "." `obj)
             [(Term.app `hf.is_open_map.functor.obj [`U])])
            "="
            `U))]
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.cases "cases" [(Tactic.casesTarget [] `U)] [] [])
             []
             (Tactic.dsimp
              "dsimp"
              []
              []
              ["only"]
              ["["
               [(Tactic.simpLemma [] [] `opens.map) "," (Tactic.simpLemma [] [] `IsOpenMap.functor)]
               "]"]
              [])
             []
             (Tactic.congr "congr" [(num "1")])
             []
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [] (Term.app `Set.preimage_image_eq [(Term.hole "_") `hf.inj]))]
               "]")
              [])
             []
             (Tactic.tacticRfl "rfl")]))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.cases "cases" [(Tactic.casesTarget [] `U)] [] [])
          []
          (Tactic.dsimp
           "dsimp"
           []
           []
           ["only"]
           ["["
            [(Tactic.simpLemma [] [] `opens.map) "," (Tactic.simpLemma [] [] `IsOpenMap.functor)]
            "]"]
           [])
          []
          (Tactic.congr "congr" [(num "1")])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] (Term.app `Set.preimage_image_eq [(Term.hole "_") `hf.inj]))]
            "]")
           [])
          []
          (Tactic.tacticRfl "rfl")])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticRfl "rfl")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] (Term.app `Set.preimage_image_eq [(Term.hole "_") `hf.inj]))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Set.preimage_image_eq [(Term.hole "_") `hf.inj])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hf.inj
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Set.preimage_image_eq
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.congr "congr" [(num "1")])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.dsimp
       "dsimp"
       []
       []
       ["only"]
       ["["
        [(Tactic.simpLemma [] [] `opens.map) "," (Tactic.simpLemma [] [] `IsOpenMap.functor)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `IsOpenMap.functor
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `opens.map
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.cases "cases" [(Tactic.casesTarget [] `U)] [] [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `U
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Term.app
        (Term.proj (Term.app `opens.map [`f]) "." `obj)
        [(Term.app `hf.is_open_map.functor.obj [`U])])
       "="
       `U)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `U
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app
       (Term.proj (Term.app `opens.map [`f]) "." `obj)
       [(Term.app `hf.is_open_map.functor.obj [`U])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `hf.is_open_map.functor.obj [`U])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `U
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `hf.is_open_map.functor.obj
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `hf.is_open_map.functor.obj [`U])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app `opens.map [`f]) "." `obj)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `opens.map [`f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `opens.map
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `opens.map [`f]) ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.dsimp "dsimp" [] [] [] [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hf
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app
       (AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termis_open_immersion
        "is_open_immersion")
       [(Term.app (Term.proj `Y "." `of_restrict) [`hf])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj `Y "." `of_restrict) [`hf])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hf
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `Y "." `of_restrict)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `Y
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.proj `Y "." `of_restrict) [`hf])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termis_open_immersion
       "is_open_immersion")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termis_open_immersion', expected 'AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termis_open_immersion._@.AlgebraicGeometry.OpenImmersion._hyg.21'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
instance
  ofRestrict
  { X : TopCat } ( Y : PresheafedSpaceCat C ) { f : X ⟶ Y . carrier } ( hf : OpenEmbedding f )
    : is_open_immersion Y . of_restrict hf
  where
    base_open := hf
      c_iso
        U
        :=
        by
          dsimp
            have
              : opens.map f . obj hf.is_open_map.functor.obj U = U
                :=
                by
                  cases U
                    dsimp only [ opens.map , IsOpenMap.functor ]
                    congr 1
                    rw [ Set.preimage_image_eq _ hf.inj ]
                    rfl
            convert show is_iso Y.presheaf.map 𝟙 _ from inferInstance
            · apply Subsingleton.helim rw [ this ]
            · rw [ Y.presheaf.map_id ] infer_instance
#align
  algebraic_geometry.PresheafedSpace.is_open_immersion.of_restrict AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.ofRestrict

@[elementwise, simp]
theorem of_restrict_inv_app {C : Type _} [Category C] (X : PresheafedSpaceCat C) {Y : TopCat}
    {f : Y ⟶ TopCat.of X.carrier} (h : OpenEmbedding f) (U : Opens (X.restrict h).carrier) :
    (PresheafedSpaceCat.IsOpenImmersion.ofRestrict X h).invApp U = 𝟙 _ :=
  by
  delta PresheafedSpace.is_open_immersion.inv_app
  rw [is_iso.comp_inv_eq, category.id_comp]
  change X.presheaf.map _ = X.presheaf.map _
  congr
#align
  algebraic_geometry.PresheafedSpace.is_open_immersion.of_restrict_inv_app AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.of_restrict_inv_app

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "An open immersion is an iso if the underlying continuous map is epi. -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `to_iso [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`f]
         [":" (Combinatorics.Quiver.Basic.«term_⟶_» `X " ⟶ " `Y)]
         []
         ")")
        (Term.instBinder
         "["
         [`h ":"]
         (Term.app
          (AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termis_open_immersion
           "is_open_immersion")
          [`f])
         "]")
        (Term.instBinder "[" [`h' ":"] (Term.app `Epi [(Term.proj `f "." `base)]) "]")]
       (Term.typeSpec ":" (Term.app `IsIso [`f])))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Mathlib.Tactic.applyWith
            "apply"
            "("
            "config"
            ":="
            (Term.structInst
             "{"
             []
             [(Term.structInstField (Term.structInstLVal `instances []) ":=" `false)]
             (Term.optEllipsis [])
             []
             "}")
            ")"
            `is_iso_of_components)
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.tacticLet_
              "let"
              (Term.letDecl
               (Term.letPatDecl
                (Lean.termThis "this")
                []
                [(Term.typeSpec ":" (Topology.Homeomorph.«term_≃ₜ_» `X " ≃ₜ " `Y))]
                ":="
                (Term.app
                 (Term.proj
                  (Term.app `Homeomorph.ofEmbedding [(Term.hole "_") `h.base_open.to_embedding])
                  "."
                  `trans)
                 [(Term.structInst
                   "{"
                   []
                   [(Term.structInstField (Term.structInstLVal `toFun []) ":=" `Subtype.val)
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
                       (Term.anonymousCtor
                        "⟨"
                        [`x
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
                               [(Tactic.rwRule
                                 []
                                 (Term.app
                                  `set.range_iff_surjective.mpr
                                  [(Term.app
                                    (Term.proj
                                     (Term.app `TopCat.epi_iff_surjective [(Term.hole "_")])
                                     "."
                                     `mp)
                                    [`h'])]))]
                               "]")
                              [])
                             []
                             (Tactic.tacticTrivial "trivial")])))]
                        "⟩"))))
                    []
                    (Term.structInstField
                     (Term.structInstLVal `left_inv [])
                     ":="
                     (Term.fun
                      "fun"
                      (Term.basicFun
                       [(Term.anonymousCtor "⟨" [(Term.hole "_") "," (Term.hole "_")] "⟩")]
                       []
                       "=>"
                       `rfl)))
                    []
                    (Term.structInstField
                     (Term.structInstLVal `right_inv [])
                     ":="
                     (Term.fun "fun" (Term.basicFun [(Term.hole "_")] [] "=>" `rfl)))]
                   (Term.optEllipsis [])
                   []
                   "}")]))))
             []
             (convert
              "convert"
              []
              (Term.app `is_iso.of_iso [(Term.app `TopCat.isoOfHomeo [`this])])
              [])
             []
             (tactic__
              (cdotTk (patternIgnore (token.«· » "·")))
              [(Std.Tactic.Ext.«tacticExt___:_» "ext" [] []) [] (Tactic.tacticRfl "rfl")])])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Mathlib.Tactic.applyWith
              "apply"
              "("
              "config"
              ":="
              (Term.structInst
               "{"
               []
               [(Term.structInstField (Term.structInstLVal `instances []) ":=" `false)]
               (Term.optEllipsis [])
               []
               "}")
              ")"
              `nat_iso.is_iso_of_is_iso_app)
             []
             (Tactic.intro "intro" [`U])
             []
             (Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                []
                [(Term.typeSpec
                  ":"
                  («term_=_»
                   `U
                   "="
                   (Term.app
                    `op
                    [(Term.app
                      `h.open_functor.obj
                      [(Term.app
                        (Term.proj (Term.app `opens.map [`f.base]) "." `obj)
                        [(Term.app `unop [`U])])])])))]
                ":="
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(Tactic.induction "induction" [`U] ["using" `Opposite.rec] [] [])
                    []
                    (Tactic.cases "cases" [(Tactic.casesTarget [] `U)] [] [])
                    []
                    (Tactic.dsimp
                     "dsimp"
                     []
                     []
                     ["only"]
                     ["["
                      [(Tactic.simpLemma [] [] `functor.op) "," (Tactic.simpLemma [] [] `opens.map)]
                      "]"]
                     [])
                    []
                    (Tactic.congr "congr" [])
                    []
                    (Tactic.exact
                     "exact"
                     (Term.proj
                      (Term.app
                       `Set.image_preimage_eq
                       [(Term.hole "_")
                        (Term.app
                         (Term.proj (Term.app `TopCat.epi_iff_surjective [(Term.hole "_")]) "." `mp)
                         [`h'])])
                      "."
                      `symm))]))))))
             []
             (convert
              "convert"
              []
              (Term.app
               (Term.explicit "@" `is_open_immersion.c_iso)
               [(Term.hole "_")
                `h
                (Term.app
                 (Term.proj (Term.app `opens.map [`f.base]) "." `obj)
                 [(Term.app `unop [`U])])])
              [])])])))
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
         [(Mathlib.Tactic.applyWith
           "apply"
           "("
           "config"
           ":="
           (Term.structInst
            "{"
            []
            [(Term.structInstField (Term.structInstLVal `instances []) ":=" `false)]
            (Term.optEllipsis [])
            []
            "}")
           ")"
           `is_iso_of_components)
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.tacticLet_
             "let"
             (Term.letDecl
              (Term.letPatDecl
               (Lean.termThis "this")
               []
               [(Term.typeSpec ":" (Topology.Homeomorph.«term_≃ₜ_» `X " ≃ₜ " `Y))]
               ":="
               (Term.app
                (Term.proj
                 (Term.app `Homeomorph.ofEmbedding [(Term.hole "_") `h.base_open.to_embedding])
                 "."
                 `trans)
                [(Term.structInst
                  "{"
                  []
                  [(Term.structInstField (Term.structInstLVal `toFun []) ":=" `Subtype.val)
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
                      (Term.anonymousCtor
                       "⟨"
                       [`x
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
                              [(Tactic.rwRule
                                []
                                (Term.app
                                 `set.range_iff_surjective.mpr
                                 [(Term.app
                                   (Term.proj
                                    (Term.app `TopCat.epi_iff_surjective [(Term.hole "_")])
                                    "."
                                    `mp)
                                   [`h'])]))]
                              "]")
                             [])
                            []
                            (Tactic.tacticTrivial "trivial")])))]
                       "⟩"))))
                   []
                   (Term.structInstField
                    (Term.structInstLVal `left_inv [])
                    ":="
                    (Term.fun
                     "fun"
                     (Term.basicFun
                      [(Term.anonymousCtor "⟨" [(Term.hole "_") "," (Term.hole "_")] "⟩")]
                      []
                      "=>"
                      `rfl)))
                   []
                   (Term.structInstField
                    (Term.structInstLVal `right_inv [])
                    ":="
                    (Term.fun "fun" (Term.basicFun [(Term.hole "_")] [] "=>" `rfl)))]
                  (Term.optEllipsis [])
                  []
                  "}")]))))
            []
            (convert
             "convert"
             []
             (Term.app `is_iso.of_iso [(Term.app `TopCat.isoOfHomeo [`this])])
             [])
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(Std.Tactic.Ext.«tacticExt___:_» "ext" [] []) [] (Tactic.tacticRfl "rfl")])])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Mathlib.Tactic.applyWith
             "apply"
             "("
             "config"
             ":="
             (Term.structInst
              "{"
              []
              [(Term.structInstField (Term.structInstLVal `instances []) ":=" `false)]
              (Term.optEllipsis [])
              []
              "}")
             ")"
             `nat_iso.is_iso_of_is_iso_app)
            []
            (Tactic.intro "intro" [`U])
            []
            (Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               []
               [(Term.typeSpec
                 ":"
                 («term_=_»
                  `U
                  "="
                  (Term.app
                   `op
                   [(Term.app
                     `h.open_functor.obj
                     [(Term.app
                       (Term.proj (Term.app `opens.map [`f.base]) "." `obj)
                       [(Term.app `unop [`U])])])])))]
               ":="
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(Tactic.induction "induction" [`U] ["using" `Opposite.rec] [] [])
                   []
                   (Tactic.cases "cases" [(Tactic.casesTarget [] `U)] [] [])
                   []
                   (Tactic.dsimp
                    "dsimp"
                    []
                    []
                    ["only"]
                    ["["
                     [(Tactic.simpLemma [] [] `functor.op) "," (Tactic.simpLemma [] [] `opens.map)]
                     "]"]
                    [])
                   []
                   (Tactic.congr "congr" [])
                   []
                   (Tactic.exact
                    "exact"
                    (Term.proj
                     (Term.app
                      `Set.image_preimage_eq
                      [(Term.hole "_")
                       (Term.app
                        (Term.proj (Term.app `TopCat.epi_iff_surjective [(Term.hole "_")]) "." `mp)
                        [`h'])])
                     "."
                     `symm))]))))))
            []
            (convert
             "convert"
             []
             (Term.app
              (Term.explicit "@" `is_open_immersion.c_iso)
              [(Term.hole "_")
               `h
               (Term.app
                (Term.proj (Term.app `opens.map [`f.base]) "." `obj)
                [(Term.app `unop [`U])])])
             [])])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Mathlib.Tactic.applyWith
         "apply"
         "("
         "config"
         ":="
         (Term.structInst
          "{"
          []
          [(Term.structInstField (Term.structInstLVal `instances []) ":=" `false)]
          (Term.optEllipsis [])
          []
          "}")
         ")"
         `nat_iso.is_iso_of_is_iso_app)
        []
        (Tactic.intro "intro" [`U])
        []
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           []
           [(Term.typeSpec
             ":"
             («term_=_»
              `U
              "="
              (Term.app
               `op
               [(Term.app
                 `h.open_functor.obj
                 [(Term.app
                   (Term.proj (Term.app `opens.map [`f.base]) "." `obj)
                   [(Term.app `unop [`U])])])])))]
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.induction "induction" [`U] ["using" `Opposite.rec] [] [])
               []
               (Tactic.cases "cases" [(Tactic.casesTarget [] `U)] [] [])
               []
               (Tactic.dsimp
                "dsimp"
                []
                []
                ["only"]
                ["["
                 [(Tactic.simpLemma [] [] `functor.op) "," (Tactic.simpLemma [] [] `opens.map)]
                 "]"]
                [])
               []
               (Tactic.congr "congr" [])
               []
               (Tactic.exact
                "exact"
                (Term.proj
                 (Term.app
                  `Set.image_preimage_eq
                  [(Term.hole "_")
                   (Term.app
                    (Term.proj (Term.app `TopCat.epi_iff_surjective [(Term.hole "_")]) "." `mp)
                    [`h'])])
                 "."
                 `symm))]))))))
        []
        (convert
         "convert"
         []
         (Term.app
          (Term.explicit "@" `is_open_immersion.c_iso)
          [(Term.hole "_")
           `h
           (Term.app (Term.proj (Term.app `opens.map [`f.base]) "." `obj) [(Term.app `unop [`U])])])
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (convert
       "convert"
       []
       (Term.app
        (Term.explicit "@" `is_open_immersion.c_iso)
        [(Term.hole "_")
         `h
         (Term.app (Term.proj (Term.app `opens.map [`f.base]) "." `obj) [(Term.app `unop [`U])])])
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.explicit "@" `is_open_immersion.c_iso)
       [(Term.hole "_")
        `h
        (Term.app (Term.proj (Term.app `opens.map [`f.base]) "." `obj) [(Term.app `unop [`U])])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj (Term.app `opens.map [`f.base]) "." `obj) [(Term.app `unop [`U])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `unop [`U])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `U
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `unop
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `unop [`U]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app `opens.map [`f.base]) "." `obj)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `opens.map [`f.base])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f.base
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `opens.map
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `opens.map [`f.base]) ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      (Term.proj (Term.paren "(" (Term.app `opens.map [`f.base]) ")") "." `obj)
      [(Term.paren "(" (Term.app `unop [`U]) ")")])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.explicit "@" `is_open_immersion.c_iso)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `is_open_immersion.c_iso
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (some 1024,
     term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         []
         [(Term.typeSpec
           ":"
           («term_=_»
            `U
            "="
            (Term.app
             `op
             [(Term.app
               `h.open_functor.obj
               [(Term.app
                 (Term.proj (Term.app `opens.map [`f.base]) "." `obj)
                 [(Term.app `unop [`U])])])])))]
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.induction "induction" [`U] ["using" `Opposite.rec] [] [])
             []
             (Tactic.cases "cases" [(Tactic.casesTarget [] `U)] [] [])
             []
             (Tactic.dsimp
              "dsimp"
              []
              []
              ["only"]
              ["["
               [(Tactic.simpLemma [] [] `functor.op) "," (Tactic.simpLemma [] [] `opens.map)]
               "]"]
              [])
             []
             (Tactic.congr "congr" [])
             []
             (Tactic.exact
              "exact"
              (Term.proj
               (Term.app
                `Set.image_preimage_eq
                [(Term.hole "_")
                 (Term.app
                  (Term.proj (Term.app `TopCat.epi_iff_surjective [(Term.hole "_")]) "." `mp)
                  [`h'])])
               "."
               `symm))]))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.induction "induction" [`U] ["using" `Opposite.rec] [] [])
          []
          (Tactic.cases "cases" [(Tactic.casesTarget [] `U)] [] [])
          []
          (Tactic.dsimp
           "dsimp"
           []
           []
           ["only"]
           ["[" [(Tactic.simpLemma [] [] `functor.op) "," (Tactic.simpLemma [] [] `opens.map)] "]"]
           [])
          []
          (Tactic.congr "congr" [])
          []
          (Tactic.exact
           "exact"
           (Term.proj
            (Term.app
             `Set.image_preimage_eq
             [(Term.hole "_")
              (Term.app
               (Term.proj (Term.app `TopCat.epi_iff_surjective [(Term.hole "_")]) "." `mp)
               [`h'])])
            "."
            `symm))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.proj
        (Term.app
         `Set.image_preimage_eq
         [(Term.hole "_")
          (Term.app
           (Term.proj (Term.app `TopCat.epi_iff_surjective [(Term.hole "_")]) "." `mp)
           [`h'])])
        "."
        `symm))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj
       (Term.app
        `Set.image_preimage_eq
        [(Term.hole "_")
         (Term.app
          (Term.proj (Term.app `TopCat.epi_iff_surjective [(Term.hole "_")]) "." `mp)
          [`h'])])
       "."
       `symm)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       `Set.image_preimage_eq
       [(Term.hole "_")
        (Term.app
         (Term.proj (Term.app `TopCat.epi_iff_surjective [(Term.hole "_")]) "." `mp)
         [`h'])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj (Term.app `TopCat.epi_iff_surjective [(Term.hole "_")]) "." `mp) [`h'])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app `TopCat.epi_iff_surjective [(Term.hole "_")]) "." `mp)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `TopCat.epi_iff_surjective [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `TopCat.epi_iff_surjective
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `TopCat.epi_iff_surjective [(Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      (Term.proj
       (Term.paren "(" (Term.app `TopCat.epi_iff_surjective [(Term.hole "_")]) ")")
       "."
       `mp)
      [`h'])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Set.image_preimage_eq
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `Set.image_preimage_eq
      [(Term.hole "_")
       (Term.paren
        "("
        (Term.app
         (Term.proj
          (Term.paren "(" (Term.app `TopCat.epi_iff_surjective [(Term.hole "_")]) ")")
          "."
          `mp)
         [`h'])
        ")")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.congr "congr" [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.dsimp
       "dsimp"
       []
       []
       ["only"]
       ["[" [(Tactic.simpLemma [] [] `functor.op) "," (Tactic.simpLemma [] [] `opens.map)] "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `opens.map
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `functor.op
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.cases "cases" [(Tactic.casesTarget [] `U)] [] [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `U
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.induction "induction" [`U] ["using" `Opposite.rec] [] [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `U
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       `U
       "="
       (Term.app
        `op
        [(Term.app
          `h.open_functor.obj
          [(Term.app
            (Term.proj (Term.app `opens.map [`f.base]) "." `obj)
            [(Term.app `unop [`U])])])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `op
       [(Term.app
         `h.open_functor.obj
         [(Term.app
           (Term.proj (Term.app `opens.map [`f.base]) "." `obj)
           [(Term.app `unop [`U])])])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `h.open_functor.obj
       [(Term.app (Term.proj (Term.app `opens.map [`f.base]) "." `obj) [(Term.app `unop [`U])])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj (Term.app `opens.map [`f.base]) "." `obj) [(Term.app `unop [`U])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `unop [`U])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `U
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `unop
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `unop [`U]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app `opens.map [`f.base]) "." `obj)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `opens.map [`f.base])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f.base
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `opens.map
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `opens.map [`f.base]) ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      (Term.proj (Term.paren "(" (Term.app `opens.map [`f.base]) ")") "." `obj)
      [(Term.paren "(" (Term.app `unop [`U]) ")")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `h.open_functor.obj
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `h.open_functor.obj
      [(Term.paren
        "("
        (Term.app
         (Term.proj (Term.paren "(" (Term.app `opens.map [`f.base]) ")") "." `obj)
         [(Term.paren "(" (Term.app `unop [`U]) ")")])
        ")")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `op
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `U
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.intro "intro" [`U])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `U
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.applyWith
       "apply"
       "("
       "config"
       ":="
       (Term.structInst
        "{"
        []
        [(Term.structInstField (Term.structInstLVal `instances []) ":=" `false)]
        (Term.optEllipsis [])
        []
        "}")
       ")"
       `nat_iso.is_iso_of_is_iso_app)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `nat_iso.is_iso_of_is_iso_app
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.structInst
       "{"
       []
       [(Term.structInstField (Term.structInstLVal `instances []) ":=" `false)]
       (Term.optEllipsis [])
       []
       "}")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `false
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.tacticLet_
         "let"
         (Term.letDecl
          (Term.letPatDecl
           (Lean.termThis "this")
           []
           [(Term.typeSpec ":" (Topology.Homeomorph.«term_≃ₜ_» `X " ≃ₜ " `Y))]
           ":="
           (Term.app
            (Term.proj
             (Term.app `Homeomorph.ofEmbedding [(Term.hole "_") `h.base_open.to_embedding])
             "."
             `trans)
            [(Term.structInst
              "{"
              []
              [(Term.structInstField (Term.structInstLVal `toFun []) ":=" `Subtype.val)
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
                  (Term.anonymousCtor
                   "⟨"
                   [`x
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
                          [(Tactic.rwRule
                            []
                            (Term.app
                             `set.range_iff_surjective.mpr
                             [(Term.app
                               (Term.proj
                                (Term.app `TopCat.epi_iff_surjective [(Term.hole "_")])
                                "."
                                `mp)
                               [`h'])]))]
                          "]")
                         [])
                        []
                        (Tactic.tacticTrivial "trivial")])))]
                   "⟩"))))
               []
               (Term.structInstField
                (Term.structInstLVal `left_inv [])
                ":="
                (Term.fun
                 "fun"
                 (Term.basicFun
                  [(Term.anonymousCtor "⟨" [(Term.hole "_") "," (Term.hole "_")] "⟩")]
                  []
                  "=>"
                  `rfl)))
               []
               (Term.structInstField
                (Term.structInstLVal `right_inv [])
                ":="
                (Term.fun "fun" (Term.basicFun [(Term.hole "_")] [] "=>" `rfl)))]
              (Term.optEllipsis [])
              []
              "}")]))))
        []
        (convert "convert" [] (Term.app `is_iso.of_iso [(Term.app `TopCat.isoOfHomeo [`this])]) [])
        []
        (tactic__
         (cdotTk (patternIgnore (token.«· » "·")))
         [(Std.Tactic.Ext.«tacticExt___:_» "ext" [] []) [] (Tactic.tacticRfl "rfl")])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Std.Tactic.Ext.«tacticExt___:_» "ext" [] []) [] (Tactic.tacticRfl "rfl")])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticRfl "rfl")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Ext.«tacticExt___:_» "ext" [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (convert "convert" [] (Term.app `is_iso.of_iso [(Term.app `TopCat.isoOfHomeo [`this])]) [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `is_iso.of_iso [(Term.app `TopCat.isoOfHomeo [`this])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `TopCat.isoOfHomeo [`this])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `this
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `TopCat.isoOfHomeo
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `TopCat.isoOfHomeo [`this])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `is_iso.of_iso
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticLet_
       "let"
       (Term.letDecl
        (Term.letPatDecl
         (Lean.termThis "this")
         []
         [(Term.typeSpec ":" (Topology.Homeomorph.«term_≃ₜ_» `X " ≃ₜ " `Y))]
         ":="
         (Term.app
          (Term.proj
           (Term.app `Homeomorph.ofEmbedding [(Term.hole "_") `h.base_open.to_embedding])
           "."
           `trans)
          [(Term.structInst
            "{"
            []
            [(Term.structInstField (Term.structInstLVal `toFun []) ":=" `Subtype.val)
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
                (Term.anonymousCtor
                 "⟨"
                 [`x
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
                        [(Tactic.rwRule
                          []
                          (Term.app
                           `set.range_iff_surjective.mpr
                           [(Term.app
                             (Term.proj
                              (Term.app `TopCat.epi_iff_surjective [(Term.hole "_")])
                              "."
                              `mp)
                             [`h'])]))]
                        "]")
                       [])
                      []
                      (Tactic.tacticTrivial "trivial")])))]
                 "⟩"))))
             []
             (Term.structInstField
              (Term.structInstLVal `left_inv [])
              ":="
              (Term.fun
               "fun"
               (Term.basicFun
                [(Term.anonymousCtor "⟨" [(Term.hole "_") "," (Term.hole "_")] "⟩")]
                []
                "=>"
                `rfl)))
             []
             (Term.structInstField
              (Term.structInstLVal `right_inv [])
              ":="
              (Term.fun "fun" (Term.basicFun [(Term.hole "_")] [] "=>" `rfl)))]
            (Term.optEllipsis [])
            []
            "}")]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letPatDecl', expected 'Lean.Parser.Term.letIdDecl'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (Term.app `Homeomorph.ofEmbedding [(Term.hole "_") `h.base_open.to_embedding])
        "."
        `trans)
       [(Term.structInst
         "{"
         []
         [(Term.structInstField (Term.structInstLVal `toFun []) ":=" `Subtype.val)
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
             (Term.anonymousCtor
              "⟨"
              [`x
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
                     [(Tactic.rwRule
                       []
                       (Term.app
                        `set.range_iff_surjective.mpr
                        [(Term.app
                          (Term.proj
                           (Term.app `TopCat.epi_iff_surjective [(Term.hole "_")])
                           "."
                           `mp)
                          [`h'])]))]
                     "]")
                    [])
                   []
                   (Tactic.tacticTrivial "trivial")])))]
              "⟩"))))
          []
          (Term.structInstField
           (Term.structInstLVal `left_inv [])
           ":="
           (Term.fun
            "fun"
            (Term.basicFun
             [(Term.anonymousCtor "⟨" [(Term.hole "_") "," (Term.hole "_")] "⟩")]
             []
             "=>"
             `rfl)))
          []
          (Term.structInstField
           (Term.structInstLVal `right_inv [])
           ":="
           (Term.fun "fun" (Term.basicFun [(Term.hole "_")] [] "=>" `rfl)))]
         (Term.optEllipsis [])
         []
         "}")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInst', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInst', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.structInst
       "{"
       []
       [(Term.structInstField (Term.structInstLVal `toFun []) ":=" `Subtype.val)
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
           (Term.anonymousCtor
            "⟨"
            [`x
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
                   [(Tactic.rwRule
                     []
                     (Term.app
                      `set.range_iff_surjective.mpr
                      [(Term.app
                        (Term.proj (Term.app `TopCat.epi_iff_surjective [(Term.hole "_")]) "." `mp)
                        [`h'])]))]
                   "]")
                  [])
                 []
                 (Tactic.tacticTrivial "trivial")])))]
            "⟩"))))
        []
        (Term.structInstField
         (Term.structInstLVal `left_inv [])
         ":="
         (Term.fun
          "fun"
          (Term.basicFun
           [(Term.anonymousCtor "⟨" [(Term.hole "_") "," (Term.hole "_")] "⟩")]
           []
           "=>"
           `rfl)))
        []
        (Term.structInstField
         (Term.structInstLVal `right_inv [])
         ":="
         (Term.fun "fun" (Term.basicFun [(Term.hole "_")] [] "=>" `rfl)))]
       (Term.optEllipsis [])
       []
       "}")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun "fun" (Term.basicFun [(Term.hole "_")] [] "=>" `rfl))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rfl
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [(Term.anonymousCtor "⟨" [(Term.hole "_") "," (Term.hole "_")] "⟩")]
        []
        "=>"
        `rfl))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rfl
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [(Term.hole "_") "," (Term.hole "_")] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
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
        (Term.anonymousCtor
         "⟨"
         [`x
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
                [(Tactic.rwRule
                  []
                  (Term.app
                   `set.range_iff_surjective.mpr
                   [(Term.app
                     (Term.proj (Term.app `TopCat.epi_iff_surjective [(Term.hole "_")]) "." `mp)
                     [`h'])]))]
                "]")
               [])
              []
              (Tactic.tacticTrivial "trivial")])))]
         "⟩")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [`x
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
              [(Tactic.rwRule
                []
                (Term.app
                 `set.range_iff_surjective.mpr
                 [(Term.app
                   (Term.proj (Term.app `TopCat.epi_iff_surjective [(Term.hole "_")]) "." `mp)
                   [`h'])]))]
              "]")
             [])
            []
            (Tactic.tacticTrivial "trivial")])))]
       "⟩")
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
            [(Tactic.rwRule
              []
              (Term.app
               `set.range_iff_surjective.mpr
               [(Term.app
                 (Term.proj (Term.app `TopCat.epi_iff_surjective [(Term.hole "_")]) "." `mp)
                 [`h'])]))]
            "]")
           [])
          []
          (Tactic.tacticTrivial "trivial")])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticTrivial "trivial")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule
          []
          (Term.app
           `set.range_iff_surjective.mpr
           [(Term.app
             (Term.proj (Term.app `TopCat.epi_iff_surjective [(Term.hole "_")]) "." `mp)
             [`h'])]))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `set.range_iff_surjective.mpr
       [(Term.app
         (Term.proj (Term.app `TopCat.epi_iff_surjective [(Term.hole "_")]) "." `mp)
         [`h'])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj (Term.app `TopCat.epi_iff_surjective [(Term.hole "_")]) "." `mp) [`h'])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app `TopCat.epi_iff_surjective [(Term.hole "_")]) "." `mp)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `TopCat.epi_iff_surjective [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `TopCat.epi_iff_surjective
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `TopCat.epi_iff_surjective [(Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      (Term.proj
       (Term.paren "(" (Term.app `TopCat.epi_iff_surjective [(Term.hole "_")]) ")")
       "."
       `mp)
      [`h'])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `set.range_iff_surjective.mpr
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Subtype.val
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (Term.app `Homeomorph.ofEmbedding [(Term.hole "_") `h.base_open.to_embedding])
       "."
       `trans)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `Homeomorph.ofEmbedding [(Term.hole "_") `h.base_open.to_embedding])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h.base_open.to_embedding
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Homeomorph.ofEmbedding
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `Homeomorph.ofEmbedding [(Term.hole "_") `h.base_open.to_embedding])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Topology.Homeomorph.«term_≃ₜ_» `X " ≃ₜ " `Y)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Y
[PrettyPrinter.parenthesize] ...precedences are 26 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
      `X
[PrettyPrinter.parenthesize] ...precedences are 25 >? 1024, (none, [anonymous]) <=? (some 25, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 25, (some 26, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Lean.termThis "this")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.applyWith
       "apply"
       "("
       "config"
       ":="
       (Term.structInst
        "{"
        []
        [(Term.structInstField (Term.structInstLVal `instances []) ":=" `false)]
        (Term.optEllipsis [])
        []
        "}")
       ")"
       `is_iso_of_components)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `is_iso_of_components
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.structInst
       "{"
       []
       [(Term.structInstField (Term.structInstLVal `instances []) ":=" `false)]
       (Term.optEllipsis [])
       []
       "}")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `false
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app `IsIso [`f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `IsIso
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.instBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.instBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.instBinder', expected 'Lean.Parser.Term.explicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.instBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.instBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Epi [(Term.proj `f "." `base)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `f "." `base)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Epi
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.instBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.instBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.instBinder', expected 'Lean.Parser.Term.explicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.instBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.instBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termis_open_immersion
        "is_open_immersion")
       [`f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termis_open_immersion
       "is_open_immersion")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termis_open_immersion', expected 'AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termis_open_immersion._@.AlgebraicGeometry.OpenImmersion._hyg.21'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/-- An open immersion is an iso if the underlying continuous map is epi. -/
  theorem
    to_iso
    ( f : X ⟶ Y ) [ h : is_open_immersion f ] [ h' : Epi f . base ] : IsIso f
    :=
      by
        apply ( config := { instances := false } ) is_iso_of_components
          ·
            let
                this
                  : X ≃ₜ Y
                  :=
                  Homeomorph.ofEmbedding _ h.base_open.to_embedding . trans
                    {
                      toFun := Subtype.val
                        invFun
                          :=
                          fun
                            x
                              =>
                              ⟨
                                x
                                  ,
                                  by
                                    rw
                                        [
                                          set.range_iff_surjective.mpr
                                            TopCat.epi_iff_surjective _ . mp h'
                                          ]
                                      trivial
                                ⟩
                        left_inv := fun ⟨ _ , _ ⟩ => rfl
                        right_inv := fun _ => rfl
                      }
              convert is_iso.of_iso TopCat.isoOfHomeo this
              · ext rfl
          ·
            apply ( config := { instances := false } ) nat_iso.is_iso_of_is_iso_app
              intro U
              have
                : U = op h.open_functor.obj opens.map f.base . obj unop U
                  :=
                  by
                    induction U using Opposite.rec
                      cases U
                      dsimp only [ functor.op , opens.map ]
                      congr
                      exact Set.image_preimage_eq _ TopCat.epi_iff_surjective _ . mp h' . symm
              convert @ is_open_immersion.c_iso _ h opens.map f.base . obj unop U
#align
  algebraic_geometry.PresheafedSpace.is_open_immersion.to_iso AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.to_iso

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.instance
      (Term.attrKind [])
      "instance"
      []
      [(Command.declId `stalk_iso [])]
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `HasColimits [`C]) "]")
        (Term.instBinder
         "["
         [`H ":"]
         (Term.app
          (AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termis_open_immersion
           "is_open_immersion")
          [`f])
         "]")
        (Term.explicitBinder "(" [`x] [":" `X] [] ")")]
       (Term.typeSpec ":" (Term.app `IsIso [(Term.app `stalkMap [`f `x])])))
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
             [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `H.iso_restrict_hom_of_restrict)]
             "]")
            [])
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `PresheafedSpace.stalk_map.comp)] "]")
            [])
           []
           (Tactic.tacticInfer_instance "infer_instance")])))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.opaque'
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
            [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `H.iso_restrict_hom_of_restrict)]
            "]")
           [])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `PresheafedSpace.stalk_map.comp)] "]")
           [])
          []
          (Tactic.tacticInfer_instance "infer_instance")])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticInfer_instance "infer_instance")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `PresheafedSpace.stalk_map.comp)] "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `PresheafedSpace.stalk_map.comp
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `H.iso_restrict_hom_of_restrict)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `H.iso_restrict_hom_of_restrict
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app `IsIso [(Term.app `stalkMap [`f `x])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `stalkMap [`f `x])
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
      `stalkMap
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `stalkMap [`f `x]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `IsIso
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `X
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.instBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.instBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.instBinder', expected 'Lean.Parser.Term.explicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.instBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.instBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termis_open_immersion
        "is_open_immersion")
       [`f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termis_open_immersion
       "is_open_immersion")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termis_open_immersion', expected 'AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termis_open_immersion._@.AlgebraicGeometry.OpenImmersion._hyg.21'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
instance
  stalk_iso
  [ HasColimits C ] [ H : is_open_immersion f ] ( x : X ) : IsIso stalkMap f x
  := by rw [ ← H.iso_restrict_hom_of_restrict ] rw [ PresheafedSpace.stalk_map.comp ] infer_instance
#align
  algebraic_geometry.PresheafedSpace.is_open_immersion.stalk_iso AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.stalk_iso

end

section Pullback

noncomputable section

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.variable
     "variable"
     [(Term.implicitBinder
       "{"
       [`X `Y `Z]
       [":" (Term.app (Term.explicitUniv `PresheafedSpaceCat ".{" [`v] "}") [`C])]
       "}")
      (Term.explicitBinder "(" [`f] [":" (Combinatorics.Quiver.Basic.«term_⟶_» `X " ⟶ " `Z)] [] ")")
      (Term.instBinder
       "["
       [`hf ":"]
       (Term.app
        (AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termis_open_immersion
         "is_open_immersion")
        [`f])
       "]")
      (Term.explicitBinder
       "("
       [`g]
       [":" (Combinatorics.Quiver.Basic.«term_⟶_» `Y " ⟶ " `Z)]
       []
       ")")])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Combinatorics.Quiver.Basic.«term_⟶_» `Y " ⟶ " `Z)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Z
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      `Y
[PrettyPrinter.parenthesize] ...precedences are 11 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 10, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.instBinder', expected 'Lean.Parser.Term.explicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.instBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.instBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termis_open_immersion
        "is_open_immersion")
       [`f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termis_open_immersion
       "is_open_immersion")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termis_open_immersion', expected 'AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termis_open_immersion._@.AlgebraicGeometry.OpenImmersion._hyg.21'-/-- failed to format: format: uncaught backtrack exception
variable
  { X Y Z : PresheafedSpaceCat .{ v } C } ( f : X ⟶ Z ) [ hf : is_open_immersion f ] ( g : Y ⟶ Z )

include hf

/-- (Implementation.) The projection map when constructing the pullback along an open immersion.
-/
def pullbackConeOfLeftFst :
    Y.restrict (TopCat.snd_open_embedding_of_left_open_embedding hf.base_open g.base) ⟶ X
    where
  base := pullback.fst
  c :=
    { app := fun U =>
        hf.invApp (unop U) ≫
          g.c.app (op (hf.base_open.IsOpenMap.Functor.obj (unop U))) ≫
            Y.Presheaf.map
              (eqToHom
                (by
                  simp only [IsOpenMap.functor, Subtype.mk_eq_mk, unop_op, op_inj_iff, opens.map,
                    Subtype.coe_mk, functor.op_obj, Subtype.val_eq_coe]
                  apply LE.le.antisymm
                  · rintro _ ⟨_, h₁, h₂⟩
                    use (TopCat.pullbackIsoProdSubtype _ _).inv ⟨⟨_, _⟩, h₂⟩
                    simpa using h₁
                  · rintro _ ⟨x, h₁, rfl⟩
                    exact ⟨_, h₁, concrete_category.congr_hom pullback.condition x⟩))
      naturality' := by
        intro U V i
        induction U using Opposite.rec
        induction V using Opposite.rec
        simp only [Quiver.Hom.unop_op, TopCat.Presheaf.pushforward_obj_map, category.assoc,
          nat_trans.naturality_assoc, functor.op_map, inv_naturality_assoc, ← Y.presheaf.map_comp]
        erw [← Y.presheaf.map_comp]
        congr }
#align
  algebraic_geometry.PresheafedSpace.is_open_immersion.pullback_cone_of_left_fst AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.pullbackConeOfLeftFst

theorem pullback_cone_of_left_condition : pullbackConeOfLeftFst f g ≫ f = Y.of_restrict _ ≫ g :=
  by
  ext U
  · induction U using Opposite.rec
    dsimp only [comp_c_app, nat_trans.comp_app, unop_op, whisker_right_app,
      pullback_cone_of_left_fst]
    simp only [Quiver.Hom.unop_op, TopCat.Presheaf.pushforward_obj_map, app_inv_app_assoc,
      eq_to_hom_app, eq_to_hom_unop, category.assoc, nat_trans.naturality_assoc, functor.op_map]
    erw [← Y.presheaf.map_comp, ← Y.presheaf.map_comp]
    congr
  · simpa using pullback.condition
#align
  algebraic_geometry.PresheafedSpace.is_open_immersion.pullback_cone_of_left_condition AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.pullback_cone_of_left_condition

/-- We construct the pullback along an open immersion via restricting along the pullback of the
maps of underlying spaces (which is also an open embedding).
-/
def pullbackConeOfLeft : PullbackCone f g :=
  PullbackCone.mk (pullbackConeOfLeftFst f g) (Y.of_restrict _)
    (pullback_cone_of_left_condition f g)
#align
  algebraic_geometry.PresheafedSpace.is_open_immersion.pullback_cone_of_left AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.pullbackConeOfLeft

variable (s : PullbackCone f g)

/-- (Implementation.) Any cone over `cospan f g` indeed factors through the constructed cone.
-/
def pullbackConeOfLeftLift : s.x ⟶ (pullbackConeOfLeft f g).x
    where
  base :=
    pullback.lift s.fst.base s.snd.base
      (congr_arg (fun x => PresheafedSpaceCat.Hom.base x) s.condition)
  c :=
    { app := fun U =>
        s.snd.c.app _ ≫
          s.x.Presheaf.map
            (eqToHom
              (by
                dsimp only [opens.map, IsOpenMap.functor, functor.op]
                congr 2
                let s' : pullback_cone f.base g.base := pullback_cone.mk s.fst.base s.snd.base _
                have : _ = s.snd.base := limit.lift_π s' walking_cospan.right
                conv_lhs =>
                  erw [← this]
                  rw [coe_comp]
                  erw [← Set.preimage_preimage]
                erw [Set.preimage_image_eq _
                    (TopCat.snd_open_embedding_of_left_open_embedding hf.base_open g.base).inj]
                simp))
      naturality' := fun U V i => by
        erw [s.snd.c.naturality_assoc]
        rw [category.assoc]
        erw [← s.X.presheaf.map_comp, ← s.X.presheaf.map_comp]
        congr }
#align
  algebraic_geometry.PresheafedSpace.is_open_immersion.pullback_cone_of_left_lift AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.pullbackConeOfLeftLift

-- this lemma is not a `simp` lemma, because it is an implementation detail
theorem pullback_cone_of_left_lift_fst :
    pullbackConeOfLeftLift f g s ≫ (pullbackConeOfLeft f g).fst = s.fst :=
  by
  ext x
  · induction x using Opposite.rec
    change ((_ ≫ _) ≫ _ ≫ _) ≫ _ = _
    simp_rw [category.assoc]
    erw [← s.X.presheaf.map_comp]
    erw [s.snd.c.naturality_assoc]
    have := congr_app s.condition (op (hf.open_functor.obj x))
    dsimp only [comp_c_app, unop_op] at this
    rw [← is_iso.comp_inv_eq] at this
    reassoc! this
    erw [← this, hf.inv_app_app_assoc, s.fst.c.naturality_assoc]
    simpa [eq_to_hom_map]
  · change pullback.lift _ _ _ ≫ pullback.fst = _
    simp
#align
  algebraic_geometry.PresheafedSpace.is_open_immersion.pullback_cone_of_left_lift_fst AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.pullback_cone_of_left_lift_fst

-- this lemma is not a `simp` lemma, because it is an implementation detail
theorem pullback_cone_of_left_lift_snd :
    pullbackConeOfLeftLift f g s ≫ (pullbackConeOfLeft f g).snd = s.snd :=
  by
  ext x
  · change (_ ≫ _ ≫ _) ≫ _ = _
    simp_rw [category.assoc]
    erw [s.snd.c.naturality_assoc]
    erw [← s.X.presheaf.map_comp, ← s.X.presheaf.map_comp]
    trans s.snd.c.app x ≫ s.X.presheaf.map (𝟙 _)
    · congr
    · rw [s.X.presheaf.map_id]
      erw [category.comp_id]
  · change pullback.lift _ _ _ ≫ pullback.snd = _
    simp
#align
  algebraic_geometry.PresheafedSpace.is_open_immersion.pullback_cone_of_left_lift_snd AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.pullback_cone_of_left_lift_snd

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.instance
      (Term.attrKind [])
      "instance"
      []
      [(Command.declId `pullbackConeSndIsOpenImmersion [])]
      (Command.declSig
       []
       (Term.typeSpec
        ":"
        (Term.app
         (AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termis_open_immersion
          "is_open_immersion")
         [(Term.proj (Term.app `pullbackConeOfLeft [`f `g]) "." `snd)])))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.tacticErw__
            "erw"
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [] `CategoryTheory.Limits.PullbackCone.mk_snd)]
             "]")
            [])
           []
           (Tactic.tacticInfer_instance "infer_instance")])))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.tacticErw__
           "erw"
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `CategoryTheory.Limits.PullbackCone.mk_snd)]
            "]")
           [])
          []
          (Tactic.tacticInfer_instance "infer_instance")])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticInfer_instance "infer_instance")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticErw__
       "erw"
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `CategoryTheory.Limits.PullbackCone.mk_snd)] "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `CategoryTheory.Limits.PullbackCone.mk_snd
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app
       (AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termis_open_immersion
        "is_open_immersion")
       [(Term.proj (Term.app `pullbackConeOfLeft [`f `g]) "." `snd)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.app `pullbackConeOfLeft [`f `g]) "." `snd)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `pullbackConeOfLeft [`f `g])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `pullbackConeOfLeft
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `pullbackConeOfLeft [`f `g])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termis_open_immersion
       "is_open_immersion")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termis_open_immersion', expected 'AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termis_open_immersion._@.AlgebraicGeometry.OpenImmersion._hyg.21'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
instance
  pullbackConeSndIsOpenImmersion
  : is_open_immersion pullbackConeOfLeft f g . snd
  := by erw [ CategoryTheory.Limits.PullbackCone.mk_snd ] infer_instance
#align
  algebraic_geometry.PresheafedSpace.is_open_immersion.pullback_cone_snd_is_open_immersion AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.pullbackConeSndIsOpenImmersion

/-- The constructed pullback cone is indeed the pullback. -/
def pullbackConeOfLeftIsLimit : IsLimit (pullbackConeOfLeft f g) :=
  by
  apply pullback_cone.is_limit_aux'
  intro s
  use pullback_cone_of_left_lift f g s
  use pullback_cone_of_left_lift_fst f g s
  use pullback_cone_of_left_lift_snd f g s
  intro m h₁ h₂
  rw [← cancel_mono (pullback_cone_of_left f g).snd]
  exact h₂.trans (pullback_cone_of_left_lift_snd f g s).symm
#align
  algebraic_geometry.PresheafedSpace.is_open_immersion.pullback_cone_of_left_is_limit AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.pullbackConeOfLeftIsLimit

instance has_pullback_of_left : HasPullback f g :=
  ⟨⟨⟨_, pullbackConeOfLeftIsLimit f g⟩⟩⟩
#align
  algebraic_geometry.PresheafedSpace.is_open_immersion.has_pullback_of_left AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.has_pullback_of_left

instance has_pullback_of_right : HasPullback g f :=
  has_pullback_symmetry f g
#align
  algebraic_geometry.PresheafedSpace.is_open_immersion.has_pullback_of_right AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.has_pullback_of_right

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment "/--" "Open immersions are stable under base-change. -/")]
      []
      []
      []
      []
      [])
     (Command.instance
      (Term.attrKind [])
      "instance"
      []
      [(Command.declId `pullbackSndOfLeft [])]
      (Command.declSig
       []
       (Term.typeSpec
        ":"
        (Term.app
         (AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termis_open_immersion
          "is_open_immersion")
         [(Term.typeAscription
           "("
           `pullback.snd
           ":"
           [(Combinatorics.Quiver.Basic.«term_⟶_»
             (Term.app `pullback [`f `g])
             " ⟶ "
             (Term.hole "_"))]
           ")")])))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.delta "delta" [`pullback.snd] [])
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule
               [(patternIgnore (token.«← » "←"))]
               (Term.app
                `limit.iso_limit_cone_hom_π
                [(Term.anonymousCtor
                  "⟨"
                  [(Term.hole "_") "," (Term.app `pullback_cone_of_left_is_limit [`f `g])]
                  "⟩")
                 `walking_cospan.right]))]
             "]")
            [])
           []
           (Tactic.tacticInfer_instance "infer_instance")])))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.delta "delta" [`pullback.snd] [])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule
              [(patternIgnore (token.«← » "←"))]
              (Term.app
               `limit.iso_limit_cone_hom_π
               [(Term.anonymousCtor
                 "⟨"
                 [(Term.hole "_") "," (Term.app `pullback_cone_of_left_is_limit [`f `g])]
                 "⟩")
                `walking_cospan.right]))]
            "]")
           [])
          []
          (Tactic.tacticInfer_instance "infer_instance")])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticInfer_instance "infer_instance")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule
          [(patternIgnore (token.«← » "←"))]
          (Term.app
           `limit.iso_limit_cone_hom_π
           [(Term.anonymousCtor
             "⟨"
             [(Term.hole "_") "," (Term.app `pullback_cone_of_left_is_limit [`f `g])]
             "⟩")
            `walking_cospan.right]))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `limit.iso_limit_cone_hom_π
       [(Term.anonymousCtor
         "⟨"
         [(Term.hole "_") "," (Term.app `pullback_cone_of_left_is_limit [`f `g])]
         "⟩")
        `walking_cospan.right])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `walking_cospan.right
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.anonymousCtor
       "⟨"
       [(Term.hole "_") "," (Term.app `pullback_cone_of_left_is_limit [`f `g])]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `pullback_cone_of_left_is_limit [`f `g])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `pullback_cone_of_left_is_limit
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `limit.iso_limit_cone_hom_π
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.delta "delta" [`pullback.snd] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app
       (AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termis_open_immersion
        "is_open_immersion")
       [(Term.typeAscription
         "("
         `pullback.snd
         ":"
         [(Combinatorics.Quiver.Basic.«term_⟶_» (Term.app `pullback [`f `g]) " ⟶ " (Term.hole "_"))]
         ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription
       "("
       `pullback.snd
       ":"
       [(Combinatorics.Quiver.Basic.«term_⟶_» (Term.app `pullback [`f `g]) " ⟶ " (Term.hole "_"))]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Combinatorics.Quiver.Basic.«term_⟶_» (Term.app `pullback [`f `g]) " ⟶ " (Term.hole "_"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      (Term.app `pullback [`f `g])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `pullback
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 11 >? 1022, (some 1023, term) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 10, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `pullback.snd
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termis_open_immersion
       "is_open_immersion")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termis_open_immersion', expected 'AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termis_open_immersion._@.AlgebraicGeometry.OpenImmersion._hyg.21'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/-- Open immersions are stable under base-change. -/
  instance
    pullbackSndOfLeft
    : is_open_immersion ( pullback.snd : pullback f g ⟶ _ )
    :=
      by
        delta pullback.snd
          rw
            [
              ←
                limit.iso_limit_cone_hom_π
                  ⟨ _ , pullback_cone_of_left_is_limit f g ⟩ walking_cospan.right
              ]
          infer_instance
#align
  algebraic_geometry.PresheafedSpace.is_open_immersion.pullback_snd_of_left AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.pullbackSndOfLeft

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment "/--" "Open immersions are stable under base-change. -/")]
      []
      []
      []
      []
      [])
     (Command.instance
      (Term.attrKind [])
      "instance"
      []
      [(Command.declId `pullbackFstOfRight [])]
      (Command.declSig
       []
       (Term.typeSpec
        ":"
        (Term.app
         (AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termis_open_immersion
          "is_open_immersion")
         [(Term.typeAscription
           "("
           `pullback.fst
           ":"
           [(Combinatorics.Quiver.Basic.«term_⟶_»
             (Term.app `pullback [`g `f])
             " ⟶ "
             (Term.hole "_"))]
           ")")])))
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
             [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `pullback_symmetry_hom_comp_snd)]
             "]")
            [])
           []
           (Tactic.tacticInfer_instance "infer_instance")])))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.opaque'
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
            [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `pullback_symmetry_hom_comp_snd)]
            "]")
           [])
          []
          (Tactic.tacticInfer_instance "infer_instance")])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticInfer_instance "infer_instance")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `pullback_symmetry_hom_comp_snd)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `pullback_symmetry_hom_comp_snd
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app
       (AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termis_open_immersion
        "is_open_immersion")
       [(Term.typeAscription
         "("
         `pullback.fst
         ":"
         [(Combinatorics.Quiver.Basic.«term_⟶_» (Term.app `pullback [`g `f]) " ⟶ " (Term.hole "_"))]
         ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription
       "("
       `pullback.fst
       ":"
       [(Combinatorics.Quiver.Basic.«term_⟶_» (Term.app `pullback [`g `f]) " ⟶ " (Term.hole "_"))]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Combinatorics.Quiver.Basic.«term_⟶_» (Term.app `pullback [`g `f]) " ⟶ " (Term.hole "_"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      (Term.app `pullback [`g `f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `pullback
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 11 >? 1022, (some 1023, term) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 10, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `pullback.fst
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termis_open_immersion
       "is_open_immersion")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termis_open_immersion', expected 'AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termis_open_immersion._@.AlgebraicGeometry.OpenImmersion._hyg.21'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/-- Open immersions are stable under base-change. -/
  instance
    pullbackFstOfRight
    : is_open_immersion ( pullback.fst : pullback g f ⟶ _ )
    := by rw [ ← pullback_symmetry_hom_comp_snd ] infer_instance
#align
  algebraic_geometry.PresheafedSpace.is_open_immersion.pullback_fst_of_right AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.pullbackFstOfRight

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.instance
      (Term.attrKind [])
      "instance"
      []
      [(Command.declId `pullbackToBaseIsOpenImmersion [])]
      (Command.declSig
       [(Term.instBinder
         "["
         []
         (Term.app
          (AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termis_open_immersion
           "is_open_immersion")
          [`g])
         "]")]
       (Term.typeSpec
        ":"
        (Term.app
         (AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termis_open_immersion
          "is_open_immersion")
         [(Term.app `limit.π [(Term.app `cospan [`f `g]) `WalkingCospan.one])])))
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
             [(Tactic.rwRule
               [(patternIgnore (token.«← » "←"))]
               (Term.app `limit.w [(Term.app `cospan [`f `g]) `walking_cospan.hom.inl]))
              ","
              (Tactic.rwRule [] `cospan_map_inl)]
             "]")
            [])
           []
           (Tactic.tacticInfer_instance "infer_instance")])))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.opaque'
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
            [(Tactic.rwRule
              [(patternIgnore (token.«← » "←"))]
              (Term.app `limit.w [(Term.app `cospan [`f `g]) `walking_cospan.hom.inl]))
             ","
             (Tactic.rwRule [] `cospan_map_inl)]
            "]")
           [])
          []
          (Tactic.tacticInfer_instance "infer_instance")])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticInfer_instance "infer_instance")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule
          [(patternIgnore (token.«← » "←"))]
          (Term.app `limit.w [(Term.app `cospan [`f `g]) `walking_cospan.hom.inl]))
         ","
         (Tactic.rwRule [] `cospan_map_inl)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `cospan_map_inl
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `limit.w [(Term.app `cospan [`f `g]) `walking_cospan.hom.inl])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `walking_cospan.hom.inl
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `cospan [`f `g])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `cospan
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `cospan [`f `g]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `limit.w
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app
       (AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termis_open_immersion
        "is_open_immersion")
       [(Term.app `limit.π [(Term.app `cospan [`f `g]) `WalkingCospan.one])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `limit.π [(Term.app `cospan [`f `g]) `WalkingCospan.one])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `WalkingCospan.one
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `cospan [`f `g])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `cospan
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `cospan [`f `g]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `limit.π
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `limit.π [(Term.paren "(" (Term.app `cospan [`f `g]) ")") `WalkingCospan.one])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termis_open_immersion
       "is_open_immersion")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termis_open_immersion', expected 'AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termis_open_immersion._@.AlgebraicGeometry.OpenImmersion._hyg.21'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
instance
  pullbackToBaseIsOpenImmersion
  [ is_open_immersion g ] : is_open_immersion limit.π cospan f g WalkingCospan.one
  := by rw [ ← limit.w cospan f g walking_cospan.hom.inl , cospan_map_inl ] infer_instance
#align
  algebraic_geometry.PresheafedSpace.is_open_immersion.pullback_to_base_is_open_immersion AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.pullbackToBaseIsOpenImmersion

instance forgetPreservesLimitsOfLeft : PreservesLimit (cospan f g) (forget C) :=
  preservesLimitOfPreservesLimitCone (pullbackConeOfLeftIsLimit f g)
    (by
      apply (is_limit.postcompose_hom_equiv (diagramIsoCospan.{v} _) _).toFun
      refine' (is_limit.equiv_iso_limit _).toFun (limit.is_limit (cospan f.base g.base))
      fapply cones.ext
      exact iso.refl _
      change ∀ j, _ = 𝟙 _ ≫ _ ≫ _
      simp_rw [category.id_comp]
      rintro (_ | _ | _) <;> symm
      · erw [category.comp_id]
        exact limit.w (cospan f.base g.base) walking_cospan.hom.inl
      · exact category.comp_id _
      · exact category.comp_id _)
#align
  algebraic_geometry.PresheafedSpace.is_open_immersion.forget_preserves_limits_of_left AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.forgetPreservesLimitsOfLeft

instance forgetPreservesLimitsOfRight : PreservesLimit (cospan g f) (forget C) :=
  preservesPullbackSymmetry (forget C) f g
#align
  algebraic_geometry.PresheafedSpace.is_open_immersion.forget_preserves_limits_of_right AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.forgetPreservesLimitsOfRight

theorem pullback_snd_is_iso_of_range_subset (H : Set.range g.base ⊆ Set.range f.base) :
    IsIso (pullback.snd : pullback f g ⟶ _) :=
  by
  haveI := TopCat.snd_iso_of_left_embedding_range_subset hf.base_open.to_embedding g.base H
  have : is_iso (pullback.snd : pullback f g ⟶ _).base :=
    by
    delta pullback.snd
    rw [← limit.iso_limit_cone_hom_π ⟨_, pullback_cone_of_left_is_limit f g⟩ walking_cospan.right]
    change is_iso (_ ≫ pullback.snd)
    infer_instance
  apply to_iso
#align
  algebraic_geometry.PresheafedSpace.is_open_immersion.pullback_snd_is_iso_of_range_subset AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.pullback_snd_is_iso_of_range_subset

/-- The universal property of open immersions:
For an open immersion `f : X ⟶ Z`, given any morphism of schemes `g : Y ⟶ Z` whose topological
image is contained in the image of `f`, we can lift this morphism to a unique `Y ⟶ X` that
commutes with these maps.
-/
def lift (H : Set.range g.base ⊆ Set.range f.base) : Y ⟶ X :=
  haveI := pullback_snd_is_iso_of_range_subset f g H
  inv (pullback.snd : pullback f g ⟶ _) ≫ pullback.fst
#align
  algebraic_geometry.PresheafedSpace.is_open_immersion.lift AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.lift

@[simp, reassoc.1]
theorem lift_fac (H : Set.range g.base ⊆ Set.range f.base) : lift f g H ≫ f = g :=
  by
  erw [category.assoc]
  rw [is_iso.inv_comp_eq]
  exact pullback.condition
#align
  algebraic_geometry.PresheafedSpace.is_open_immersion.lift_fac AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.lift_fac

theorem lift_uniq (H : Set.range g.base ⊆ Set.range f.base) (l : Y ⟶ X) (hl : l ≫ f = g) :
    l = lift f g H := by rw [← cancel_mono f, hl, lift_fac]
#align
  algebraic_geometry.PresheafedSpace.is_open_immersion.lift_uniq AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.lift_uniq

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment "/--" "Two open immersions with equal range is isomorphic. -/")]
      [(Term.attributes
        "@["
        [(Term.attrInstance (Term.attrKind []) (Attr.simps "simps" [] (Attr.simpsArgsRest [] [])))]
        "]")]
      []
      []
      []
      [])
     (Command.def
      "def"
      (Command.declId `isoOfRangeEq [])
      (Command.optDeclSig
       [(Term.instBinder
         "["
         []
         (Term.app
          (AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termis_open_immersion
           "is_open_immersion")
          [`g])
         "]")
        (Term.explicitBinder
         "("
         [`e]
         [":"
          («term_=_»
           (Term.app `Set.range [(Term.proj `f "." `base)])
           "="
           (Term.app `Set.range [(Term.proj `g "." `base)]))]
         []
         ")")]
       [(Term.typeSpec ":" (CategoryTheory.CategoryTheory.Isomorphism.«term_≅_» `X " ≅ " `Y))])
      (Command.whereStructInst
       "where"
       [(Command.whereStructField
         (Term.letDecl
          (Term.letIdDecl `Hom [] [] ":=" (Term.app `lift [`g `f (Term.app `le_of_eq [`e])]))))
        []
        (Command.whereStructField
         (Term.letDecl
          (Term.letIdDecl
           `inv
           []
           []
           ":="
           (Term.app `lift [`f `g (Term.app `le_of_eq [(Term.proj `e "." `symm)])]))))
        []
        (Command.whereStructField
         (Term.letDecl
          (Term.letIdDecl
           `hom_inv_id'
           []
           []
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
                 [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] (Term.app `cancel_mono [`f]))]
                 "]")
                [])
               []
               (Tactic.simp "simp" [] [] [] [] [])]))))))
        []
        (Command.whereStructField
         (Term.letDecl
          (Term.letIdDecl
           `inv_hom_id'
           []
           []
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
                 [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] (Term.app `cancel_mono [`g]))]
                 "]")
                [])
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
         [(Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] (Term.app `cancel_mono [`g]))]
            "]")
           [])
          []
          (Tactic.simp "simp" [] [] [] [] [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] [] [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] (Term.app `cancel_mono [`g]))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `cancel_mono [`g])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `cancel_mono
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
         [(Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] (Term.app `cancel_mono [`f]))]
            "]")
           [])
          []
          (Tactic.simp "simp" [] [] [] [] [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] [] [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] (Term.app `cancel_mono [`f]))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `cancel_mono [`f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `cancel_mono
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `lift [`f `g (Term.app `le_of_eq [(Term.proj `e "." `symm)])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `le_of_eq [(Term.proj `e "." `symm)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `e "." `symm)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `e
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `le_of_eq
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `le_of_eq [(Term.proj `e "." `symm)])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `lift
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `lift [`g `f (Term.app `le_of_eq [`e])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `le_of_eq [`e])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `e
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `le_of_eq
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `le_of_eq [`e]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `lift
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (CategoryTheory.CategoryTheory.Isomorphism.«term_≅_» `X " ≅ " `Y)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Y
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      `X
[PrettyPrinter.parenthesize] ...precedences are 11 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 10,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Term.app `Set.range [(Term.proj `f "." `base)])
       "="
       (Term.app `Set.range [(Term.proj `g "." `base)]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Set.range [(Term.proj `g "." `base)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `g "." `base)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `g
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Set.range
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app `Set.range [(Term.proj `f "." `base)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `f "." `base)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Set.range
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.instBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.instBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.instBinder', expected 'Lean.Parser.Term.explicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.instBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.instBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termis_open_immersion
        "is_open_immersion")
       [`g])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termis_open_immersion
       "is_open_immersion")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termis_open_immersion', expected 'AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termis_open_immersion._@.AlgebraicGeometry.OpenImmersion._hyg.21'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/-- Two open immersions with equal range is isomorphic. -/ @[ simps ]
  def
    isoOfRangeEq
    [ is_open_immersion g ] ( e : Set.range f . base = Set.range g . base ) : X ≅ Y
    where
      Hom := lift g f le_of_eq e
        inv := lift f g le_of_eq e . symm
        hom_inv_id' := by rw [ ← cancel_mono f ] simp
        inv_hom_id' := by rw [ ← cancel_mono g ] simp
#align
  algebraic_geometry.PresheafedSpace.is_open_immersion.iso_of_range_eq AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.isoOfRangeEq

end Pullback

open CategoryTheory.Limits.WalkingCospan

section ToSheafedSpace

variable {X : PresheafedSpaceCat.{v} C} (Y : SheafedSpaceCat C)

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.variable
     "variable"
     [(Term.explicitBinder
       "("
       [`f]
       [":" (Combinatorics.Quiver.Basic.«term_⟶_» `X " ⟶ " (Term.proj `Y "." `toPresheafedSpace))]
       []
       ")")
      (Term.instBinder
       "["
       [`H ":"]
       (Term.app
        (AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termis_open_immersion
         "is_open_immersion")
        [`f])
       "]")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.instBinder', expected 'Lean.Parser.Term.explicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.instBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.instBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termis_open_immersion
        "is_open_immersion")
       [`f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termis_open_immersion
       "is_open_immersion")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termis_open_immersion', expected 'AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termis_open_immersion._@.AlgebraicGeometry.OpenImmersion._hyg.21'-/-- failed to format: format: uncaught backtrack exception
variable ( f : X ⟶ Y . toPresheafedSpace ) [ H : is_open_immersion f ]

include H

/-- If `X ⟶ Y` is an open immersion, and `Y` is a SheafedSpace, then so is `X`. -/
def toSheafedSpace : SheafedSpaceCat C
    where
  IsSheaf :=
    by
    apply TopCat.Presheaf.is_sheaf_of_iso (sheaf_iso_of_iso H.iso_restrict.symm).symm
    apply TopCat.Sheaf.pushforward_sheaf_of_sheaf
    exact (Y.restrict H.base_open).IsSheaf
  toPresheafedSpace := X
#align
  algebraic_geometry.PresheafedSpace.is_open_immersion.to_SheafedSpace AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.toSheafedSpace

@[simp]
theorem to_SheafedSpace_to_PresheafedSpace : (toSheafedSpace Y f).toPresheafedSpace = X :=
  rfl
#align
  algebraic_geometry.PresheafedSpace.is_open_immersion.to_SheafedSpace_to_PresheafedSpace AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.to_SheafedSpace_to_PresheafedSpace

/-- If `X ⟶ Y` is an open immersion of PresheafedSpaces, and `Y` is a SheafedSpace, we can
upgrade it into a morphism of SheafedSpaces.
-/
def toSheafedSpaceHom : toSheafedSpace Y f ⟶ Y :=
  f
#align
  algebraic_geometry.PresheafedSpace.is_open_immersion.to_SheafedSpace_hom AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.toSheafedSpaceHom

@[simp]
theorem to_SheafedSpace_hom_base : (toSheafedSpaceHom Y f).base = f.base :=
  rfl
#align
  algebraic_geometry.PresheafedSpace.is_open_immersion.to_SheafedSpace_hom_base AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.to_SheafedSpace_hom_base

@[simp]
theorem to_SheafedSpace_hom_c : (toSheafedSpaceHom Y f).c = f.c :=
  rfl
#align
  algebraic_geometry.PresheafedSpace.is_open_immersion.to_SheafedSpace_hom_c AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.to_SheafedSpace_hom_c

instance to_SheafedSpace_is_open_immersion :
    SheafedSpaceCat.IsOpenImmersion (toSheafedSpaceHom Y f) :=
  H
#align
  algebraic_geometry.PresheafedSpace.is_open_immersion.to_SheafedSpace_is_open_immersion AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.to_SheafedSpace_is_open_immersion

omit H

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
      (Command.declId `SheafedSpace_to_SheafedSpace [])
      (Command.declSig
       [(Term.implicitBinder
         "{"
         [`X `Y]
         [":" (Term.app (Term.explicitUniv `SheafedSpaceCat ".{" [`v] "}") [`C])]
         "}")
        (Term.explicitBinder
         "("
         [`f]
         [":" (Combinatorics.Quiver.Basic.«term_⟶_» `X " ⟶ " `Y)]
         []
         ")")
        (Term.instBinder
         "["
         []
         (Term.app
          (AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termis_open_immersion
           "is_open_immersion")
          [`f])
         "]")]
       (Term.typeSpec ":" («term_=_» (Term.app `toSheafedSpace [`Y `f]) "=" `X)))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.cases "cases" [(Tactic.casesTarget [] `X)] [] []) [] (Tactic.tacticRfl "rfl")])))
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
         [(Tactic.cases "cases" [(Tactic.casesTarget [] `X)] [] []) [] (Tactic.tacticRfl "rfl")])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticRfl "rfl")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.cases "cases" [(Tactic.casesTarget [] `X)] [] [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `X
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_» (Term.app `toSheafedSpace [`Y `f]) "=" `X)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `X
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app `toSheafedSpace [`Y `f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `Y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `toSheafedSpace
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.instBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.instBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.instBinder', expected 'Lean.Parser.Term.explicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.instBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.instBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termis_open_immersion
        "is_open_immersion")
       [`f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termis_open_immersion
       "is_open_immersion")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termis_open_immersion', expected 'AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termis_open_immersion._@.AlgebraicGeometry.OpenImmersion._hyg.21'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ simp ]
  theorem
    SheafedSpace_to_SheafedSpace
    { X Y : SheafedSpaceCat .{ v } C } ( f : X ⟶ Y ) [ is_open_immersion f ]
      : toSheafedSpace Y f = X
    := by cases X rfl
#align
  algebraic_geometry.PresheafedSpace.is_open_immersion.SheafedSpace_to_SheafedSpace AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.SheafedSpace_to_SheafedSpace

end ToSheafedSpace

section ToLocallyRingedSpace

variable {X : PresheafedSpaceCat.{u} CommRingCat.{u}} (Y : LocallyRingedSpaceCat.{u})

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.variable
     "variable"
     [(Term.explicitBinder
       "("
       [`f]
       [":" (Combinatorics.Quiver.Basic.«term_⟶_» `X " ⟶ " (Term.proj `Y "." `toPresheafedSpace))]
       []
       ")")
      (Term.instBinder
       "["
       [`H ":"]
       (Term.app
        (AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termis_open_immersion
         "is_open_immersion")
        [`f])
       "]")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.instBinder', expected 'Lean.Parser.Term.explicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.instBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.instBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termis_open_immersion
        "is_open_immersion")
       [`f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termis_open_immersion
       "is_open_immersion")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termis_open_immersion', expected 'AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termis_open_immersion._@.AlgebraicGeometry.OpenImmersion._hyg.21'-/-- failed to format: format: uncaught backtrack exception
variable ( f : X ⟶ Y . toPresheafedSpace ) [ H : is_open_immersion f ]

include H

/-- If `X ⟶ Y` is an open immersion, and `Y` is a LocallyRingedSpace, then so is `X`. -/
def toLocallyRingedSpace : LocallyRingedSpaceCat
    where
  toSheafedSpace := toSheafedSpace Y.toSheafedSpace f
  LocalRing x :=
    haveI : LocalRing (Y.to_SheafedSpace.to_PresheafedSpace.stalk (f.base x)) := Y.local_ring _
    (as_iso (stalk_map f x)).commRingIsoToRingEquiv.LocalRing
#align
  algebraic_geometry.PresheafedSpace.is_open_immersion.to_LocallyRingedSpace AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.toLocallyRingedSpace

@[simp]
theorem to_LocallyRingedSpace_to_SheafedSpace :
    (toLocallyRingedSpace Y f).toSheafedSpace = toSheafedSpace Y.1 f :=
  rfl
#align
  algebraic_geometry.PresheafedSpace.is_open_immersion.to_LocallyRingedSpace_to_SheafedSpace AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.to_LocallyRingedSpace_to_SheafedSpace

/-- If `X ⟶ Y` is an open immersion of PresheafedSpaces, and `Y` is a LocallyRingedSpace, we can
upgrade it into a morphism of LocallyRingedSpace.
-/
def toLocallyRingedSpaceHom : toLocallyRingedSpace Y f ⟶ Y :=
  ⟨f, fun x => inferInstance⟩
#align
  algebraic_geometry.PresheafedSpace.is_open_immersion.to_LocallyRingedSpace_hom AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.toLocallyRingedSpaceHom

@[simp]
theorem to_LocallyRingedSpace_hom_val : (toLocallyRingedSpaceHom Y f).val = f :=
  rfl
#align
  algebraic_geometry.PresheafedSpace.is_open_immersion.to_LocallyRingedSpace_hom_val AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.to_LocallyRingedSpace_hom_val

instance to_LocallyRingedSpace_is_open_immersion :
    LocallyRingedSpaceCat.IsOpenImmersion (toLocallyRingedSpaceHom Y f) :=
  H
#align
  algebraic_geometry.PresheafedSpace.is_open_immersion.to_LocallyRingedSpace_is_open_immersion AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.to_LocallyRingedSpace_is_open_immersion

omit H

@[simp]
theorem LocallyRingedSpace_to_LocallyRingedSpace {X Y : LocallyRingedSpaceCat} (f : X ⟶ Y)
    [LocallyRingedSpaceCat.IsOpenImmersion f] : toLocallyRingedSpace Y f.1 = X :=
  by
  cases X
  delta to_LocallyRingedSpace
  simp
#align
  algebraic_geometry.PresheafedSpace.is_open_immersion.LocallyRingedSpace_to_LocallyRingedSpace AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.LocallyRingedSpace_to_LocallyRingedSpace

end ToLocallyRingedSpace

theorem is_iso_of_subset {X Y : PresheafedSpaceCat.{v} C} (f : X ⟶ Y)
    [H : PresheafedSpaceCat.IsOpenImmersion f] (U : Opens Y.carrier)
    (hU : (U : Set Y.carrier) ⊆ Set.range f.base) : IsIso (f.c.app <| op U) :=
  by
  have : U = H.base_open.is_open_map.functor.obj ((opens.map f.base).obj U) :=
    by
    ext1
    exact (set.inter_eq_left_iff_subset.mpr hU).symm.trans set.image_preimage_eq_inter_range.symm
  convert PresheafedSpace.is_open_immersion.c_iso ((opens.map f.base).obj U)
#align
  algebraic_geometry.PresheafedSpace.is_open_immersion.is_iso_of_subset AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.is_iso_of_subset

end PresheafedSpaceCat.IsOpenImmersion

namespace SheafedSpaceCat.IsOpenImmersion

instance (priority := 100) of_is_iso {X Y : SheafedSpaceCat.{v} C} (f : X ⟶ Y) [IsIso f] :
    SheafedSpaceCat.IsOpenImmersion f :=
  @PresheafedSpaceCat.IsOpenImmersion.ofIsIso _ f
    (SheafedSpaceCat.forgetToPresheafedSpace.map_is_iso _)
#align
  algebraic_geometry.SheafedSpace.is_open_immersion.of_is_iso AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.of_is_iso

instance comp {X Y Z : SheafedSpaceCat C} (f : X ⟶ Y) (g : Y ⟶ Z)
    [SheafedSpaceCat.IsOpenImmersion f] [SheafedSpaceCat.IsOpenImmersion g] :
    SheafedSpaceCat.IsOpenImmersion (f ≫ g) :=
  PresheafedSpaceCat.IsOpenImmersion.comp f g
#align
  algebraic_geometry.SheafedSpace.is_open_immersion.comp AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.comp

section Pullback

variable {X Y Z : SheafedSpaceCat C} (f : X ⟶ Z) (g : Y ⟶ Z)

variable [H : SheafedSpaceCat.IsOpenImmersion f]

include H

-- mathport name: exprforget
local notation "forget" => SheafedSpaceCat.forgetToPresheafedSpace

open CategoryTheory.Limits.WalkingCospan

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.instance
      (Term.attrKind [])
      "instance"
      []
      []
      (Command.declSig [] (Term.typeSpec ":" (Term.app `Mono [`f])))
      (Command.declValSimple
       ":="
       (Term.app
        (Term.proj
         (AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget
          "forget")
         "."
         `mono_of_mono_map)
        [(Term.show
          "show"
          (Term.app
           (Term.explicit "@" `Mono)
           [(Term.app `PresheafedSpaceCat [`C]) (Term.hole "_") (Term.hole "_") (Term.hole "_") `f])
          (Term.byTactic'
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented [(Tactic.tacticInfer_instance "infer_instance")]))))])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget
         "forget")
        "."
        `mono_of_mono_map)
       [(Term.show
         "show"
         (Term.app
          (Term.explicit "@" `Mono)
          [(Term.app `PresheafedSpaceCat [`C]) (Term.hole "_") (Term.hole "_") (Term.hole "_") `f])
         (Term.byTactic'
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented [(Tactic.tacticInfer_instance "infer_instance")]))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.show', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.show', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.show
       "show"
       (Term.app
        (Term.explicit "@" `Mono)
        [(Term.app `PresheafedSpaceCat [`C]) (Term.hole "_") (Term.hole "_") (Term.hole "_") `f])
       (Term.byTactic'
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented [(Tactic.tacticInfer_instance "infer_instance")]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic'', expected 'Lean.Parser.Term.fromTerm'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticInfer_instance "infer_instance")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app
       (Term.explicit "@" `Mono)
       [(Term.app `PresheafedSpaceCat [`C]) (Term.hole "_") (Term.hole "_") (Term.hole "_") `f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.app `PresheafedSpaceCat [`C])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `C
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `PresheafedSpaceCat
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `PresheafedSpaceCat [`C]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.explicit "@" `Mono)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Mono
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (some 1024,
     term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0,
     tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.show
      "show"
      (Term.app
       (Term.explicit "@" `Mono)
       [(Term.paren "(" (Term.app `PresheafedSpaceCat [`C]) ")")
        (Term.hole "_")
        (Term.hole "_")
        (Term.hole "_")
        `f])
      (Term.byTactic'
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented [(Tactic.tacticInfer_instance "infer_instance")]))))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget
        "forget")
       "."
       `mono_of_mono_map)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget
       "forget")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget', expected 'AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget._@.AlgebraicGeometry.OpenImmersion._hyg.362'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
instance
  : Mono f
  := forget . mono_of_mono_map show @ Mono PresheafedSpaceCat C _ _ _ f by infer_instance

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.instance
      (Term.attrKind [])
      "instance"
      []
      [(Command.declId `forgetMapIsOpenImmersion [])]
      (Command.declSig
       []
       (Term.typeSpec
        ":"
        (Term.app
         `PresheafedSpaceCat.IsOpenImmersion
         [(Term.app
           (Term.proj
            (AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget
             "forget")
            "."
            `map)
           [`f])])))
      (Command.declValSimple
       ":="
       (Term.anonymousCtor "⟨" [(Term.proj `H "." `base_open) "," (Term.proj `H "." `c_iso)] "⟩")
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [(Term.proj `H "." `base_open) "," (Term.proj `H "." `c_iso)] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `H "." `c_iso)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `H
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `H "." `base_open)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `H
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app
       `PresheafedSpaceCat.IsOpenImmersion
       [(Term.app
         (Term.proj
          (AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget
           "forget")
          "."
          `map)
         [`f])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget
         "forget")
        "."
        `map)
       [`f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget
        "forget")
       "."
       `map)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget
       "forget")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget', expected 'AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget._@.AlgebraicGeometry.OpenImmersion._hyg.362'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
instance
  forgetMapIsOpenImmersion
  : PresheafedSpaceCat.IsOpenImmersion forget . map f
  := ⟨ H . base_open , H . c_iso ⟩
#align
  algebraic_geometry.SheafedSpace.is_open_immersion.forget_map_is_open_immersion AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.forgetMapIsOpenImmersion

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.instance
      (Term.attrKind [])
      "instance"
      []
      [(Command.declId `hasLimitCospanForgetOfLeft [])]
      (Command.declSig
       []
       (Term.typeSpec
        ":"
        (Term.app
         `HasLimit
         [(CategoryTheory.Functor.CategoryTheory.Functor.Basic.«term_⋙_»
           (Term.app `cospan [`f `g])
           " ⋙ "
           (AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget
            "forget"))])))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.apply
            "apply"
            (Term.app
             `has_limit_of_iso
             [(Term.proj
               (Term.app (Term.explicitUniv `diagramIsoCospan ".{" [`v] "}") [(Term.hole "_")])
               "."
               `symm)]))
           []
           (Tactic.change
            "change"
            (Term.app
             `has_limit
             [(Term.app
               `cospan
               [(Term.app
                 (Term.proj
                  (AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget
                   "forget")
                  "."
                  `map)
                 [`f])
                (Term.app
                 (Term.proj
                  (AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget
                   "forget")
                  "."
                  `map)
                 [`g])])])
            [])
           []
           (Tactic.tacticInfer_instance "infer_instance")])))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.apply
           "apply"
           (Term.app
            `has_limit_of_iso
            [(Term.proj
              (Term.app (Term.explicitUniv `diagramIsoCospan ".{" [`v] "}") [(Term.hole "_")])
              "."
              `symm)]))
          []
          (Tactic.change
           "change"
           (Term.app
            `has_limit
            [(Term.app
              `cospan
              [(Term.app
                (Term.proj
                 (AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget
                  "forget")
                 "."
                 `map)
                [`f])
               (Term.app
                (Term.proj
                 (AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget
                  "forget")
                 "."
                 `map)
                [`g])])])
           [])
          []
          (Tactic.tacticInfer_instance "infer_instance")])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticInfer_instance "infer_instance")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.change
       "change"
       (Term.app
        `has_limit
        [(Term.app
          `cospan
          [(Term.app
            (Term.proj
             (AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget
              "forget")
             "."
             `map)
            [`f])
           (Term.app
            (Term.proj
             (AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget
              "forget")
             "."
             `map)
            [`g])])])
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `has_limit
       [(Term.app
         `cospan
         [(Term.app
           (Term.proj
            (AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget
             "forget")
            "."
            `map)
           [`f])
          (Term.app
           (Term.proj
            (AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget
             "forget")
            "."
            `map)
           [`g])])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `cospan
       [(Term.app
         (Term.proj
          (AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget
           "forget")
          "."
          `map)
         [`f])
        (Term.app
         (Term.proj
          (AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget
           "forget")
          "."
          `map)
         [`g])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget
         "forget")
        "."
        `map)
       [`g])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget
        "forget")
       "."
       `map)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget
       "forget")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget', expected 'AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget._@.AlgebraicGeometry.OpenImmersion._hyg.362'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
instance
  hasLimitCospanForgetOfLeft
  : HasLimit cospan f g ⋙ forget
  :=
    by
      apply has_limit_of_iso diagramIsoCospan .{ v } _ . symm
        change has_limit cospan forget . map f forget . map g
        infer_instance
#align
  algebraic_geometry.SheafedSpace.is_open_immersion.has_limit_cospan_forget_of_left AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.hasLimitCospanForgetOfLeft

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.instance
      (Term.attrKind [])
      "instance"
      []
      [(Command.declId `hasLimitCospanForgetOfLeft' [])]
      (Command.declSig
       []
       (Term.typeSpec
        ":"
        (Term.app
         `HasLimit
         [(Term.app
           `cospan
           [(Term.app
             (Term.proj
              (CategoryTheory.Functor.CategoryTheory.Functor.Basic.«term_⋙_»
               (Term.app `cospan [`f `g])
               " ⋙ "
               (AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget
                "forget"))
              "."
              `map)
             [`Hom.inl])
            (Term.app
             (Term.proj
              (CategoryTheory.Functor.CategoryTheory.Functor.Basic.«term_⋙_»
               (Term.app `cospan [`f `g])
               " ⋙ "
               (AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget
                "forget"))
              "."
              `map)
             [`Hom.inr])])])))
      (Command.declValSimple
       ":="
       (Term.show
        "show"
        (Term.app
         `HasLimit
         [(Term.app
           `cospan
           [(Term.app
             (Term.proj
              (AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget
               "forget")
              "."
              `map)
             [`f])
            (Term.app
             (Term.proj
              (AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget
               "forget")
              "."
              `map)
             [`g])])])
        (Term.fromTerm "from" `inferInstance))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.show
       "show"
       (Term.app
        `HasLimit
        [(Term.app
          `cospan
          [(Term.app
            (Term.proj
             (AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget
              "forget")
             "."
             `map)
            [`f])
           (Term.app
            (Term.proj
             (AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget
              "forget")
             "."
             `map)
            [`g])])])
       (Term.fromTerm "from" `inferInstance))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `inferInstance
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app
       `HasLimit
       [(Term.app
         `cospan
         [(Term.app
           (Term.proj
            (AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget
             "forget")
            "."
            `map)
           [`f])
          (Term.app
           (Term.proj
            (AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget
             "forget")
            "."
            `map)
           [`g])])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `cospan
       [(Term.app
         (Term.proj
          (AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget
           "forget")
          "."
          `map)
         [`f])
        (Term.app
         (Term.proj
          (AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget
           "forget")
          "."
          `map)
         [`g])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget
         "forget")
        "."
        `map)
       [`g])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget
        "forget")
       "."
       `map)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget
       "forget")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget', expected 'AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget._@.AlgebraicGeometry.OpenImmersion._hyg.362'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
instance
  hasLimitCospanForgetOfLeft'
  : HasLimit cospan cospan f g ⋙ forget . map Hom.inl cospan f g ⋙ forget . map Hom.inr
  := show HasLimit cospan forget . map f forget . map g from inferInstance
#align
  algebraic_geometry.SheafedSpace.is_open_immersion.has_limit_cospan_forget_of_left' AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.hasLimitCospanForgetOfLeft'

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.instance
      (Term.attrKind [])
      "instance"
      []
      [(Command.declId `hasLimitCospanForgetOfRight [])]
      (Command.declSig
       []
       (Term.typeSpec
        ":"
        (Term.app
         `HasLimit
         [(CategoryTheory.Functor.CategoryTheory.Functor.Basic.«term_⋙_»
           (Term.app `cospan [`g `f])
           " ⋙ "
           (AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget
            "forget"))])))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.apply
            "apply"
            (Term.app
             `has_limit_of_iso
             [(Term.proj
               (Term.app (Term.explicitUniv `diagramIsoCospan ".{" [`v] "}") [(Term.hole "_")])
               "."
               `symm)]))
           []
           (Tactic.change
            "change"
            (Term.app
             `has_limit
             [(Term.app
               `cospan
               [(Term.app
                 (Term.proj
                  (AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget
                   "forget")
                  "."
                  `map)
                 [`g])
                (Term.app
                 (Term.proj
                  (AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget
                   "forget")
                  "."
                  `map)
                 [`f])])])
            [])
           []
           (Tactic.tacticInfer_instance "infer_instance")])))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.apply
           "apply"
           (Term.app
            `has_limit_of_iso
            [(Term.proj
              (Term.app (Term.explicitUniv `diagramIsoCospan ".{" [`v] "}") [(Term.hole "_")])
              "."
              `symm)]))
          []
          (Tactic.change
           "change"
           (Term.app
            `has_limit
            [(Term.app
              `cospan
              [(Term.app
                (Term.proj
                 (AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget
                  "forget")
                 "."
                 `map)
                [`g])
               (Term.app
                (Term.proj
                 (AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget
                  "forget")
                 "."
                 `map)
                [`f])])])
           [])
          []
          (Tactic.tacticInfer_instance "infer_instance")])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticInfer_instance "infer_instance")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.change
       "change"
       (Term.app
        `has_limit
        [(Term.app
          `cospan
          [(Term.app
            (Term.proj
             (AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget
              "forget")
             "."
             `map)
            [`g])
           (Term.app
            (Term.proj
             (AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget
              "forget")
             "."
             `map)
            [`f])])])
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `has_limit
       [(Term.app
         `cospan
         [(Term.app
           (Term.proj
            (AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget
             "forget")
            "."
            `map)
           [`g])
          (Term.app
           (Term.proj
            (AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget
             "forget")
            "."
            `map)
           [`f])])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `cospan
       [(Term.app
         (Term.proj
          (AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget
           "forget")
          "."
          `map)
         [`g])
        (Term.app
         (Term.proj
          (AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget
           "forget")
          "."
          `map)
         [`f])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget
         "forget")
        "."
        `map)
       [`f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget
        "forget")
       "."
       `map)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget
       "forget")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget', expected 'AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget._@.AlgebraicGeometry.OpenImmersion._hyg.362'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
instance
  hasLimitCospanForgetOfRight
  : HasLimit cospan g f ⋙ forget
  :=
    by
      apply has_limit_of_iso diagramIsoCospan .{ v } _ . symm
        change has_limit cospan forget . map g forget . map f
        infer_instance
#align
  algebraic_geometry.SheafedSpace.is_open_immersion.has_limit_cospan_forget_of_right AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.hasLimitCospanForgetOfRight

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.instance
      (Term.attrKind [])
      "instance"
      []
      [(Command.declId `hasLimitCospanForgetOfRight' [])]
      (Command.declSig
       []
       (Term.typeSpec
        ":"
        (Term.app
         `HasLimit
         [(Term.app
           `cospan
           [(Term.app
             (Term.proj
              (CategoryTheory.Functor.CategoryTheory.Functor.Basic.«term_⋙_»
               (Term.app `cospan [`g `f])
               " ⋙ "
               (AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget
                "forget"))
              "."
              `map)
             [`Hom.inl])
            (Term.app
             (Term.proj
              (CategoryTheory.Functor.CategoryTheory.Functor.Basic.«term_⋙_»
               (Term.app `cospan [`g `f])
               " ⋙ "
               (AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget
                "forget"))
              "."
              `map)
             [`Hom.inr])])])))
      (Command.declValSimple
       ":="
       (Term.show
        "show"
        (Term.app
         `HasLimit
         [(Term.app
           `cospan
           [(Term.app
             (Term.proj
              (AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget
               "forget")
              "."
              `map)
             [`g])
            (Term.app
             (Term.proj
              (AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget
               "forget")
              "."
              `map)
             [`f])])])
        (Term.fromTerm "from" `inferInstance))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.show
       "show"
       (Term.app
        `HasLimit
        [(Term.app
          `cospan
          [(Term.app
            (Term.proj
             (AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget
              "forget")
             "."
             `map)
            [`g])
           (Term.app
            (Term.proj
             (AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget
              "forget")
             "."
             `map)
            [`f])])])
       (Term.fromTerm "from" `inferInstance))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `inferInstance
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app
       `HasLimit
       [(Term.app
         `cospan
         [(Term.app
           (Term.proj
            (AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget
             "forget")
            "."
            `map)
           [`g])
          (Term.app
           (Term.proj
            (AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget
             "forget")
            "."
            `map)
           [`f])])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `cospan
       [(Term.app
         (Term.proj
          (AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget
           "forget")
          "."
          `map)
         [`g])
        (Term.app
         (Term.proj
          (AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget
           "forget")
          "."
          `map)
         [`f])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget
         "forget")
        "."
        `map)
       [`f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget
        "forget")
       "."
       `map)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget
       "forget")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget', expected 'AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget._@.AlgebraicGeometry.OpenImmersion._hyg.362'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
instance
  hasLimitCospanForgetOfRight'
  : HasLimit cospan cospan g f ⋙ forget . map Hom.inl cospan g f ⋙ forget . map Hom.inr
  := show HasLimit cospan forget . map g forget . map f from inferInstance
#align
  algebraic_geometry.SheafedSpace.is_open_immersion.has_limit_cospan_forget_of_right' AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.hasLimitCospanForgetOfRight'

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.instance
      (Term.attrKind [])
      "instance"
      []
      [(Command.declId `forgetCreatesPullbackOfLeft [])]
      (Command.declSig
       []
       (Term.typeSpec
        ":"
        (Term.app
         `CreatesLimit
         [(Term.app `cospan [`f `g])
          (AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget
           "forget")])))
      (Command.declValSimple
       ":="
       (Term.app
        `createsLimitOfFullyFaithfulOfIso
        [(Term.app
          `PresheafedSpaceCat.IsOpenImmersion.toSheafedSpace
          [`Y
           (Term.app
            (Term.explicit "@" `pullback.snd)
            [(Term.app `PresheafedSpaceCat [`C])
             (Term.hole "_")
             (Term.hole "_")
             (Term.hole "_")
             (Term.hole "_")
             `f
             `g
             (Term.hole "_")])])
         (CategoryTheory.Iso.CategoryTheory.Isomorphism.«term_≪≫_»
          (Term.app
           `eqToIso
           [(Term.show
             "show"
             («term_=_»
              (Term.app `pullback [(Term.hole "_") (Term.hole "_")])
              "="
              (Term.app `pullback [(Term.hole "_") (Term.hole "_")]))
             (Term.byTactic'
              "by"
              (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.congr "congr" [])]))))])
          " ≪≫ "
          (Term.app
           `HasLimit.isoOfNatIso
           [(Term.proj (Term.app `diagramIsoCospan [(Term.hole "_")]) "." `symm)]))])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `createsLimitOfFullyFaithfulOfIso
       [(Term.app
         `PresheafedSpaceCat.IsOpenImmersion.toSheafedSpace
         [`Y
          (Term.app
           (Term.explicit "@" `pullback.snd)
           [(Term.app `PresheafedSpaceCat [`C])
            (Term.hole "_")
            (Term.hole "_")
            (Term.hole "_")
            (Term.hole "_")
            `f
            `g
            (Term.hole "_")])])
        (CategoryTheory.Iso.CategoryTheory.Isomorphism.«term_≪≫_»
         (Term.app
          `eqToIso
          [(Term.show
            "show"
            («term_=_»
             (Term.app `pullback [(Term.hole "_") (Term.hole "_")])
             "="
             (Term.app `pullback [(Term.hole "_") (Term.hole "_")]))
            (Term.byTactic'
             "by"
             (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.congr "congr" [])]))))])
         " ≪≫ "
         (Term.app
          `HasLimit.isoOfNatIso
          [(Term.proj (Term.app `diagramIsoCospan [(Term.hole "_")]) "." `symm)]))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.Iso.CategoryTheory.Isomorphism.«term_≪≫_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.Iso.CategoryTheory.Isomorphism.«term_≪≫_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (CategoryTheory.Iso.CategoryTheory.Isomorphism.«term_≪≫_»
       (Term.app
        `eqToIso
        [(Term.show
          "show"
          («term_=_»
           (Term.app `pullback [(Term.hole "_") (Term.hole "_")])
           "="
           (Term.app `pullback [(Term.hole "_") (Term.hole "_")]))
          (Term.byTactic'
           "by"
           (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.congr "congr" [])]))))])
       " ≪≫ "
       (Term.app
        `HasLimit.isoOfNatIso
        [(Term.proj (Term.app `diagramIsoCospan [(Term.hole "_")]) "." `symm)]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `HasLimit.isoOfNatIso
       [(Term.proj (Term.app `diagramIsoCospan [(Term.hole "_")]) "." `symm)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.app `diagramIsoCospan [(Term.hole "_")]) "." `symm)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `diagramIsoCospan [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `diagramIsoCospan
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `diagramIsoCospan [(Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `HasLimit.isoOfNatIso
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Term.app
       `eqToIso
       [(Term.show
         "show"
         («term_=_»
          (Term.app `pullback [(Term.hole "_") (Term.hole "_")])
          "="
          (Term.app `pullback [(Term.hole "_") (Term.hole "_")]))
         (Term.byTactic'
          "by"
          (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.congr "congr" [])]))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.show', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.show', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.show
       "show"
       («term_=_»
        (Term.app `pullback [(Term.hole "_") (Term.hole "_")])
        "="
        (Term.app `pullback [(Term.hole "_") (Term.hole "_")]))
       (Term.byTactic'
        "by"
        (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.congr "congr" [])]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic'', expected 'Lean.Parser.Term.fromTerm'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.congr "congr" [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app `pullback [(Term.hole "_") (Term.hole "_")])
       "="
       (Term.app `pullback [(Term.hole "_") (Term.hole "_")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `pullback [(Term.hole "_") (Term.hole "_")])
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
      `pullback
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app `pullback [(Term.hole "_") (Term.hole "_")])
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
      `pullback
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0,
     tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.show
      "show"
      («term_=_»
       (Term.app `pullback [(Term.hole "_") (Term.hole "_")])
       "="
       (Term.app `pullback [(Term.hole "_") (Term.hole "_")]))
      (Term.byTactic'
       "by"
       (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.congr "congr" [])]))))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `eqToIso
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1022, (some 1023, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (CategoryTheory.Iso.CategoryTheory.Isomorphism.«term_≪≫_»
      (Term.app
       `eqToIso
       [(Term.paren
         "("
         (Term.show
          "show"
          («term_=_»
           (Term.app `pullback [(Term.hole "_") (Term.hole "_")])
           "="
           (Term.app `pullback [(Term.hole "_") (Term.hole "_")]))
          (Term.byTactic'
           "by"
           (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.congr "congr" [])]))))
         ")")])
      " ≪≫ "
      (Term.app
       `HasLimit.isoOfNatIso
       [(Term.proj (Term.paren "(" (Term.app `diagramIsoCospan [(Term.hole "_")]) ")") "." `symm)]))
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       `PresheafedSpaceCat.IsOpenImmersion.toSheafedSpace
       [`Y
        (Term.app
         (Term.explicit "@" `pullback.snd)
         [(Term.app `PresheafedSpaceCat [`C])
          (Term.hole "_")
          (Term.hole "_")
          (Term.hole "_")
          (Term.hole "_")
          `f
          `g
          (Term.hole "_")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.explicit "@" `pullback.snd)
       [(Term.app `PresheafedSpaceCat [`C])
        (Term.hole "_")
        (Term.hole "_")
        (Term.hole "_")
        (Term.hole "_")
        `f
        `g
        (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.app `PresheafedSpaceCat [`C])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `C
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `PresheafedSpaceCat
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `PresheafedSpaceCat [`C]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.explicit "@" `pullback.snd)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `pullback.snd
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (some 1024,
     term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      (Term.explicit "@" `pullback.snd)
      [(Term.paren "(" (Term.app `PresheafedSpaceCat [`C]) ")")
       (Term.hole "_")
       (Term.hole "_")
       (Term.hole "_")
       (Term.hole "_")
       `f
       `g
       (Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `Y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `PresheafedSpaceCat.IsOpenImmersion.toSheafedSpace
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `PresheafedSpaceCat.IsOpenImmersion.toSheafedSpace
      [`Y
       (Term.paren
        "("
        (Term.app
         (Term.explicit "@" `pullback.snd)
         [(Term.paren "(" (Term.app `PresheafedSpaceCat [`C]) ")")
          (Term.hole "_")
          (Term.hole "_")
          (Term.hole "_")
          (Term.hole "_")
          `f
          `g
          (Term.hole "_")])
        ")")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `createsLimitOfFullyFaithfulOfIso
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app
       `CreatesLimit
       [(Term.app `cospan [`f `g])
        (AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget
         "forget")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget
       "forget")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget', expected 'AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget._@.AlgebraicGeometry.OpenImmersion._hyg.362'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
instance
  forgetCreatesPullbackOfLeft
  : CreatesLimit cospan f g forget
  :=
    createsLimitOfFullyFaithfulOfIso
      PresheafedSpaceCat.IsOpenImmersion.toSheafedSpace
          Y @ pullback.snd PresheafedSpaceCat C _ _ _ _ f g _
        eqToIso show pullback _ _ = pullback _ _ by congr
          ≪≫
          HasLimit.isoOfNatIso diagramIsoCospan _ . symm
#align
  algebraic_geometry.SheafedSpace.is_open_immersion.forget_creates_pullback_of_left AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.forgetCreatesPullbackOfLeft

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.instance
      (Term.attrKind [])
      "instance"
      []
      [(Command.declId `forgetCreatesPullbackOfRight [])]
      (Command.declSig
       []
       (Term.typeSpec
        ":"
        (Term.app
         `CreatesLimit
         [(Term.app `cospan [`g `f])
          (AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget
           "forget")])))
      (Command.declValSimple
       ":="
       (Term.app
        `createsLimitOfFullyFaithfulOfIso
        [(Term.app
          `PresheafedSpaceCat.IsOpenImmersion.toSheafedSpace
          [`Y
           (Term.app
            (Term.explicit "@" `pullback.fst)
            [(Term.app `PresheafedSpaceCat [`C])
             (Term.hole "_")
             (Term.hole "_")
             (Term.hole "_")
             (Term.hole "_")
             `g
             `f
             (Term.hole "_")])])
         (CategoryTheory.Iso.CategoryTheory.Isomorphism.«term_≪≫_»
          (Term.app
           `eqToIso
           [(Term.show
             "show"
             («term_=_»
              (Term.app `pullback [(Term.hole "_") (Term.hole "_")])
              "="
              (Term.app `pullback [(Term.hole "_") (Term.hole "_")]))
             (Term.byTactic'
              "by"
              (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.congr "congr" [])]))))])
          " ≪≫ "
          (Term.app
           `HasLimit.isoOfNatIso
           [(Term.proj (Term.app `diagramIsoCospan [(Term.hole "_")]) "." `symm)]))])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `createsLimitOfFullyFaithfulOfIso
       [(Term.app
         `PresheafedSpaceCat.IsOpenImmersion.toSheafedSpace
         [`Y
          (Term.app
           (Term.explicit "@" `pullback.fst)
           [(Term.app `PresheafedSpaceCat [`C])
            (Term.hole "_")
            (Term.hole "_")
            (Term.hole "_")
            (Term.hole "_")
            `g
            `f
            (Term.hole "_")])])
        (CategoryTheory.Iso.CategoryTheory.Isomorphism.«term_≪≫_»
         (Term.app
          `eqToIso
          [(Term.show
            "show"
            («term_=_»
             (Term.app `pullback [(Term.hole "_") (Term.hole "_")])
             "="
             (Term.app `pullback [(Term.hole "_") (Term.hole "_")]))
            (Term.byTactic'
             "by"
             (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.congr "congr" [])]))))])
         " ≪≫ "
         (Term.app
          `HasLimit.isoOfNatIso
          [(Term.proj (Term.app `diagramIsoCospan [(Term.hole "_")]) "." `symm)]))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.Iso.CategoryTheory.Isomorphism.«term_≪≫_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.Iso.CategoryTheory.Isomorphism.«term_≪≫_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (CategoryTheory.Iso.CategoryTheory.Isomorphism.«term_≪≫_»
       (Term.app
        `eqToIso
        [(Term.show
          "show"
          («term_=_»
           (Term.app `pullback [(Term.hole "_") (Term.hole "_")])
           "="
           (Term.app `pullback [(Term.hole "_") (Term.hole "_")]))
          (Term.byTactic'
           "by"
           (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.congr "congr" [])]))))])
       " ≪≫ "
       (Term.app
        `HasLimit.isoOfNatIso
        [(Term.proj (Term.app `diagramIsoCospan [(Term.hole "_")]) "." `symm)]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `HasLimit.isoOfNatIso
       [(Term.proj (Term.app `diagramIsoCospan [(Term.hole "_")]) "." `symm)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.app `diagramIsoCospan [(Term.hole "_")]) "." `symm)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `diagramIsoCospan [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `diagramIsoCospan
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `diagramIsoCospan [(Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `HasLimit.isoOfNatIso
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Term.app
       `eqToIso
       [(Term.show
         "show"
         («term_=_»
          (Term.app `pullback [(Term.hole "_") (Term.hole "_")])
          "="
          (Term.app `pullback [(Term.hole "_") (Term.hole "_")]))
         (Term.byTactic'
          "by"
          (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.congr "congr" [])]))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.show', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.show', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.show
       "show"
       («term_=_»
        (Term.app `pullback [(Term.hole "_") (Term.hole "_")])
        "="
        (Term.app `pullback [(Term.hole "_") (Term.hole "_")]))
       (Term.byTactic'
        "by"
        (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.congr "congr" [])]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic'', expected 'Lean.Parser.Term.fromTerm'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.congr "congr" [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app `pullback [(Term.hole "_") (Term.hole "_")])
       "="
       (Term.app `pullback [(Term.hole "_") (Term.hole "_")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `pullback [(Term.hole "_") (Term.hole "_")])
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
      `pullback
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app `pullback [(Term.hole "_") (Term.hole "_")])
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
      `pullback
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0,
     tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.show
      "show"
      («term_=_»
       (Term.app `pullback [(Term.hole "_") (Term.hole "_")])
       "="
       (Term.app `pullback [(Term.hole "_") (Term.hole "_")]))
      (Term.byTactic'
       "by"
       (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.congr "congr" [])]))))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `eqToIso
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1022, (some 1023, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (CategoryTheory.Iso.CategoryTheory.Isomorphism.«term_≪≫_»
      (Term.app
       `eqToIso
       [(Term.paren
         "("
         (Term.show
          "show"
          («term_=_»
           (Term.app `pullback [(Term.hole "_") (Term.hole "_")])
           "="
           (Term.app `pullback [(Term.hole "_") (Term.hole "_")]))
          (Term.byTactic'
           "by"
           (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.congr "congr" [])]))))
         ")")])
      " ≪≫ "
      (Term.app
       `HasLimit.isoOfNatIso
       [(Term.proj (Term.paren "(" (Term.app `diagramIsoCospan [(Term.hole "_")]) ")") "." `symm)]))
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       `PresheafedSpaceCat.IsOpenImmersion.toSheafedSpace
       [`Y
        (Term.app
         (Term.explicit "@" `pullback.fst)
         [(Term.app `PresheafedSpaceCat [`C])
          (Term.hole "_")
          (Term.hole "_")
          (Term.hole "_")
          (Term.hole "_")
          `g
          `f
          (Term.hole "_")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.explicit "@" `pullback.fst)
       [(Term.app `PresheafedSpaceCat [`C])
        (Term.hole "_")
        (Term.hole "_")
        (Term.hole "_")
        (Term.hole "_")
        `g
        `f
        (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.app `PresheafedSpaceCat [`C])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `C
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `PresheafedSpaceCat
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `PresheafedSpaceCat [`C]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.explicit "@" `pullback.fst)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `pullback.fst
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (some 1024,
     term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      (Term.explicit "@" `pullback.fst)
      [(Term.paren "(" (Term.app `PresheafedSpaceCat [`C]) ")")
       (Term.hole "_")
       (Term.hole "_")
       (Term.hole "_")
       (Term.hole "_")
       `g
       `f
       (Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `Y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `PresheafedSpaceCat.IsOpenImmersion.toSheafedSpace
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `PresheafedSpaceCat.IsOpenImmersion.toSheafedSpace
      [`Y
       (Term.paren
        "("
        (Term.app
         (Term.explicit "@" `pullback.fst)
         [(Term.paren "(" (Term.app `PresheafedSpaceCat [`C]) ")")
          (Term.hole "_")
          (Term.hole "_")
          (Term.hole "_")
          (Term.hole "_")
          `g
          `f
          (Term.hole "_")])
        ")")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `createsLimitOfFullyFaithfulOfIso
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app
       `CreatesLimit
       [(Term.app `cospan [`g `f])
        (AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget
         "forget")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget
       "forget")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget', expected 'AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget._@.AlgebraicGeometry.OpenImmersion._hyg.362'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
instance
  forgetCreatesPullbackOfRight
  : CreatesLimit cospan g f forget
  :=
    createsLimitOfFullyFaithfulOfIso
      PresheafedSpaceCat.IsOpenImmersion.toSheafedSpace
          Y @ pullback.fst PresheafedSpaceCat C _ _ _ _ g f _
        eqToIso show pullback _ _ = pullback _ _ by congr
          ≪≫
          HasLimit.isoOfNatIso diagramIsoCospan _ . symm
#align
  algebraic_geometry.SheafedSpace.is_open_immersion.forget_creates_pullback_of_right AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.forgetCreatesPullbackOfRight

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.instance
      (Term.attrKind [])
      "instance"
      []
      [(Command.declId `sheafedSpaceForgetPreservesOfLeft [])]
      (Command.declSig
       []
       (Term.typeSpec
        ":"
        (Term.app
         `PreservesLimit
         [(Term.app `cospan [`f `g]) (Term.app `SheafedSpaceCat.forget [`C])])))
      (Command.declValSimple
       ":="
       (Term.app
        (Term.explicit "@" `Limits.compPreservesLimit)
        [(Term.hole "_")
         (Term.hole "_")
         (Term.hole "_")
         (Term.hole "_")
         (AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget
          "forget")
         (Term.app `PresheafedSpaceCat.forget [`C])
         (Term.hole "_")
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Mathlib.Tactic.applyWith
              "apply"
              "("
              "config"
              ":="
              (Term.structInst
               "{"
               []
               [(Term.structInstField (Term.structInstLVal `instances []) ":=" `true)]
               (Term.optEllipsis [])
               []
               "}")
              ")"
              (Term.app
               `preserves_limit_of_iso_diagram
               [(Term.hole "_")
                (Term.proj
                 (Term.app (Term.explicitUniv `diagramIsoCospan ".{" [`v] "}") [(Term.hole "_")])
                 "."
                 `symm)]))
             []
             (Tactic.dsimp "dsimp" [] [] [] [] [])
             []
             (Tactic.tacticInfer_instance "infer_instance")])))])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.explicit "@" `Limits.compPreservesLimit)
       [(Term.hole "_")
        (Term.hole "_")
        (Term.hole "_")
        (Term.hole "_")
        (AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget
         "forget")
        (Term.app `PresheafedSpaceCat.forget [`C])
        (Term.hole "_")
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Mathlib.Tactic.applyWith
             "apply"
             "("
             "config"
             ":="
             (Term.structInst
              "{"
              []
              [(Term.structInstField (Term.structInstLVal `instances []) ":=" `true)]
              (Term.optEllipsis [])
              []
              "}")
             ")"
             (Term.app
              `preserves_limit_of_iso_diagram
              [(Term.hole "_")
               (Term.proj
                (Term.app (Term.explicitUniv `diagramIsoCospan ".{" [`v] "}") [(Term.hole "_")])
                "."
                `symm)]))
            []
            (Tactic.dsimp "dsimp" [] [] [] [] [])
            []
            (Tactic.tacticInfer_instance "infer_instance")])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Mathlib.Tactic.applyWith
           "apply"
           "("
           "config"
           ":="
           (Term.structInst
            "{"
            []
            [(Term.structInstField (Term.structInstLVal `instances []) ":=" `true)]
            (Term.optEllipsis [])
            []
            "}")
           ")"
           (Term.app
            `preserves_limit_of_iso_diagram
            [(Term.hole "_")
             (Term.proj
              (Term.app (Term.explicitUniv `diagramIsoCospan ".{" [`v] "}") [(Term.hole "_")])
              "."
              `symm)]))
          []
          (Tactic.dsimp "dsimp" [] [] [] [] [])
          []
          (Tactic.tacticInfer_instance "infer_instance")])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticInfer_instance "infer_instance")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.dsimp "dsimp" [] [] [] [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.applyWith
       "apply"
       "("
       "config"
       ":="
       (Term.structInst
        "{"
        []
        [(Term.structInstField (Term.structInstLVal `instances []) ":=" `true)]
        (Term.optEllipsis [])
        []
        "}")
       ")"
       (Term.app
        `preserves_limit_of_iso_diagram
        [(Term.hole "_")
         (Term.proj
          (Term.app (Term.explicitUniv `diagramIsoCospan ".{" [`v] "}") [(Term.hole "_")])
          "."
          `symm)]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `preserves_limit_of_iso_diagram
       [(Term.hole "_")
        (Term.proj
         (Term.app (Term.explicitUniv `diagramIsoCospan ".{" [`v] "}") [(Term.hole "_")])
         "."
         `symm)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj
       (Term.app (Term.explicitUniv `diagramIsoCospan ".{" [`v] "}") [(Term.hole "_")])
       "."
       `symm)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app (Term.explicitUniv `diagramIsoCospan ".{" [`v] "}") [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.explicitUniv `diagramIsoCospan ".{" [`v] "}")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `v
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `diagramIsoCospan
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.explicitUniv `diagramIsoCospan ".{" [`v] "}") [(Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `preserves_limit_of_iso_diagram
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.structInst
       "{"
       []
       [(Term.structInstField (Term.structInstLVal `instances []) ":=" `true)]
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
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0,
     tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(Mathlib.Tactic.applyWith
          "apply"
          "("
          "config"
          ":="
          (Term.structInst
           "{"
           []
           [(Term.structInstField (Term.structInstLVal `instances []) ":=" `true)]
           (Term.optEllipsis [])
           []
           "}")
          ")"
          (Term.app
           `preserves_limit_of_iso_diagram
           [(Term.hole "_")
            (Term.proj
             (Term.paren
              "("
              (Term.app (Term.explicitUniv `diagramIsoCospan ".{" [`v] "}") [(Term.hole "_")])
              ")")
             "."
             `symm)]))
         []
         (Tactic.dsimp "dsimp" [] [] [] [] [])
         []
         (Tactic.tacticInfer_instance "infer_instance")])))
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.app `PresheafedSpaceCat.forget [`C])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `C
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `PresheafedSpaceCat.forget
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `PresheafedSpaceCat.forget [`C])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget
       "forget")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget', expected 'AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget._@.AlgebraicGeometry.OpenImmersion._hyg.362'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
instance
  sheafedSpaceForgetPreservesOfLeft
  : PreservesLimit cospan f g SheafedSpaceCat.forget C
  :=
    @ Limits.compPreservesLimit
      _
        _
        _
        _
        forget
        PresheafedSpaceCat.forget C
        _
        by
          apply
              (
              config
              :=
              { instances := true }
              )
              preserves_limit_of_iso_diagram _ diagramIsoCospan .{ v } _ . symm
            dsimp
            infer_instance
#align
  algebraic_geometry.SheafedSpace.is_open_immersion.SheafedSpace_forget_preserves_of_left AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.sheafedSpaceForgetPreservesOfLeft

instance sheafedSpaceForgetPreservesOfRight :
    PreservesLimit (cospan g f) (SheafedSpaceCat.forget C) :=
  preservesPullbackSymmetry _ _ _
#align
  algebraic_geometry.SheafedSpace.is_open_immersion.SheafedSpace_forget_preserves_of_right AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.sheafedSpaceForgetPreservesOfRight

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.instance
      (Term.attrKind [])
      "instance"
      []
      [(Command.declId `SheafedSpace_has_pullback_of_left [])]
      (Command.declSig [] (Term.typeSpec ":" (Term.app `HasPullback [`f `g])))
      (Command.declValSimple
       ":="
       (Term.app
        `hasLimitOfCreated
        [(Term.app `cospan [`f `g])
         (AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget
          "forget")])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `hasLimitOfCreated
       [(Term.app `cospan [`f `g])
        (AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget
         "forget")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget
       "forget")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget', expected 'AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget._@.AlgebraicGeometry.OpenImmersion._hyg.362'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
instance SheafedSpace_has_pullback_of_left : HasPullback f g := hasLimitOfCreated cospan f g forget
#align
  algebraic_geometry.SheafedSpace.is_open_immersion.SheafedSpace_has_pullback_of_left AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.SheafedSpace_has_pullback_of_left

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.instance
      (Term.attrKind [])
      "instance"
      []
      [(Command.declId `SheafedSpace_has_pullback_of_right [])]
      (Command.declSig [] (Term.typeSpec ":" (Term.app `HasPullback [`g `f])))
      (Command.declValSimple
       ":="
       (Term.app
        `hasLimitOfCreated
        [(Term.app `cospan [`g `f])
         (AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget
          "forget")])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `hasLimitOfCreated
       [(Term.app `cospan [`g `f])
        (AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget
         "forget")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget
       "forget")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget', expected 'AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget._@.AlgebraicGeometry.OpenImmersion._hyg.362'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
instance SheafedSpace_has_pullback_of_right : HasPullback g f := hasLimitOfCreated cospan g f forget
#align
  algebraic_geometry.SheafedSpace.is_open_immersion.SheafedSpace_has_pullback_of_right AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.SheafedSpace_has_pullback_of_right

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment "/--" "Open immersions are stable under base-change. -/")]
      []
      []
      []
      []
      [])
     (Command.instance
      (Term.attrKind [])
      "instance"
      []
      [(Command.declId `SheafedSpace_pullback_snd_of_left [])]
      (Command.declSig
       []
       (Term.typeSpec
        ":"
        (Term.app
         `SheafedSpaceCat.IsOpenImmersion
         [(Term.typeAscription
           "("
           `pullback.snd
           ":"
           [(Combinatorics.Quiver.Basic.«term_⟶_»
             (Term.app `pullback [`f `g])
             " ⟶ "
             (Term.hole "_"))]
           ")")])))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.delta "delta" [`pullback.snd] [])
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              []
              [(Term.typeSpec
                ":"
                («term_=_»
                 (Term.hole "_")
                 "="
                 (Term.app `limit.π [(Term.app `cospan [`f `g]) `right])))]
              ":="
              (Term.app
               `preserves_limits_iso_hom_π
               [(AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget
                 "forget")
                (Term.app `cospan [`f `g])
                `right]))))
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq "[" [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `this)] "]")
            [])
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              []
              []
              ":="
              (Term.app
               `has_limit.iso_of_nat_iso_hom_π
               [(Term.app
                 (Term.explicitUniv `diagramIsoCospan ".{" [`v] "}")
                 [(CategoryTheory.Functor.CategoryTheory.Functor.Basic.«term_⋙_»
                   (Term.app `cospan [`f `g])
                   " ⋙ "
                   (AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget
                    "forget"))])
                `right]))))
           []
           (Tactic.tacticErw__
            "erw"
            (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `category.comp_id)] "]")
            [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq "[" [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `this)] "]")
            [])
           []
           (Tactic.dsimp "dsimp" [] [] [] [] [])
           []
           (Tactic.tacticInfer_instance "infer_instance")])))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.delta "delta" [`pullback.snd] [])
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             []
             [(Term.typeSpec
               ":"
               («term_=_»
                (Term.hole "_")
                "="
                (Term.app `limit.π [(Term.app `cospan [`f `g]) `right])))]
             ":="
             (Term.app
              `preserves_limits_iso_hom_π
              [(AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget
                "forget")
               (Term.app `cospan [`f `g])
               `right]))))
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `this)] "]")
           [])
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             []
             []
             ":="
             (Term.app
              `has_limit.iso_of_nat_iso_hom_π
              [(Term.app
                (Term.explicitUniv `diagramIsoCospan ".{" [`v] "}")
                [(CategoryTheory.Functor.CategoryTheory.Functor.Basic.«term_⋙_»
                  (Term.app `cospan [`f `g])
                  " ⋙ "
                  (AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget
                   "forget"))])
               `right]))))
          []
          (Tactic.tacticErw__
           "erw"
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `category.comp_id)] "]")
           [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `this)] "]")
           [])
          []
          (Tactic.dsimp "dsimp" [] [] [] [] [])
          []
          (Tactic.tacticInfer_instance "infer_instance")])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticInfer_instance "infer_instance")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.dsimp "dsimp" [] [] [] [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `this)] "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `this
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticErw__
       "erw"
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `category.comp_id)] "]")
       [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `this
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `category.comp_id
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         []
         []
         ":="
         (Term.app
          `has_limit.iso_of_nat_iso_hom_π
          [(Term.app
            (Term.explicitUniv `diagramIsoCospan ".{" [`v] "}")
            [(CategoryTheory.Functor.CategoryTheory.Functor.Basic.«term_⋙_»
              (Term.app `cospan [`f `g])
              " ⋙ "
              (AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget
               "forget"))])
           `right]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `has_limit.iso_of_nat_iso_hom_π
       [(Term.app
         (Term.explicitUniv `diagramIsoCospan ".{" [`v] "}")
         [(CategoryTheory.Functor.CategoryTheory.Functor.Basic.«term_⋙_»
           (Term.app `cospan [`f `g])
           " ⋙ "
           (AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget
            "forget"))])
        `right])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `right
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       (Term.explicitUniv `diagramIsoCospan ".{" [`v] "}")
       [(CategoryTheory.Functor.CategoryTheory.Functor.Basic.«term_⋙_»
         (Term.app `cospan [`f `g])
         " ⋙ "
         (AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget
          "forget"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.Functor.CategoryTheory.Functor.Basic.«term_⋙_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.Functor.CategoryTheory.Functor.Basic.«term_⋙_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (CategoryTheory.Functor.CategoryTheory.Functor.Basic.«term_⋙_»
       (Term.app `cospan [`f `g])
       " ⋙ "
       (AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget
        "forget"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget
       "forget")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget', expected 'AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget._@.AlgebraicGeometry.OpenImmersion._hyg.362'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.letPatDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveEqnsDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/-- Open immersions are stable under base-change. -/
  instance
    SheafedSpace_pullback_snd_of_left
    : SheafedSpaceCat.IsOpenImmersion ( pullback.snd : pullback f g ⟶ _ )
    :=
      by
        delta pullback.snd
          have : _ = limit.π cospan f g right := preserves_limits_iso_hom_π forget cospan f g right
          rw [ ← this ]
          have := has_limit.iso_of_nat_iso_hom_π diagramIsoCospan .{ v } cospan f g ⋙ forget right
          erw [ category.comp_id ] at this
          rw [ ← this ]
          dsimp
          infer_instance
#align
  algebraic_geometry.SheafedSpace.is_open_immersion.SheafedSpace_pullback_snd_of_left AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.SheafedSpace_pullback_snd_of_left

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.instance
      (Term.attrKind [])
      "instance"
      []
      [(Command.declId `SheafedSpace_pullback_fst_of_right [])]
      (Command.declSig
       []
       (Term.typeSpec
        ":"
        (Term.app
         `SheafedSpaceCat.IsOpenImmersion
         [(Term.typeAscription
           "("
           `pullback.fst
           ":"
           [(Combinatorics.Quiver.Basic.«term_⟶_»
             (Term.app `pullback [`g `f])
             " ⟶ "
             (Term.hole "_"))]
           ")")])))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.delta "delta" [`pullback.fst] [])
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              []
              [(Term.typeSpec
                ":"
                («term_=_»
                 (Term.hole "_")
                 "="
                 (Term.app `limit.π [(Term.app `cospan [`g `f]) `left])))]
              ":="
              (Term.app
               `preserves_limits_iso_hom_π
               [(AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget
                 "forget")
                (Term.app `cospan [`g `f])
                `left]))))
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq "[" [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `this)] "]")
            [])
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              []
              []
              ":="
              (Term.app
               `has_limit.iso_of_nat_iso_hom_π
               [(Term.app
                 (Term.explicitUniv `diagramIsoCospan ".{" [`v] "}")
                 [(CategoryTheory.Functor.CategoryTheory.Functor.Basic.«term_⋙_»
                   (Term.app `cospan [`g `f])
                   " ⋙ "
                   (AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget
                    "forget"))])
                `left]))))
           []
           (Tactic.tacticErw__
            "erw"
            (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `category.comp_id)] "]")
            [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq "[" [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `this)] "]")
            [])
           []
           (Tactic.dsimp "dsimp" [] [] [] [] [])
           []
           (Tactic.tacticInfer_instance "infer_instance")])))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.delta "delta" [`pullback.fst] [])
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             []
             [(Term.typeSpec
               ":"
               («term_=_»
                (Term.hole "_")
                "="
                (Term.app `limit.π [(Term.app `cospan [`g `f]) `left])))]
             ":="
             (Term.app
              `preserves_limits_iso_hom_π
              [(AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget
                "forget")
               (Term.app `cospan [`g `f])
               `left]))))
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `this)] "]")
           [])
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             []
             []
             ":="
             (Term.app
              `has_limit.iso_of_nat_iso_hom_π
              [(Term.app
                (Term.explicitUniv `diagramIsoCospan ".{" [`v] "}")
                [(CategoryTheory.Functor.CategoryTheory.Functor.Basic.«term_⋙_»
                  (Term.app `cospan [`g `f])
                  " ⋙ "
                  (AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget
                   "forget"))])
               `left]))))
          []
          (Tactic.tacticErw__
           "erw"
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `category.comp_id)] "]")
           [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `this)] "]")
           [])
          []
          (Tactic.dsimp "dsimp" [] [] [] [] [])
          []
          (Tactic.tacticInfer_instance "infer_instance")])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticInfer_instance "infer_instance")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.dsimp "dsimp" [] [] [] [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `this)] "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `this
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticErw__
       "erw"
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `category.comp_id)] "]")
       [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `this
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `category.comp_id
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         []
         []
         ":="
         (Term.app
          `has_limit.iso_of_nat_iso_hom_π
          [(Term.app
            (Term.explicitUniv `diagramIsoCospan ".{" [`v] "}")
            [(CategoryTheory.Functor.CategoryTheory.Functor.Basic.«term_⋙_»
              (Term.app `cospan [`g `f])
              " ⋙ "
              (AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget
               "forget"))])
           `left]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `has_limit.iso_of_nat_iso_hom_π
       [(Term.app
         (Term.explicitUniv `diagramIsoCospan ".{" [`v] "}")
         [(CategoryTheory.Functor.CategoryTheory.Functor.Basic.«term_⋙_»
           (Term.app `cospan [`g `f])
           " ⋙ "
           (AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget
            "forget"))])
        `left])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `left
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       (Term.explicitUniv `diagramIsoCospan ".{" [`v] "}")
       [(CategoryTheory.Functor.CategoryTheory.Functor.Basic.«term_⋙_»
         (Term.app `cospan [`g `f])
         " ⋙ "
         (AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget
          "forget"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.Functor.CategoryTheory.Functor.Basic.«term_⋙_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.Functor.CategoryTheory.Functor.Basic.«term_⋙_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (CategoryTheory.Functor.CategoryTheory.Functor.Basic.«term_⋙_»
       (Term.app `cospan [`g `f])
       " ⋙ "
       (AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget
        "forget"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget
       "forget")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget', expected 'AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget._@.AlgebraicGeometry.OpenImmersion._hyg.362'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.letPatDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveEqnsDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
instance
  SheafedSpace_pullback_fst_of_right
  : SheafedSpaceCat.IsOpenImmersion ( pullback.fst : pullback g f ⟶ _ )
  :=
    by
      delta pullback.fst
        have : _ = limit.π cospan g f left := preserves_limits_iso_hom_π forget cospan g f left
        rw [ ← this ]
        have := has_limit.iso_of_nat_iso_hom_π diagramIsoCospan .{ v } cospan g f ⋙ forget left
        erw [ category.comp_id ] at this
        rw [ ← this ]
        dsimp
        infer_instance
#align
  algebraic_geometry.SheafedSpace.is_open_immersion.SheafedSpace_pullback_fst_of_right AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.SheafedSpace_pullback_fst_of_right

instance SheafedSpace_pullback_to_base_is_open_immersion [SheafedSpaceCat.IsOpenImmersion g] :
    SheafedSpaceCat.IsOpenImmersion (limit.π (cospan f g) one : pullback f g ⟶ Z) :=
  by
  rw [← limit.w (cospan f g) hom.inl, cospan_map_inl]
  infer_instance
#align
  algebraic_geometry.SheafedSpace.is_open_immersion.SheafedSpace_pullback_to_base_is_open_immersion AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.SheafedSpace_pullback_to_base_is_open_immersion

end Pullback

section OfStalkIso

variable [HasLimits C] [HasColimits C] [ConcreteCategory.{v} C]

variable [ReflectsIsomorphisms (forget C)] [PreservesLimits (forget C)]

variable [PreservesFilteredColimits (forget C)]

/-- Suppose `X Y : SheafedSpace C`, where `C` is a concrete category,
whose forgetful functor reflects isomorphisms, preserves limits and filtered colimits.
Then a morphism `X ⟶ Y` that is a topological open embedding
is an open immersion iff every stalk map is an iso.
-/
theorem of_stalk_iso {X Y : SheafedSpaceCat C} (f : X ⟶ Y) (hf : OpenEmbedding f.base)
    [H : ∀ x : X, IsIso (PresheafedSpaceCat.stalkMap f x)] : SheafedSpaceCat.IsOpenImmersion f :=
  { base_open := hf
    c_iso := fun U =>
      by
      apply (config := { instances := false })
        TopCat.Presheaf.app_is_iso_of_stalk_functor_map_iso
          (show Y.sheaf ⟶ (TopCat.Sheaf.pushforward f.base).obj X.sheaf from ⟨f.c⟩)
      rintro ⟨_, y, hy, rfl⟩
      specialize H y
      delta PresheafedSpace.stalk_map at H
      haveI H' :=
        TopCat.Presheaf.stalkPushforward.stalk_pushforward_iso_of_open_embedding C hf X.presheaf y
      have := @is_iso.comp_is_iso _ H (@is_iso.inv_is_iso _ H')
      rw [category.assoc, is_iso.hom_inv_id, category.comp_id] at this
      exact this }
#align
  algebraic_geometry.SheafedSpace.is_open_immersion.of_stalk_iso AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.of_stalk_iso

end OfStalkIso

section Prod

variable [HasLimits C] {ι : Type v} (F : Discrete ι ⥤ SheafedSpaceCat C) [HasColimit F]
  (i : Discrete ι)

theorem sigma_ι_open_embedding : OpenEmbedding (colimit.ι F i).base :=
  by
  rw [← show _ = (colimit.ι F i).base from ι_preserves_colimits_iso_inv (SheafedSpace.forget C) F i]
  have : _ = _ ≫ colimit.ι (discrete.functor ((F ⋙ SheafedSpace.forget C).obj ∘ discrete.mk)) i :=
    has_colimit.iso_of_nat_iso_ι_hom discrete.nat_iso_functor i
  rw [← iso.eq_comp_inv] at this
  rw [this]
  have : colimit.ι _ _ ≫ _ = _ :=
    TopCat.sigma_iso_sigma_hom_ι.{v, v} ((F ⋙ SheafedSpace.forget C).obj ∘ discrete.mk) i.as
  rw [← iso.eq_comp_inv] at this
  cases i
  rw [this]
  simp_rw [← category.assoc, TopCat.open_embedding_iff_comp_is_iso,
    TopCat.open_embedding_iff_is_iso_comp]
  dsimp
  exact open_embedding_sigma_mk
#align
  algebraic_geometry.SheafedSpace.is_open_immersion.sigma_ι_open_embedding AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.sigma_ι_open_embedding

theorem image_preimage_is_empty (j : Discrete ι) (h : i ≠ j) (U : Opens (F.obj i)) :
    (Opens.map (colimit.ι (F ⋙ SheafedSpace.forget_to_PresheafedSpace) j).base).obj
        ((Opens.map (preservesColimitIso SheafedSpaceCat.forgetToPresheafedSpace F).inv.base).obj
          ((sigma_ι_open_embedding F i).IsOpenMap.Functor.obj U)) =
      ∅ :=
  by
  ext
  apply iff_false_intro
  rintro ⟨y, hy, eq⟩
  replace eq :=
    concrete_category.congr_arg
      (preserves_colimit_iso (SheafedSpace.forget C) F ≪≫
          has_colimit.iso_of_nat_iso discrete.nat_iso_functor ≪≫ TopCat.sigmaIsoSigma.{v} _).Hom
      Eq
  simp_rw [CategoryTheory.Iso.trans_hom, ← TopCat.comp_app, ← PresheafedSpace.comp_base] at eq
  rw [ι_preserves_colimits_iso_inv] at eq
  change
    ((SheafedSpace.forget C).map (colimit.ι F i) ≫ _) y =
      ((SheafedSpace.forget C).map (colimit.ι F j) ≫ _) x at
    eq
  cases i; cases j
  rw [ι_preserves_colimits_iso_hom_assoc, ι_preserves_colimits_iso_hom_assoc,
    has_colimit.iso_of_nat_iso_ι_hom_assoc, has_colimit.iso_of_nat_iso_ι_hom_assoc,
    TopCat.sigma_iso_sigma_hom_ι.{v}, TopCat.sigma_iso_sigma_hom_ι.{v}] at eq
  exact h (congr_arg discrete.mk (congr_arg Sigma.fst Eq))
#align
  algebraic_geometry.SheafedSpace.is_open_immersion.image_preimage_is_empty AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.image_preimage_is_empty

instance sigma_ι_is_open_immersion [HasStrictTerminalObjects C] :
    SheafedSpaceCat.IsOpenImmersion (colimit.ι F i)
    where
  base_open := sigma_ι_open_embedding F i
  c_iso U :=
    by
    have e : colimit.ι F i = _ :=
      (ι_preserves_colimits_iso_inv SheafedSpace.forget_to_PresheafedSpace F i).symm
    have H :
      OpenEmbedding
        (colimit.ι (F ⋙ SheafedSpace.forget_to_PresheafedSpace) i ≫
            (preserves_colimit_iso SheafedSpace.forget_to_PresheafedSpace F).inv).base :=
      e ▸ sigma_ι_open_embedding F i
    suffices
      is_iso
        ((colimit.ι (F ⋙ SheafedSpace.forget_to_PresheafedSpace) i ≫
                (preserves_colimit_iso SheafedSpace.forget_to_PresheafedSpace F).inv).c.app
          (op (H.is_open_map.functor.obj U)))
      by convert this
    rw [PresheafedSpace.comp_c_app, ←
      PresheafedSpace.colimit_presheaf_obj_iso_componentwise_limit_hom_π]
    rsuffices :
      is_iso
        (limit.π
          (PresheafedSpace.componentwise_diagram (F ⋙ SheafedSpace.forget_to_PresheafedSpace)
            ((opens.map
                  (preserves_colimit_iso SheafedSpace.forget_to_PresheafedSpace F).inv.base).obj
              (unop <| op <| H.is_open_map.functor.obj U)))
          (op i))
    · infer_instance
    apply limit_π_is_iso_of_is_strict_terminal
    intro j hj
    induction j using Opposite.rec
    dsimp
    convert (F.obj j).Sheaf.isTerminalOfEmpty
    convert image_preimage_is_empty F i j (fun h => hj (congr_arg op h.symm)) U
    exact (congr_arg PresheafedSpace.hom.base e).symm
#align
  algebraic_geometry.SheafedSpace.is_open_immersion.sigma_ι_is_open_immersion AlgebraicGeometry.SheafedSpaceCat.IsOpenImmersion.sigma_ι_is_open_immersion

end Prod

end SheafedSpaceCat.IsOpenImmersion

namespace LocallyRingedSpaceCat.IsOpenImmersion

section Pullback

variable {X Y Z : LocallyRingedSpaceCat.{u}} (f : X ⟶ Z) (g : Y ⟶ Z)

variable [H : LocallyRingedSpaceCat.IsOpenImmersion f]

instance (priority := 100) of_is_iso [IsIso g] : LocallyRingedSpaceCat.IsOpenImmersion g :=
  @PresheafedSpaceCat.IsOpenImmersion.ofIsIso _ g.1
    ⟨⟨(inv g).1, by
        erw [← LocallyRingedSpace.comp_val]
        rw [is_iso.hom_inv_id]
        erw [← LocallyRingedSpace.comp_val]
        rw [is_iso.inv_hom_id]
        constructor <;> simpa⟩⟩
#align
  algebraic_geometry.LocallyRingedSpace.is_open_immersion.of_is_iso AlgebraicGeometry.LocallyRingedSpaceCat.IsOpenImmersion.of_is_iso

include H

instance comp (g : Z ⟶ Y) [LocallyRingedSpaceCat.IsOpenImmersion g] :
    LocallyRingedSpaceCat.IsOpenImmersion (f ≫ g) :=
  PresheafedSpaceCat.IsOpenImmersion.comp f.1 g.1
#align
  algebraic_geometry.LocallyRingedSpace.is_open_immersion.comp AlgebraicGeometry.LocallyRingedSpaceCat.IsOpenImmersion.comp

instance mono : Mono f :=
  LocallyRingedSpaceCat.forgetToSheafedSpace.mono_of_mono_map (show Mono f.1 by infer_instance)
#align
  algebraic_geometry.LocallyRingedSpace.is_open_immersion.mono AlgebraicGeometry.LocallyRingedSpaceCat.IsOpenImmersion.mono

instance : SheafedSpaceCat.IsOpenImmersion (LocallyRingedSpaceCat.forgetToSheafedSpace.map f) :=
  H

/-- An explicit pullback cone over `cospan f g` if `f` is an open immersion. -/
def pullbackConeOfLeft : PullbackCone f g :=
  by
  refine'
    pullback_cone.mk _
      (Y.of_restrict (TopCat.snd_open_embedding_of_left_open_embedding H.base_open g.1.base)) _
  · use PresheafedSpace.is_open_immersion.pullback_cone_of_left_fst f.1 g.1
    intro x
    have :=
      PresheafedSpace.stalk_map.congr_hom _ _
        (PresheafedSpace.is_open_immersion.pullback_cone_of_left_condition f.1 g.1) x
    rw [PresheafedSpace.stalk_map.comp, PresheafedSpace.stalk_map.comp] at this
    rw [← is_iso.eq_inv_comp] at this
    rw [this]
    infer_instance
  ·
    exact
      LocallyRingedSpace.hom.ext _ _
        (PresheafedSpace.is_open_immersion.pullback_cone_of_left_condition _ _)
#align
  algebraic_geometry.LocallyRingedSpace.is_open_immersion.pullback_cone_of_left AlgebraicGeometry.LocallyRingedSpaceCat.IsOpenImmersion.pullbackConeOfLeft

instance : LocallyRingedSpaceCat.IsOpenImmersion (pullbackConeOfLeft f g).snd :=
  show PresheafedSpaceCat.IsOpenImmersion (Y.toPresheafedSpace.of_restrict _) by infer_instance

/-- The constructed `pullback_cone_of_left` is indeed limiting. -/
def pullbackConeOfLeftIsLimit : IsLimit (pullbackConeOfLeft f g) :=
  (PullbackCone.isLimitAux' _) fun s =>
    by
    use
      PresheafedSpace.is_open_immersion.pullback_cone_of_left_lift f.1 g.1
        (pullback_cone.mk s.fst.1 s.snd.1 (congr_arg LocallyRingedSpace.hom.val s.condition))
    · intro x
      have :=
        PresheafedSpace.stalk_map.congr_hom _ _
          (PresheafedSpace.is_open_immersion.pullback_cone_of_left_lift_snd f.1 g.1
            (pullback_cone.mk s.fst.1 s.snd.1 (congr_arg LocallyRingedSpace.hom.val s.condition)))
          x
      change _ = _ ≫ PresheafedSpace.stalk_map s.snd.1 x at this
      rw [PresheafedSpace.stalk_map.comp, ← is_iso.eq_inv_comp] at this
      rw [this]
      infer_instance
    constructor
    ·
      exact
        LocallyRingedSpace.hom.ext _ _
          (PresheafedSpace.is_open_immersion.pullback_cone_of_left_lift_fst f.1 g.1 _)
    constructor
    ·
      exact
        LocallyRingedSpace.hom.ext _ _
          (PresheafedSpace.is_open_immersion.pullback_cone_of_left_lift_snd f.1 g.1 _)
    intro m h₁ h₂
    rw [← cancel_mono (pullback_cone_of_left f g).snd]
    exact
      h₂.trans
        (LocallyRingedSpace.hom.ext _ _
          (PresheafedSpace.is_open_immersion.pullback_cone_of_left_lift_snd f.1 g.1
              (pullback_cone.mk s.fst.1 s.snd.1
                (congr_arg LocallyRingedSpace.hom.val s.condition))).symm)
#align
  algebraic_geometry.LocallyRingedSpace.is_open_immersion.pullback_cone_of_left_is_limit AlgebraicGeometry.LocallyRingedSpaceCat.IsOpenImmersion.pullbackConeOfLeftIsLimit

instance has_pullback_of_left : HasPullback f g :=
  ⟨⟨⟨_, pullbackConeOfLeftIsLimit f g⟩⟩⟩
#align
  algebraic_geometry.LocallyRingedSpace.is_open_immersion.has_pullback_of_left AlgebraicGeometry.LocallyRingedSpaceCat.IsOpenImmersion.has_pullback_of_left

instance has_pullback_of_right : HasPullback g f :=
  has_pullback_symmetry f g
#align
  algebraic_geometry.LocallyRingedSpace.is_open_immersion.has_pullback_of_right AlgebraicGeometry.LocallyRingedSpaceCat.IsOpenImmersion.has_pullback_of_right

/-- Open immersions are stable under base-change. -/
instance pullback_snd_of_left :
    LocallyRingedSpaceCat.IsOpenImmersion (pullback.snd : pullback f g ⟶ _) :=
  by
  delta pullback.snd
  rw [← limit.iso_limit_cone_hom_π ⟨_, pullback_cone_of_left_is_limit f g⟩ walking_cospan.right]
  infer_instance
#align
  algebraic_geometry.LocallyRingedSpace.is_open_immersion.pullback_snd_of_left AlgebraicGeometry.LocallyRingedSpaceCat.IsOpenImmersion.pullback_snd_of_left

/-- Open immersions are stable under base-change. -/
instance pullback_fst_of_right :
    LocallyRingedSpaceCat.IsOpenImmersion (pullback.fst : pullback g f ⟶ _) :=
  by
  rw [← pullback_symmetry_hom_comp_snd]
  infer_instance
#align
  algebraic_geometry.LocallyRingedSpace.is_open_immersion.pullback_fst_of_right AlgebraicGeometry.LocallyRingedSpaceCat.IsOpenImmersion.pullback_fst_of_right

instance pullback_to_base_is_open_immersion [LocallyRingedSpaceCat.IsOpenImmersion g] :
    LocallyRingedSpaceCat.IsOpenImmersion (limit.π (cospan f g) WalkingCospan.one) :=
  by
  rw [← limit.w (cospan f g) walking_cospan.hom.inl, cospan_map_inl]
  infer_instance
#align
  algebraic_geometry.LocallyRingedSpace.is_open_immersion.pullback_to_base_is_open_immersion AlgebraicGeometry.LocallyRingedSpaceCat.IsOpenImmersion.pullback_to_base_is_open_immersion

instance forgetPreservesPullbackOfLeft :
    PreservesLimit (cospan f g) LocallyRingedSpaceCat.forgetToSheafedSpace :=
  preservesLimitOfPreservesLimitCone (pullbackConeOfLeftIsLimit f g)
    (by
      apply (is_limit_map_cone_pullback_cone_equiv _ _).symm.toFun
      apply is_limit_of_is_limit_pullback_cone_map SheafedSpace.forget_to_PresheafedSpace
      exact PresheafedSpace.is_open_immersion.pullback_cone_of_left_is_limit f.1 g.1)
#align
  algebraic_geometry.LocallyRingedSpace.is_open_immersion.forget_preserves_pullback_of_left AlgebraicGeometry.LocallyRingedSpaceCat.IsOpenImmersion.forgetPreservesPullbackOfLeft

instance forgetToPresheafedSpacePreservesPullbackOfLeft :
    PreservesLimit (cospan f g)
      (LocallyRingedSpace.forget_to_SheafedSpace ⋙ SheafedSpace.forget_to_PresheafedSpace) :=
  preservesLimitOfPreservesLimitCone (pullbackConeOfLeftIsLimit f g)
    (by
      apply (is_limit_map_cone_pullback_cone_equiv _ _).symm.toFun
      exact PresheafedSpace.is_open_immersion.pullback_cone_of_left_is_limit f.1 g.1)
#align
  algebraic_geometry.LocallyRingedSpace.is_open_immersion.forget_to_PresheafedSpace_preserves_pullback_of_left AlgebraicGeometry.LocallyRingedSpaceCat.IsOpenImmersion.forgetToPresheafedSpacePreservesPullbackOfLeft

instance forgetToPresheafedSpacePreservesOpenImmersion :
    PresheafedSpaceCat.IsOpenImmersion
      ((LocallyRingedSpace.forget_to_SheafedSpace ⋙ SheafedSpace.forget_to_PresheafedSpace).map
        f) :=
  H
#align
  algebraic_geometry.LocallyRingedSpace.is_open_immersion.forget_to_PresheafedSpace_preserves_open_immersion AlgebraicGeometry.LocallyRingedSpaceCat.IsOpenImmersion.forgetToPresheafedSpacePreservesOpenImmersion

instance forgetToTopPreservesPullbackOfLeft :
    PreservesLimit (cospan f g)
      (LocallyRingedSpace.forget_to_SheafedSpace ⋙ SheafedSpaceCat.forget _) :=
  by
  change
    preserves_limit _
      ((LocallyRingedSpace.forget_to_SheafedSpace ⋙ SheafedSpace.forget_to_PresheafedSpace) ⋙
        PresheafedSpace.forget _)
  apply (config := { instances := false }) limits.comp_preserves_limit
  infer_instance
  apply preserves_limit_of_iso_diagram _ (diagramIsoCospan.{u} _).symm
  dsimp [SheafedSpace.forget_to_PresheafedSpace]
  infer_instance
#align
  algebraic_geometry.LocallyRingedSpace.is_open_immersion.forget_to_Top_preserves_pullback_of_left AlgebraicGeometry.LocallyRingedSpaceCat.IsOpenImmersion.forgetToTopPreservesPullbackOfLeft

instance forgetReflectsPullbackOfLeft :
    ReflectsLimit (cospan f g) LocallyRingedSpaceCat.forgetToSheafedSpace :=
  reflectsLimitOfReflectsIsomorphisms _ _
#align
  algebraic_geometry.LocallyRingedSpace.is_open_immersion.forget_reflects_pullback_of_left AlgebraicGeometry.LocallyRingedSpaceCat.IsOpenImmersion.forgetReflectsPullbackOfLeft

instance forgetPreservesPullbackOfRight :
    PreservesLimit (cospan g f) LocallyRingedSpaceCat.forgetToSheafedSpace :=
  preservesPullbackSymmetry _ _ _
#align
  algebraic_geometry.LocallyRingedSpace.is_open_immersion.forget_preserves_pullback_of_right AlgebraicGeometry.LocallyRingedSpaceCat.IsOpenImmersion.forgetPreservesPullbackOfRight

instance forgetToPresheafedSpacePreservesPullbackOfRight :
    PreservesLimit (cospan g f)
      (LocallyRingedSpace.forget_to_SheafedSpace ⋙ SheafedSpace.forget_to_PresheafedSpace) :=
  preservesPullbackSymmetry _ _ _
#align
  algebraic_geometry.LocallyRingedSpace.is_open_immersion.forget_to_PresheafedSpace_preserves_pullback_of_right AlgebraicGeometry.LocallyRingedSpaceCat.IsOpenImmersion.forgetToPresheafedSpacePreservesPullbackOfRight

instance forgetReflectsPullbackOfRight :
    ReflectsLimit (cospan g f) LocallyRingedSpaceCat.forgetToSheafedSpace :=
  reflectsLimitOfReflectsIsomorphisms _ _
#align
  algebraic_geometry.LocallyRingedSpace.is_open_immersion.forget_reflects_pullback_of_right AlgebraicGeometry.LocallyRingedSpaceCat.IsOpenImmersion.forgetReflectsPullbackOfRight

instance forgetToPresheafedSpaceReflectsPullbackOfLeft :
    ReflectsLimit (cospan f g)
      (LocallyRingedSpace.forget_to_SheafedSpace ⋙ SheafedSpace.forget_to_PresheafedSpace) :=
  reflectsLimitOfReflectsIsomorphisms _ _
#align
  algebraic_geometry.LocallyRingedSpace.is_open_immersion.forget_to_PresheafedSpace_reflects_pullback_of_left AlgebraicGeometry.LocallyRingedSpaceCat.IsOpenImmersion.forgetToPresheafedSpaceReflectsPullbackOfLeft

instance forgetToPresheafedSpaceReflectsPullbackOfRight :
    ReflectsLimit (cospan g f)
      (LocallyRingedSpace.forget_to_SheafedSpace ⋙ SheafedSpace.forget_to_PresheafedSpace) :=
  reflectsLimitOfReflectsIsomorphisms _ _
#align
  algebraic_geometry.LocallyRingedSpace.is_open_immersion.forget_to_PresheafedSpace_reflects_pullback_of_right AlgebraicGeometry.LocallyRingedSpaceCat.IsOpenImmersion.forgetToPresheafedSpaceReflectsPullbackOfRight

theorem pullback_snd_is_iso_of_range_subset (H' : Set.range g.1.base ⊆ Set.range f.1.base) :
    IsIso (pullback.snd : pullback f g ⟶ _) :=
  by
  apply (config := { instances := false })
    reflects_isomorphisms.reflects LocallyRingedSpace.forget_to_SheafedSpace
  apply (config := { instances := false })
    reflects_isomorphisms.reflects SheafedSpace.forget_to_PresheafedSpace
  erw [←
    preserves_pullback.iso_hom_snd
      (LocallyRingedSpace.forget_to_SheafedSpace ⋙ SheafedSpace.forget_to_PresheafedSpace) f g]
  haveI := PresheafedSpace.is_open_immersion.pullback_snd_is_iso_of_range_subset _ _ H'
  infer_instance
  infer_instance
#align
  algebraic_geometry.LocallyRingedSpace.is_open_immersion.pullback_snd_is_iso_of_range_subset AlgebraicGeometry.LocallyRingedSpaceCat.IsOpenImmersion.pullback_snd_is_iso_of_range_subset

/-- The universal property of open immersions:
For an open immersion `f : X ⟶ Z`, given any morphism of schemes `g : Y ⟶ Z` whose topological
image is contained in the image of `f`, we can lift this morphism to a unique `Y ⟶ X` that
commutes with these maps.
-/
def lift (H' : Set.range g.1.base ⊆ Set.range f.1.base) : Y ⟶ X :=
  haveI := pullback_snd_is_iso_of_range_subset f g H'
  inv (pullback.snd : pullback f g ⟶ _) ≫ pullback.fst
#align
  algebraic_geometry.LocallyRingedSpace.is_open_immersion.lift AlgebraicGeometry.LocallyRingedSpaceCat.IsOpenImmersion.lift

@[simp, reassoc.1]
theorem lift_fac (H' : Set.range g.1.base ⊆ Set.range f.1.base) : lift f g H' ≫ f = g :=
  by
  erw [category.assoc]
  rw [is_iso.inv_comp_eq]
  exact pullback.condition
#align
  algebraic_geometry.LocallyRingedSpace.is_open_immersion.lift_fac AlgebraicGeometry.LocallyRingedSpaceCat.IsOpenImmersion.lift_fac

theorem lift_uniq (H' : Set.range g.1.base ⊆ Set.range f.1.base) (l : Y ⟶ X) (hl : l ≫ f = g) :
    l = lift f g H' := by rw [← cancel_mono f, hl, lift_fac]
#align
  algebraic_geometry.LocallyRingedSpace.is_open_immersion.lift_uniq AlgebraicGeometry.LocallyRingedSpaceCat.IsOpenImmersion.lift_uniq

theorem lift_range (H' : Set.range g.1.base ⊆ Set.range f.1.base) :
    Set.range (lift f g H').1.base = f.1.base ⁻¹' Set.range g.1.base :=
  by
  haveI := pullback_snd_is_iso_of_range_subset f g H'
  dsimp only [lift]
  have : _ = (pullback.fst : pullback f g ⟶ _).val.base :=
    preserves_pullback.iso_hom_fst
      (LocallyRingedSpace.forget_to_SheafedSpace ⋙ SheafedSpace.forget _) f g
  rw [LocallyRingedSpace.comp_val, SheafedSpace.comp_base, ← this, ← category.assoc, coe_comp]
  rw [Set.range_comp, set.range_iff_surjective.mpr, Set.image_univ, TopCat.pullback_fst_range]
  ext
  constructor
  · rintro ⟨y, eq⟩
    exact ⟨y, Eq.symm⟩
  · rintro ⟨y, eq⟩
    exact ⟨y, Eq.symm⟩
  · rw [← TopCat.epi_iff_surjective]
    rw [show (inv (pullback.snd : pullback f g ⟶ _)).val.base = _ from
        (LocallyRingedSpace.forget_to_SheafedSpace ⋙ SheafedSpace.forget _).map_inv _]
    infer_instance
#align
  algebraic_geometry.LocallyRingedSpace.is_open_immersion.lift_range AlgebraicGeometry.LocallyRingedSpaceCat.IsOpenImmersion.lift_range

end Pullback

/-- An open immersion is isomorphic to the induced open subscheme on its image. -/
def isoRestrict {X Y : LocallyRingedSpaceCat} {f : X ⟶ Y}
    (H : LocallyRingedSpaceCat.IsOpenImmersion f) : X ≅ Y.restrict H.base_open :=
  by
  apply LocallyRingedSpace.iso_of_SheafedSpace_iso
  refine' SheafedSpace.forget_to_PresheafedSpace.preimage_iso _
  exact H.iso_restrict
#align
  algebraic_geometry.LocallyRingedSpace.is_open_immersion.iso_restrict AlgebraicGeometry.LocallyRingedSpaceCat.IsOpenImmersion.isoRestrict

/-- To show that a locally ringed space is a scheme, it suffices to show that it has a jointly
surjective family of open immersions from affine schemes. -/
protected def scheme (X : LocallyRingedSpaceCat)
    (h :
      ∀ x : X,
        ∃ (R : CommRingCat)(f : SpecCat.toLocallyRingedSpace.obj (op R) ⟶ X),
          (x ∈ Set.range f.1.base : _) ∧ LocallyRingedSpaceCat.IsOpenImmersion f) :
    SchemeCat where
  toLocallyRingedSpace := X
  local_affine := by
    intro x
    obtain ⟨R, f, h₁, h₂⟩ := h x
    refine' ⟨⟨⟨_, h₂.base_open.open_range⟩, h₁⟩, R, ⟨_⟩⟩
    apply LocallyRingedSpace.iso_of_SheafedSpace_iso
    refine' SheafedSpace.forget_to_PresheafedSpace.preimage_iso _
    skip
    apply PresheafedSpace.is_open_immersion.iso_of_range_eq (PresheafedSpace.of_restrict _ _) f.1
    · exact Subtype.range_coe_subtype
    · infer_instance
#align
  algebraic_geometry.LocallyRingedSpace.is_open_immersion.Scheme AlgebraicGeometry.LocallyRingedSpaceCat.IsOpenImmersion.scheme

end LocallyRingedSpaceCat.IsOpenImmersion

theorem IsOpenImmersion.open_range {X Y : SchemeCat} (f : X ⟶ Y) [H : IsOpenImmersion f] :
    IsOpen (Set.range f.1.base) :=
  H.base_open.open_range
#align algebraic_geometry.is_open_immersion.open_range AlgebraicGeometry.IsOpenImmersion.open_range

section OpenCover

namespace SchemeCat

-- TODO: provide API to and from a presieve.
/-- An open cover of `X` consists of a family of open immersions into `X`,
and for each `x : X` an open immersion (indexed by `f x`) that covers `x`.

This is merely a coverage in the Zariski pretopology, and it would be optimal
if we could reuse the existing API about pretopologies, However, the definitions of sieves and
grothendieck topologies uses `Prop`s, so that the actual open sets and immersions are hard to
obtain. Also, since such a coverage in the pretopology usually contains a proper class of
immersions, it is quite hard to glue them, reason about finite covers, etc.
-/
structure OpenCover (X : SchemeCat.{u}) where
  J : Type v
  obj : ∀ j : J, SchemeCat
  map : ∀ j : J, obj j ⟶ X
  f : X.carrier → J
  Covers : ∀ x, x ∈ Set.range (map (f x)).1.base
  IsOpen : ∀ x, IsOpenImmersion (map x) := by infer_instance
#align algebraic_geometry.Scheme.open_cover AlgebraicGeometry.SchemeCat.OpenCover

attribute [instance] open_cover.is_open

variable {X Y Z : SchemeCat.{u}} (𝒰 : OpenCover X) (f : X ⟶ Z) (g : Y ⟶ Z)

variable [∀ x, HasPullback (𝒰.map x ≫ f) g]

/-- The affine cover of a scheme. -/
def affineCover (X : SchemeCat) : OpenCover X
    where
  J := X.carrier
  obj x := spec.obj <| Opposite.op (X.local_affine x).some_spec.some
  map x :=
    ((X.local_affine x).some_spec.some_spec.some.inv ≫ X.toLocallyRingedSpace.of_restrict _ : _)
  f x := x
  IsOpen x :=
    by
    apply (config := { instances := false }) PresheafedSpace.is_open_immersion.comp
    infer_instance
    apply PresheafedSpace.is_open_immersion.of_restrict
  Covers := by
    intro x
    erw [coe_comp]
    rw [Set.range_comp, set.range_iff_surjective.mpr, Set.image_univ]
    erw [Subtype.range_coe_subtype]
    exact (X.local_affine x).some.2
    rw [← TopCat.epi_iff_surjective]
    change epi ((SheafedSpace.forget _).map (LocallyRingedSpace.forget_to_SheafedSpace.map _))
    infer_instance
#align algebraic_geometry.Scheme.affine_cover AlgebraicGeometry.SchemeCat.affineCover

instance : Inhabited X.OpenCover :=
  ⟨X.affineCover⟩

/-- Given an open cover `{ Uᵢ }` of `X`, and for each `Uᵢ` an open cover, we may combine these
open covers to form an open cover of `X`.  -/
@[simps J obj map]
def OpenCover.bind (f : ∀ x : 𝒰.J, OpenCover (𝒰.obj x)) : OpenCover X
    where
  J := Σi : 𝒰.J, (f i).J
  obj x := (f x.1).obj x.2
  map x := (f x.1).map x.2 ≫ 𝒰.map x.1
  f x := ⟨_, (f _).f (𝒰.Covers x).some⟩
  Covers x := by
    let y := (𝒰.covers x).some
    have hy : (𝒰.map (𝒰.f x)).val.base y = x := (𝒰.covers x).some_spec
    rcases(f (𝒰.f x)).Covers y with ⟨z, hz⟩
    change x ∈ Set.range ((f (𝒰.f x)).map ((f (𝒰.f x)).f y) ≫ 𝒰.map (𝒰.f x)).1.base
    use z
    erw [comp_apply]
    rw [hz, hy]
#align algebraic_geometry.Scheme.open_cover.bind AlgebraicGeometry.SchemeCat.OpenCover.bind

/-- An isomorphism `X ⟶ Y` is an open cover of `Y`. -/
@[simps J obj map]
def openCoverOfIsIso {X Y : SchemeCat.{u}} (f : X ⟶ Y) [IsIso f] : OpenCover Y
    where
  J := PUnit.{v + 1}
  obj _ := X
  map _ := f
  f _ := PUnit.unit
  Covers x := by
    rw [set.range_iff_surjective.mpr]
    · trivial
    rw [← TopCat.epi_iff_surjective]
    infer_instance
#align algebraic_geometry.Scheme.open_cover_of_is_iso AlgebraicGeometry.SchemeCat.openCoverOfIsIso

/-- We construct an open cover from another, by providing the needed fields and showing that the
provided fields are isomorphic with the original open cover. -/
@[simps J obj map]
def OpenCover.copy {X : SchemeCat} (𝒰 : OpenCover X) (J : Type _) (obj : J → SchemeCat)
    (map : ∀ i, obj i ⟶ X) (e₁ : J ≃ 𝒰.J) (e₂ : ∀ i, obj i ≅ 𝒰.obj (e₁ i))
    (e₂ : ∀ i, map i = (e₂ i).Hom ≫ 𝒰.map (e₁ i)) : OpenCover X :=
  { J
    obj
    map
    f := fun x => e₁.symm (𝒰.f x)
    Covers := fun x =>
      by
      rw [e₂, Scheme.comp_val_base, coe_comp, Set.range_comp, set.range_iff_surjective.mpr,
        Set.image_univ, e₁.right_inverse_symm]
      · exact 𝒰.covers x
      · rw [← TopCat.epi_iff_surjective]
        infer_instance
    IsOpen := fun i => by
      rw [e₂]
      infer_instance }
#align algebraic_geometry.Scheme.open_cover.copy AlgebraicGeometry.SchemeCat.OpenCover.copy

/-- The pushforward of an open cover along an isomorphism. -/
@[simps J obj map]
def OpenCover.pushforwardIso {X Y : SchemeCat} (𝒰 : OpenCover X) (f : X ⟶ Y) [IsIso f] :
    OpenCover Y :=
  ((openCoverOfIsIso f).bind fun _ => 𝒰).copy 𝒰.J _ _
    ((Equiv.punitProd _).symm.trans (Equiv.sigmaEquivProd PUnit 𝒰.J).symm) (fun _ => Iso.refl _)
    fun _ => (Category.id_comp _).symm
#align
  algebraic_geometry.Scheme.open_cover.pushforward_iso AlgebraicGeometry.SchemeCat.OpenCover.pushforwardIso

/-- Adding an open immersion into an open cover gives another open cover. -/
@[simps]
def OpenCover.add {X : SchemeCat} (𝒰 : X.OpenCover) {Y : SchemeCat} (f : Y ⟶ X)
    [IsOpenImmersion f] : X.OpenCover where
  J := Option 𝒰.J
  obj i := Option.rec Y 𝒰.obj i
  map i := Option.rec f 𝒰.map i
  f x := some (𝒰.f x)
  Covers := 𝒰.Covers
  IsOpen := by rintro (_ | _) <;> dsimp <;> infer_instance
#align algebraic_geometry.Scheme.open_cover.add AlgebraicGeometry.SchemeCat.OpenCover.add

-- Related result : `open_cover.pullback_cover`, where we pullback an open cover on `X` along a
-- morphism `W ⟶ X`. This is provided at the end of the file since it needs some more results
-- about open immersion (which in turn needs the open cover API).
attribute [local reducible] CommRingCat.of CommRingCat.ofHom

instance val_base_is_iso {X Y : SchemeCat} (f : X ⟶ Y) [IsIso f] : IsIso f.1.base :=
  SchemeCat.forgetToTop.map_is_iso f
#align algebraic_geometry.Scheme.val_base_is_iso AlgebraicGeometry.SchemeCat.val_base_is_iso

instance basic_open_is_open_immersion {R : CommRingCat} (f : R) :
    AlgebraicGeometry.IsOpenImmersion
      (SchemeCat.spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away f))).op) :=
  by
  apply (config := { instances := false }) SheafedSpace.is_open_immersion.of_stalk_iso
  any_goals infer_instance
  any_goals infer_instance
  exact (PrimeSpectrum.localization_away_open_embedding (Localization.Away f) f : _)
  intro x
  exact Spec_map_localization_is_iso R (Submonoid.powers f) x
#align
  algebraic_geometry.Scheme.basic_open_is_open_immersion AlgebraicGeometry.SchemeCat.basic_open_is_open_immersion

/-- The basic open sets form an affine open cover of `Spec R`. -/
def affineBasisCoverOfAffine (R : CommRingCat) : OpenCover (spec.obj (Opposite.op R))
    where
  J := R
  obj r := spec.obj (Opposite.op <| CommRingCat.of <| Localization.Away r)
  map r := spec.map (Quiver.Hom.op (algebraMap R (Localization.Away r) : _))
  f x := 1
  Covers r := by
    rw [set.range_iff_surjective.mpr ((TopCat.epi_iff_surjective _).mp _)]
    · exact trivial
    · infer_instance
  IsOpen x := AlgebraicGeometry.SchemeCat.basic_open_is_open_immersion x
#align
  algebraic_geometry.Scheme.affine_basis_cover_of_affine AlgebraicGeometry.SchemeCat.affineBasisCoverOfAffine

/-- We may bind the basic open sets of an open affine cover to form a affine cover that is also
a basis. -/
def affineBasisCover (X : SchemeCat) : OpenCover X :=
  X.affineCover.bind fun x => affineBasisCoverOfAffine _
#align algebraic_geometry.Scheme.affine_basis_cover AlgebraicGeometry.SchemeCat.affineBasisCover

/-- The coordinate ring of a component in the `affine_basis_cover`. -/
def affineBasisCoverRing (X : SchemeCat) (i : X.affineBasisCover.J) : CommRingCat :=
  CommRingCat.of <| @Localization.Away (X.local_affine i.1).some_spec.some _ i.2
#align
  algebraic_geometry.Scheme.affine_basis_cover_ring AlgebraicGeometry.SchemeCat.affineBasisCoverRing

theorem affine_basis_cover_obj (X : SchemeCat) (i : X.affineBasisCover.J) :
    X.affineBasisCover.obj i = spec.obj (op <| X.affineBasisCoverRing i) :=
  rfl
#align
  algebraic_geometry.Scheme.affine_basis_cover_obj AlgebraicGeometry.SchemeCat.affine_basis_cover_obj

theorem affine_basis_cover_map_range (X : SchemeCat) (x : X.carrier)
    (r : (X.local_affine x).some_spec.some) :
    Set.range (X.affineBasisCover.map ⟨x, r⟩).1.base =
      (X.affineCover.map x).1.base '' (PrimeSpectrum.basicOpen r).1 :=
  by
  erw [coe_comp, Set.range_comp]
  congr
  exact (PrimeSpectrum.localization_away_comap_range (Localization.Away r) r : _)
#align
  algebraic_geometry.Scheme.affine_basis_cover_map_range AlgebraicGeometry.SchemeCat.affine_basis_cover_map_range

theorem affine_basis_cover_is_basis (X : SchemeCat) :
    TopologicalSpace.IsTopologicalBasis
      { x : Set X.carrier |
        ∃ a : X.affineBasisCover.J, x = Set.range (X.affineBasisCover.map a).1.base } :=
  by
  apply TopologicalSpace.is_topological_basis_of_open_of_nhds
  · rintro _ ⟨a, rfl⟩
    exact is_open_immersion.open_range (X.affine_basis_cover.map a)
  · rintro a U haU hU
    rcases X.affine_cover.covers a with ⟨x, e⟩
    let U' := (X.affine_cover.map (X.affine_cover.f a)).1.base ⁻¹' U
    have hxU' : x ∈ U' := by
      rw [← e] at haU
      exact haU
    rcases prime_spectrum.is_basis_basic_opens.exists_subset_of_mem_open hxU'
        ((X.affine_cover.map (X.affine_cover.f a)).1.base.continuous_to_fun.is_open_preimage _
          hU) with
      ⟨_, ⟨_, ⟨s, rfl⟩, rfl⟩, hxV, hVU⟩
    refine' ⟨_, ⟨⟨_, s⟩, rfl⟩, _, _⟩ <;> erw [affine_basis_cover_map_range]
    · exact ⟨x, hxV, e⟩
    · rw [Set.image_subset_iff]
      exact hVU
#align
  algebraic_geometry.Scheme.affine_basis_cover_is_basis AlgebraicGeometry.SchemeCat.affine_basis_cover_is_basis

/-- Every open cover of a quasi-compact scheme can be refined into a finite subcover.
-/
@[simps obj map]
def OpenCover.finiteSubcover {X : SchemeCat} (𝒰 : OpenCover X) [H : CompactSpace X.carrier] :
    OpenCover X :=
  by
  have :=
    @CompactSpace.elim_nhds_subcover _ H (fun x : X.carrier => Set.range (𝒰.map (𝒰.f x)).1.base)
      fun x => (is_open_immersion.open_range (𝒰.map (𝒰.f x))).mem_nhds (𝒰.covers x)
  let t := this.some
  have h : ∀ x : X.carrier, ∃ y : t, x ∈ Set.range (𝒰.map (𝒰.f y)).1.base :=
    by
    intro x
    have h' : x ∈ (⊤ : Set X.carrier) := trivial
    rw [← Classical.choose_spec this, Set.mem_unionᵢ] at h'
    rcases h' with ⟨y, _, ⟨hy, rfl⟩, hy'⟩
    exact ⟨⟨y, hy⟩, hy'⟩
  exact
    { J := t
      obj := fun x => 𝒰.obj (𝒰.f x.1)
      map := fun x => 𝒰.map (𝒰.f x.1)
      f := fun x => (h x).some
      Covers := fun x => (h x).some_spec }
#align
  algebraic_geometry.Scheme.open_cover.finite_subcover AlgebraicGeometry.SchemeCat.OpenCover.finiteSubcover

instance [H : CompactSpace X.carrier] : Fintype 𝒰.finiteSubcover.J :=
  by
  delta open_cover.finite_subcover
  infer_instance

end SchemeCat

end OpenCover

namespace PresheafedSpaceCat.IsOpenImmersion

section ToScheme

variable {X : PresheafedSpaceCat.{u} CommRingCat.{u}} (Y : SchemeCat.{u})

variable (f : X ⟶ Y.toPresheafedSpace) [H : PresheafedSpaceCat.IsOpenImmersion f]

include H

/-- If `X ⟶ Y` is an open immersion, and `Y` is a scheme, then so is `X`. -/
def toScheme : SchemeCat :=
  by
  apply LocallyRingedSpace.is_open_immersion.Scheme (to_LocallyRingedSpace _ f)
  intro x
  obtain ⟨_, ⟨i, rfl⟩, hx, hi⟩ :=
    Y.affine_basis_cover_is_basis.exists_subset_of_mem_open (Set.mem_range_self x)
      H.base_open.open_range
  use Y.affine_basis_cover_ring i
  use LocallyRingedSpace.is_open_immersion.lift (to_LocallyRingedSpace_hom _ f) _ hi
  constructor
  · rw [LocallyRingedSpace.is_open_immersion.lift_range]
    exact hx
  · delta LocallyRingedSpace.is_open_immersion.lift
    infer_instance
#align
  algebraic_geometry.PresheafedSpace.is_open_immersion.to_Scheme AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.toScheme

@[simp]
theorem to_Scheme_to_LocallyRingedSpace :
    (toScheme Y f).toLocallyRingedSpace = toLocallyRingedSpace Y.1 f :=
  rfl
#align
  algebraic_geometry.PresheafedSpace.is_open_immersion.to_Scheme_to_LocallyRingedSpace AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.to_Scheme_to_LocallyRingedSpace

/-- If `X ⟶ Y` is an open immersion of PresheafedSpaces, and `Y` is a Scheme, we can
upgrade it into a morphism of Schemes.
-/
def toSchemeHom : toScheme Y f ⟶ Y :=
  toLocallyRingedSpaceHom _ f
#align
  algebraic_geometry.PresheafedSpace.is_open_immersion.to_Scheme_hom AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.toSchemeHom

@[simp]
theorem to_Scheme_hom_val : (toSchemeHom Y f).val = f :=
  rfl
#align
  algebraic_geometry.PresheafedSpace.is_open_immersion.to_Scheme_hom_val AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.to_Scheme_hom_val

instance to_Scheme_hom_is_open_immersion : IsOpenImmersion (toSchemeHom Y f) :=
  H
#align
  algebraic_geometry.PresheafedSpace.is_open_immersion.to_Scheme_hom_is_open_immersion AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.to_Scheme_hom_is_open_immersion

omit H

theorem Scheme_eq_of_LocallyRingedSpace_eq {X Y : SchemeCat}
    (H : X.toLocallyRingedSpace = Y.toLocallyRingedSpace) : X = Y :=
  by
  cases X
  cases Y
  congr
  exact H
#align
  algebraic_geometry.PresheafedSpace.is_open_immersion.Scheme_eq_of_LocallyRingedSpace_eq AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.Scheme_eq_of_LocallyRingedSpace_eq

theorem Scheme_to_Scheme {X Y : SchemeCat} (f : X ⟶ Y) [IsOpenImmersion f] : toScheme Y f.1 = X :=
  by
  apply Scheme_eq_of_LocallyRingedSpace_eq
  exact LocallyRingedSpace_to_LocallyRingedSpace f
#align
  algebraic_geometry.PresheafedSpace.is_open_immersion.Scheme_to_Scheme AlgebraicGeometry.PresheafedSpaceCat.IsOpenImmersion.Scheme_to_Scheme

end ToScheme

end PresheafedSpaceCat.IsOpenImmersion

/-- The restriction of a Scheme along an open embedding. -/
@[simps]
def SchemeCat.restrict {U : TopCat} (X : SchemeCat) {f : U ⟶ TopCat.of X.carrier}
    (h : OpenEmbedding f) : SchemeCat :=
  { PresheafedSpaceCat.IsOpenImmersion.toScheme X (X.toPresheafedSpace.of_restrict h) with
    toPresheafedSpace := X.toPresheafedSpace.restrict h }
#align algebraic_geometry.Scheme.restrict AlgebraicGeometry.SchemeCat.restrict

/-- The canonical map from the restriction to the supspace. -/
@[simps]
def SchemeCat.ofRestrict {U : TopCat} (X : SchemeCat) {f : U ⟶ TopCat.of X.carrier}
    (h : OpenEmbedding f) : X.restrict h ⟶ X :=
  X.toLocallyRingedSpace.of_restrict h
#align algebraic_geometry.Scheme.of_restrict AlgebraicGeometry.SchemeCat.ofRestrict

instance IsOpenImmersion.of_restrict {U : TopCat} (X : SchemeCat) {f : U ⟶ TopCat.of X.carrier}
    (h : OpenEmbedding f) : IsOpenImmersion (X.of_restrict h) :=
  show PresheafedSpaceCat.IsOpenImmersion (X.toPresheafedSpace.of_restrict h) by infer_instance
#align
  algebraic_geometry.is_open_immersion.of_restrict AlgebraicGeometry.IsOpenImmersion.of_restrict

namespace IsOpenImmersion

variable {X Y Z : SchemeCat.{u}} (f : X ⟶ Z) (g : Y ⟶ Z)

variable [H : IsOpenImmersion f]

instance (priority := 100) of_is_iso [IsIso g] : IsOpenImmersion g :=
  @LocallyRingedSpaceCat.IsOpenImmersion.of_is_iso _
    (show IsIso ((inducedFunctor _).map g) by infer_instance)
#align algebraic_geometry.is_open_immersion.of_is_iso AlgebraicGeometry.IsOpenImmersion.of_is_iso

theorem to_iso {X Y : SchemeCat} (f : X ⟶ Y) [h : IsOpenImmersion f] [Epi f.1.base] : IsIso f :=
  @is_iso_of_reflects_iso _ _ f
    (Scheme.forget_to_LocallyRingedSpace ⋙
      LocallyRingedSpace.forget_to_SheafedSpace ⋙ SheafedSpace.forget_to_PresheafedSpace)
    (@PresheafedSpaceCat.IsOpenImmersion.to_iso _ f.1 h _) _
#align algebraic_geometry.is_open_immersion.to_iso AlgebraicGeometry.IsOpenImmersion.to_iso

theorem of_stalk_iso {X Y : SchemeCat} (f : X ⟶ Y) (hf : OpenEmbedding f.1.base)
    [∀ x, IsIso (PresheafedSpaceCat.stalkMap f.1 x)] : IsOpenImmersion f :=
  SheafedSpaceCat.IsOpenImmersion.of_stalk_iso f.1 hf
#align
  algebraic_geometry.is_open_immersion.of_stalk_iso AlgebraicGeometry.IsOpenImmersion.of_stalk_iso

theorem iff_stalk_iso {X Y : SchemeCat} (f : X ⟶ Y) :
    IsOpenImmersion f ↔ OpenEmbedding f.1.base ∧ ∀ x, IsIso (PresheafedSpaceCat.stalkMap f.1 x) :=
  ⟨fun H => ⟨H.1, inferInstance⟩, fun ⟨h₁, h₂⟩ => @IsOpenImmersion.of_stalk_iso f h₁ h₂⟩
#align
  algebraic_geometry.is_open_immersion.iff_stalk_iso AlgebraicGeometry.IsOpenImmersion.iff_stalk_iso

theorem AlgebraicGeometry.is_iso_iff_is_open_immersion {X Y : SchemeCat} (f : X ⟶ Y) :
    IsIso f ↔ IsOpenImmersion f ∧ Epi f.1.base :=
  ⟨fun H => ⟨inferInstance, inferInstance⟩, fun ⟨h₁, h₂⟩ => @IsOpenImmersion.to_iso f h₁ h₂⟩
#align
  algebraic_geometry.is_iso_iff_is_open_immersion AlgebraicGeometry.is_iso_iff_is_open_immersion

theorem AlgebraicGeometry.is_iso_iff_stalk_iso {X Y : SchemeCat} (f : X ⟶ Y) :
    IsIso f ↔ IsIso f.1.base ∧ ∀ x, IsIso (PresheafedSpaceCat.stalkMap f.1 x) :=
  by
  rw [is_iso_iff_is_open_immersion, is_open_immersion.iff_stalk_iso, and_comm', ← and_assoc']
  refine' and_congr ⟨_, _⟩ Iff.rfl
  · rintro ⟨h₁, h₂⟩
    convert_to
      is_iso
        (TopCat.isoOfHomeo
            (Homeomorph.homeomorphOfContinuousOpen
              (Equiv.ofBijective _ ⟨h₂.inj, (TopCat.epi_iff_surjective _).mp h₁⟩) h₂.continuous
              h₂.is_open_map)).Hom
    · ext
      rfl
    · infer_instance
  · intro H
    exact ⟨inferInstance, (TopCat.homeoOfIso (as_iso f.1.base)).OpenEmbedding⟩
#align algebraic_geometry.is_iso_iff_stalk_iso AlgebraicGeometry.is_iso_iff_stalk_iso

/-- A open immersion induces an isomorphism from the domain onto the image -/
def isoRestrict : X ≅ (Z.restrict H.base_open : _) :=
  ⟨H.isoRestrict.Hom, H.isoRestrict.inv, H.isoRestrict.hom_inv_id, H.isoRestrict.inv_hom_id⟩
#align
  algebraic_geometry.is_open_immersion.iso_restrict AlgebraicGeometry.IsOpenImmersion.isoRestrict

include H

-- mathport name: exprforget
local notation "forget" => SchemeCat.forgetToLocallyRingedSpace

instance mono : Mono f :=
  (inducedFunctor _).mono_of_mono_map (show @Mono LocallyRingedSpaceCat _ _ _ f by infer_instance)
#align algebraic_geometry.is_open_immersion.mono AlgebraicGeometry.IsOpenImmersion.mono

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.instance
      (Term.attrKind [])
      "instance"
      []
      [(Command.declId `forget_map_is_open_immersion [])]
      (Command.declSig
       []
       (Term.typeSpec
        ":"
        (Term.app
         `LocallyRingedSpaceCat.IsOpenImmersion
         [(Term.app
           (Term.proj
            (AlgebraicGeometry.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget "forget")
            "."
            `map)
           [`f])])))
      (Command.declValSimple
       ":="
       (Term.anonymousCtor "⟨" [(Term.proj `H "." `base_open) "," (Term.proj `H "." `c_iso)] "⟩")
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [(Term.proj `H "." `base_open) "," (Term.proj `H "." `c_iso)] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `H "." `c_iso)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `H
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `H "." `base_open)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `H
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app
       `LocallyRingedSpaceCat.IsOpenImmersion
       [(Term.app
         (Term.proj
          (AlgebraicGeometry.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget "forget")
          "."
          `map)
         [`f])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (AlgebraicGeometry.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget "forget")
        "."
        `map)
       [`f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (AlgebraicGeometry.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget "forget")
       "."
       `map)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (AlgebraicGeometry.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget "forget")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget', expected 'AlgebraicGeometry.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget._@.AlgebraicGeometry.OpenImmersion._hyg.695'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
instance
  forget_map_is_open_immersion
  : LocallyRingedSpaceCat.IsOpenImmersion forget . map f
  := ⟨ H . base_open , H . c_iso ⟩
#align
  algebraic_geometry.is_open_immersion.forget_map_is_open_immersion AlgebraicGeometry.IsOpenImmersion.forget_map_is_open_immersion

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.instance
      (Term.attrKind [])
      "instance"
      []
      [(Command.declId `hasLimitCospanForgetOfLeft [])]
      (Command.declSig
       []
       (Term.typeSpec
        ":"
        (Term.app
         `HasLimit
         [(CategoryTheory.Functor.CategoryTheory.Functor.Basic.«term_⋙_»
           (Term.app `cospan [`f `g])
           " ⋙ "
           `Scheme.forget_to_LocallyRingedSpace)])))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.apply
            "apply"
            (Term.app
             `has_limit_of_iso
             [(Term.proj
               (Term.app (Term.explicitUniv `diagramIsoCospan ".{" [`u] "}") [(Term.hole "_")])
               "."
               `symm)]))
           []
           (Tactic.change
            "change"
            (Term.app
             `has_limit
             [(Term.app
               `cospan
               [(Term.app
                 (Term.proj
                  (AlgebraicGeometry.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget
                   "forget")
                  "."
                  `map)
                 [`f])
                (Term.app
                 (Term.proj
                  (AlgebraicGeometry.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget
                   "forget")
                  "."
                  `map)
                 [`g])])])
            [])
           []
           (Tactic.tacticInfer_instance "infer_instance")])))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.apply
           "apply"
           (Term.app
            `has_limit_of_iso
            [(Term.proj
              (Term.app (Term.explicitUniv `diagramIsoCospan ".{" [`u] "}") [(Term.hole "_")])
              "."
              `symm)]))
          []
          (Tactic.change
           "change"
           (Term.app
            `has_limit
            [(Term.app
              `cospan
              [(Term.app
                (Term.proj
                 (AlgebraicGeometry.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget
                  "forget")
                 "."
                 `map)
                [`f])
               (Term.app
                (Term.proj
                 (AlgebraicGeometry.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget
                  "forget")
                 "."
                 `map)
                [`g])])])
           [])
          []
          (Tactic.tacticInfer_instance "infer_instance")])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticInfer_instance "infer_instance")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.change
       "change"
       (Term.app
        `has_limit
        [(Term.app
          `cospan
          [(Term.app
            (Term.proj
             (AlgebraicGeometry.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget "forget")
             "."
             `map)
            [`f])
           (Term.app
            (Term.proj
             (AlgebraicGeometry.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget "forget")
             "."
             `map)
            [`g])])])
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `has_limit
       [(Term.app
         `cospan
         [(Term.app
           (Term.proj
            (AlgebraicGeometry.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget "forget")
            "."
            `map)
           [`f])
          (Term.app
           (Term.proj
            (AlgebraicGeometry.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget "forget")
            "."
            `map)
           [`g])])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `cospan
       [(Term.app
         (Term.proj
          (AlgebraicGeometry.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget "forget")
          "."
          `map)
         [`f])
        (Term.app
         (Term.proj
          (AlgebraicGeometry.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget "forget")
          "."
          `map)
         [`g])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (AlgebraicGeometry.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget "forget")
        "."
        `map)
       [`g])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (AlgebraicGeometry.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget "forget")
       "."
       `map)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (AlgebraicGeometry.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget "forget")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget', expected 'AlgebraicGeometry.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget._@.AlgebraicGeometry.OpenImmersion._hyg.695'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
instance
  hasLimitCospanForgetOfLeft
  : HasLimit cospan f g ⋙ Scheme.forget_to_LocallyRingedSpace
  :=
    by
      apply has_limit_of_iso diagramIsoCospan .{ u } _ . symm
        change has_limit cospan forget . map f forget . map g
        infer_instance
#align
  algebraic_geometry.is_open_immersion.has_limit_cospan_forget_of_left AlgebraicGeometry.IsOpenImmersion.hasLimitCospanForgetOfLeft

open CategoryTheory.Limits.WalkingCospan

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.instance
      (Term.attrKind [])
      "instance"
      []
      [(Command.declId `hasLimitCospanForgetOfLeft' [])]
      (Command.declSig
       []
       (Term.typeSpec
        ":"
        (Term.app
         `HasLimit
         [(Term.app
           `cospan
           [(Term.app
             (Term.proj
              (CategoryTheory.Functor.CategoryTheory.Functor.Basic.«term_⋙_»
               (Term.app `cospan [`f `g])
               " ⋙ "
               (AlgebraicGeometry.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget
                "forget"))
              "."
              `map)
             [`Hom.inl])
            (Term.app
             (Term.proj
              (CategoryTheory.Functor.CategoryTheory.Functor.Basic.«term_⋙_»
               (Term.app `cospan [`f `g])
               " ⋙ "
               (AlgebraicGeometry.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget
                "forget"))
              "."
              `map)
             [`Hom.inr])])])))
      (Command.declValSimple
       ":="
       (Term.show
        "show"
        (Term.app
         `HasLimit
         [(Term.app
           `cospan
           [(Term.app
             (Term.proj
              (AlgebraicGeometry.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget
               "forget")
              "."
              `map)
             [`f])
            (Term.app
             (Term.proj
              (AlgebraicGeometry.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget
               "forget")
              "."
              `map)
             [`g])])])
        (Term.fromTerm "from" `inferInstance))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.show
       "show"
       (Term.app
        `HasLimit
        [(Term.app
          `cospan
          [(Term.app
            (Term.proj
             (AlgebraicGeometry.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget "forget")
             "."
             `map)
            [`f])
           (Term.app
            (Term.proj
             (AlgebraicGeometry.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget "forget")
             "."
             `map)
            [`g])])])
       (Term.fromTerm "from" `inferInstance))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `inferInstance
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app
       `HasLimit
       [(Term.app
         `cospan
         [(Term.app
           (Term.proj
            (AlgebraicGeometry.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget "forget")
            "."
            `map)
           [`f])
          (Term.app
           (Term.proj
            (AlgebraicGeometry.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget "forget")
            "."
            `map)
           [`g])])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `cospan
       [(Term.app
         (Term.proj
          (AlgebraicGeometry.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget "forget")
          "."
          `map)
         [`f])
        (Term.app
         (Term.proj
          (AlgebraicGeometry.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget "forget")
          "."
          `map)
         [`g])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (AlgebraicGeometry.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget "forget")
        "."
        `map)
       [`g])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (AlgebraicGeometry.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget "forget")
       "."
       `map)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (AlgebraicGeometry.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget "forget")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget', expected 'AlgebraicGeometry.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget._@.AlgebraicGeometry.OpenImmersion._hyg.695'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
instance
  hasLimitCospanForgetOfLeft'
  : HasLimit cospan cospan f g ⋙ forget . map Hom.inl cospan f g ⋙ forget . map Hom.inr
  := show HasLimit cospan forget . map f forget . map g from inferInstance
#align
  algebraic_geometry.is_open_immersion.has_limit_cospan_forget_of_left' AlgebraicGeometry.IsOpenImmersion.hasLimitCospanForgetOfLeft'

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.instance
      (Term.attrKind [])
      "instance"
      []
      [(Command.declId `hasLimitCospanForgetOfRight [])]
      (Command.declSig
       []
       (Term.typeSpec
        ":"
        (Term.app
         `HasLimit
         [(CategoryTheory.Functor.CategoryTheory.Functor.Basic.«term_⋙_»
           (Term.app `cospan [`g `f])
           " ⋙ "
           (AlgebraicGeometry.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget
            "forget"))])))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.apply
            "apply"
            (Term.app
             `has_limit_of_iso
             [(Term.proj
               (Term.app (Term.explicitUniv `diagramIsoCospan ".{" [`u] "}") [(Term.hole "_")])
               "."
               `symm)]))
           []
           (Tactic.change
            "change"
            (Term.app
             `has_limit
             [(Term.app
               `cospan
               [(Term.app
                 (Term.proj
                  (AlgebraicGeometry.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget
                   "forget")
                  "."
                  `map)
                 [`g])
                (Term.app
                 (Term.proj
                  (AlgebraicGeometry.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget
                   "forget")
                  "."
                  `map)
                 [`f])])])
            [])
           []
           (Tactic.tacticInfer_instance "infer_instance")])))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.apply
           "apply"
           (Term.app
            `has_limit_of_iso
            [(Term.proj
              (Term.app (Term.explicitUniv `diagramIsoCospan ".{" [`u] "}") [(Term.hole "_")])
              "."
              `symm)]))
          []
          (Tactic.change
           "change"
           (Term.app
            `has_limit
            [(Term.app
              `cospan
              [(Term.app
                (Term.proj
                 (AlgebraicGeometry.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget
                  "forget")
                 "."
                 `map)
                [`g])
               (Term.app
                (Term.proj
                 (AlgebraicGeometry.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget
                  "forget")
                 "."
                 `map)
                [`f])])])
           [])
          []
          (Tactic.tacticInfer_instance "infer_instance")])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticInfer_instance "infer_instance")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.change
       "change"
       (Term.app
        `has_limit
        [(Term.app
          `cospan
          [(Term.app
            (Term.proj
             (AlgebraicGeometry.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget "forget")
             "."
             `map)
            [`g])
           (Term.app
            (Term.proj
             (AlgebraicGeometry.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget "forget")
             "."
             `map)
            [`f])])])
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `has_limit
       [(Term.app
         `cospan
         [(Term.app
           (Term.proj
            (AlgebraicGeometry.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget "forget")
            "."
            `map)
           [`g])
          (Term.app
           (Term.proj
            (AlgebraicGeometry.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget "forget")
            "."
            `map)
           [`f])])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `cospan
       [(Term.app
         (Term.proj
          (AlgebraicGeometry.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget "forget")
          "."
          `map)
         [`g])
        (Term.app
         (Term.proj
          (AlgebraicGeometry.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget "forget")
          "."
          `map)
         [`f])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (AlgebraicGeometry.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget "forget")
        "."
        `map)
       [`f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (AlgebraicGeometry.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget "forget")
       "."
       `map)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (AlgebraicGeometry.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget "forget")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget', expected 'AlgebraicGeometry.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget._@.AlgebraicGeometry.OpenImmersion._hyg.695'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
instance
  hasLimitCospanForgetOfRight
  : HasLimit cospan g f ⋙ forget
  :=
    by
      apply has_limit_of_iso diagramIsoCospan .{ u } _ . symm
        change has_limit cospan forget . map g forget . map f
        infer_instance
#align
  algebraic_geometry.is_open_immersion.has_limit_cospan_forget_of_right AlgebraicGeometry.IsOpenImmersion.hasLimitCospanForgetOfRight

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.instance
      (Term.attrKind [])
      "instance"
      []
      [(Command.declId `hasLimitCospanForgetOfRight' [])]
      (Command.declSig
       []
       (Term.typeSpec
        ":"
        (Term.app
         `HasLimit
         [(Term.app
           `cospan
           [(Term.app
             (Term.proj
              (CategoryTheory.Functor.CategoryTheory.Functor.Basic.«term_⋙_»
               (Term.app `cospan [`g `f])
               " ⋙ "
               (AlgebraicGeometry.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget
                "forget"))
              "."
              `map)
             [`Hom.inl])
            (Term.app
             (Term.proj
              (CategoryTheory.Functor.CategoryTheory.Functor.Basic.«term_⋙_»
               (Term.app `cospan [`g `f])
               " ⋙ "
               (AlgebraicGeometry.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget
                "forget"))
              "."
              `map)
             [`Hom.inr])])])))
      (Command.declValSimple
       ":="
       (Term.show
        "show"
        (Term.app
         `HasLimit
         [(Term.app
           `cospan
           [(Term.app
             (Term.proj
              (AlgebraicGeometry.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget
               "forget")
              "."
              `map)
             [`g])
            (Term.app
             (Term.proj
              (AlgebraicGeometry.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget
               "forget")
              "."
              `map)
             [`f])])])
        (Term.fromTerm "from" `inferInstance))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.show
       "show"
       (Term.app
        `HasLimit
        [(Term.app
          `cospan
          [(Term.app
            (Term.proj
             (AlgebraicGeometry.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget "forget")
             "."
             `map)
            [`g])
           (Term.app
            (Term.proj
             (AlgebraicGeometry.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget "forget")
             "."
             `map)
            [`f])])])
       (Term.fromTerm "from" `inferInstance))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `inferInstance
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app
       `HasLimit
       [(Term.app
         `cospan
         [(Term.app
           (Term.proj
            (AlgebraicGeometry.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget "forget")
            "."
            `map)
           [`g])
          (Term.app
           (Term.proj
            (AlgebraicGeometry.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget "forget")
            "."
            `map)
           [`f])])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `cospan
       [(Term.app
         (Term.proj
          (AlgebraicGeometry.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget "forget")
          "."
          `map)
         [`g])
        (Term.app
         (Term.proj
          (AlgebraicGeometry.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget "forget")
          "."
          `map)
         [`f])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (AlgebraicGeometry.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget "forget")
        "."
        `map)
       [`f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (AlgebraicGeometry.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget "forget")
       "."
       `map)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (AlgebraicGeometry.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget "forget")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget', expected 'AlgebraicGeometry.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget._@.AlgebraicGeometry.OpenImmersion._hyg.695'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
instance
  hasLimitCospanForgetOfRight'
  : HasLimit cospan cospan g f ⋙ forget . map Hom.inl cospan g f ⋙ forget . map Hom.inr
  := show HasLimit cospan forget . map g forget . map f from inferInstance
#align
  algebraic_geometry.is_open_immersion.has_limit_cospan_forget_of_right' AlgebraicGeometry.IsOpenImmersion.hasLimitCospanForgetOfRight'

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.instance
      (Term.attrKind [])
      "instance"
      []
      [(Command.declId `forgetCreatesPullbackOfLeft [])]
      (Command.declSig
       []
       (Term.typeSpec
        ":"
        (Term.app
         `CreatesLimit
         [(Term.app `cospan [`f `g])
          (AlgebraicGeometry.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget
           "forget")])))
      (Command.declValSimple
       ":="
       (Term.app
        `createsLimitOfFullyFaithfulOfIso
        [(Term.app
          `PresheafedSpaceCat.IsOpenImmersion.toScheme
          [`Y
           (Term.proj
            (Term.app
             (Term.explicit "@" `pullback.snd)
             [`LocallyRingedSpaceCat
              (Term.hole "_")
              (Term.hole "_")
              (Term.hole "_")
              (Term.hole "_")
              `f
              `g
              (Term.hole "_")])
            "."
            (fieldIdx "1"))])
         (CategoryTheory.Iso.CategoryTheory.Isomorphism.«term_≪≫_»
          (Term.app
           `eqToIso
           [(Term.byTactic
             "by"
             (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])])))])
          " ≪≫ "
          (Term.app
           `HasLimit.isoOfNatIso
           [(Term.proj (Term.app `diagramIsoCospan [(Term.hole "_")]) "." `symm)]))])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `createsLimitOfFullyFaithfulOfIso
       [(Term.app
         `PresheafedSpaceCat.IsOpenImmersion.toScheme
         [`Y
          (Term.proj
           (Term.app
            (Term.explicit "@" `pullback.snd)
            [`LocallyRingedSpaceCat
             (Term.hole "_")
             (Term.hole "_")
             (Term.hole "_")
             (Term.hole "_")
             `f
             `g
             (Term.hole "_")])
           "."
           (fieldIdx "1"))])
        (CategoryTheory.Iso.CategoryTheory.Isomorphism.«term_≪≫_»
         (Term.app
          `eqToIso
          [(Term.byTactic
            "by"
            (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])])))])
         " ≪≫ "
         (Term.app
          `HasLimit.isoOfNatIso
          [(Term.proj (Term.app `diagramIsoCospan [(Term.hole "_")]) "." `symm)]))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.Iso.CategoryTheory.Isomorphism.«term_≪≫_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.Iso.CategoryTheory.Isomorphism.«term_≪≫_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (CategoryTheory.Iso.CategoryTheory.Isomorphism.«term_≪≫_»
       (Term.app
        `eqToIso
        [(Term.byTactic
          "by"
          (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])])))])
       " ≪≫ "
       (Term.app
        `HasLimit.isoOfNatIso
        [(Term.proj (Term.app `diagramIsoCospan [(Term.hole "_")]) "." `symm)]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `HasLimit.isoOfNatIso
       [(Term.proj (Term.app `diagramIsoCospan [(Term.hole "_")]) "." `symm)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.app `diagramIsoCospan [(Term.hole "_")]) "." `symm)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `diagramIsoCospan [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `diagramIsoCospan
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `diagramIsoCospan [(Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `HasLimit.isoOfNatIso
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Term.app
       `eqToIso
       [(Term.byTactic
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
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `eqToIso
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1022, (some 1023, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (CategoryTheory.Iso.CategoryTheory.Isomorphism.«term_≪≫_»
      (Term.app
       `eqToIso
       [(Term.paren
         "("
         (Term.byTactic
          "by"
          (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])])))
         ")")])
      " ≪≫ "
      (Term.app
       `HasLimit.isoOfNatIso
       [(Term.proj (Term.paren "(" (Term.app `diagramIsoCospan [(Term.hole "_")]) ")") "." `symm)]))
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       `PresheafedSpaceCat.IsOpenImmersion.toScheme
       [`Y
        (Term.proj
         (Term.app
          (Term.explicit "@" `pullback.snd)
          [`LocallyRingedSpaceCat
           (Term.hole "_")
           (Term.hole "_")
           (Term.hole "_")
           (Term.hole "_")
           `f
           `g
           (Term.hole "_")])
         "."
         (fieldIdx "1"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj
       (Term.app
        (Term.explicit "@" `pullback.snd)
        [`LocallyRingedSpaceCat
         (Term.hole "_")
         (Term.hole "_")
         (Term.hole "_")
         (Term.hole "_")
         `f
         `g
         (Term.hole "_")])
       "."
       (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       (Term.explicit "@" `pullback.snd)
       [`LocallyRingedSpaceCat
        (Term.hole "_")
        (Term.hole "_")
        (Term.hole "_")
        (Term.hole "_")
        `f
        `g
        (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      `LocallyRingedSpaceCat
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.explicit "@" `pullback.snd)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `pullback.snd
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (some 1024,
     term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      (Term.explicit "@" `pullback.snd)
      [`LocallyRingedSpaceCat
       (Term.hole "_")
       (Term.hole "_")
       (Term.hole "_")
       (Term.hole "_")
       `f
       `g
       (Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `Y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `PresheafedSpaceCat.IsOpenImmersion.toScheme
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `PresheafedSpaceCat.IsOpenImmersion.toScheme
      [`Y
       (Term.proj
        (Term.paren
         "("
         (Term.app
          (Term.explicit "@" `pullback.snd)
          [`LocallyRingedSpaceCat
           (Term.hole "_")
           (Term.hole "_")
           (Term.hole "_")
           (Term.hole "_")
           `f
           `g
           (Term.hole "_")])
         ")")
        "."
        (fieldIdx "1"))])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `createsLimitOfFullyFaithfulOfIso
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app
       `CreatesLimit
       [(Term.app `cospan [`f `g])
        (AlgebraicGeometry.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget "forget")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (AlgebraicGeometry.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget "forget")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget', expected 'AlgebraicGeometry.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget._@.AlgebraicGeometry.OpenImmersion._hyg.695'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
instance
  forgetCreatesPullbackOfLeft
  : CreatesLimit cospan f g forget
  :=
    createsLimitOfFullyFaithfulOfIso
      PresheafedSpaceCat.IsOpenImmersion.toScheme
          Y @ pullback.snd LocallyRingedSpaceCat _ _ _ _ f g _ . 1
        eqToIso by simp ≪≫ HasLimit.isoOfNatIso diagramIsoCospan _ . symm
#align
  algebraic_geometry.is_open_immersion.forget_creates_pullback_of_left AlgebraicGeometry.IsOpenImmersion.forgetCreatesPullbackOfLeft

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.instance
      (Term.attrKind [])
      "instance"
      []
      [(Command.declId `forgetCreatesPullbackOfRight [])]
      (Command.declSig
       []
       (Term.typeSpec
        ":"
        (Term.app
         `CreatesLimit
         [(Term.app `cospan [`g `f])
          (AlgebraicGeometry.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget
           "forget")])))
      (Command.declValSimple
       ":="
       (Term.app
        `createsLimitOfFullyFaithfulOfIso
        [(Term.app
          `PresheafedSpaceCat.IsOpenImmersion.toScheme
          [`Y
           (Term.proj
            (Term.app
             (Term.explicit "@" `pullback.fst)
             [`LocallyRingedSpaceCat
              (Term.hole "_")
              (Term.hole "_")
              (Term.hole "_")
              (Term.hole "_")
              `g
              `f
              (Term.hole "_")])
            "."
            (fieldIdx "1"))])
         (CategoryTheory.Iso.CategoryTheory.Isomorphism.«term_≪≫_»
          (Term.app
           `eqToIso
           [(Term.byTactic
             "by"
             (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])])))])
          " ≪≫ "
          (Term.app
           `HasLimit.isoOfNatIso
           [(Term.proj (Term.app `diagramIsoCospan [(Term.hole "_")]) "." `symm)]))])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `createsLimitOfFullyFaithfulOfIso
       [(Term.app
         `PresheafedSpaceCat.IsOpenImmersion.toScheme
         [`Y
          (Term.proj
           (Term.app
            (Term.explicit "@" `pullback.fst)
            [`LocallyRingedSpaceCat
             (Term.hole "_")
             (Term.hole "_")
             (Term.hole "_")
             (Term.hole "_")
             `g
             `f
             (Term.hole "_")])
           "."
           (fieldIdx "1"))])
        (CategoryTheory.Iso.CategoryTheory.Isomorphism.«term_≪≫_»
         (Term.app
          `eqToIso
          [(Term.byTactic
            "by"
            (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])])))])
         " ≪≫ "
         (Term.app
          `HasLimit.isoOfNatIso
          [(Term.proj (Term.app `diagramIsoCospan [(Term.hole "_")]) "." `symm)]))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.Iso.CategoryTheory.Isomorphism.«term_≪≫_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.Iso.CategoryTheory.Isomorphism.«term_≪≫_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (CategoryTheory.Iso.CategoryTheory.Isomorphism.«term_≪≫_»
       (Term.app
        `eqToIso
        [(Term.byTactic
          "by"
          (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])])))])
       " ≪≫ "
       (Term.app
        `HasLimit.isoOfNatIso
        [(Term.proj (Term.app `diagramIsoCospan [(Term.hole "_")]) "." `symm)]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `HasLimit.isoOfNatIso
       [(Term.proj (Term.app `diagramIsoCospan [(Term.hole "_")]) "." `symm)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.app `diagramIsoCospan [(Term.hole "_")]) "." `symm)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `diagramIsoCospan [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `diagramIsoCospan
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `diagramIsoCospan [(Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `HasLimit.isoOfNatIso
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Term.app
       `eqToIso
       [(Term.byTactic
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
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `eqToIso
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1022, (some 1023, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (CategoryTheory.Iso.CategoryTheory.Isomorphism.«term_≪≫_»
      (Term.app
       `eqToIso
       [(Term.paren
         "("
         (Term.byTactic
          "by"
          (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])])))
         ")")])
      " ≪≫ "
      (Term.app
       `HasLimit.isoOfNatIso
       [(Term.proj (Term.paren "(" (Term.app `diagramIsoCospan [(Term.hole "_")]) ")") "." `symm)]))
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       `PresheafedSpaceCat.IsOpenImmersion.toScheme
       [`Y
        (Term.proj
         (Term.app
          (Term.explicit "@" `pullback.fst)
          [`LocallyRingedSpaceCat
           (Term.hole "_")
           (Term.hole "_")
           (Term.hole "_")
           (Term.hole "_")
           `g
           `f
           (Term.hole "_")])
         "."
         (fieldIdx "1"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj
       (Term.app
        (Term.explicit "@" `pullback.fst)
        [`LocallyRingedSpaceCat
         (Term.hole "_")
         (Term.hole "_")
         (Term.hole "_")
         (Term.hole "_")
         `g
         `f
         (Term.hole "_")])
       "."
       (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       (Term.explicit "@" `pullback.fst)
       [`LocallyRingedSpaceCat
        (Term.hole "_")
        (Term.hole "_")
        (Term.hole "_")
        (Term.hole "_")
        `g
        `f
        (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      `LocallyRingedSpaceCat
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.explicit "@" `pullback.fst)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `pullback.fst
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (some 1024,
     term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      (Term.explicit "@" `pullback.fst)
      [`LocallyRingedSpaceCat
       (Term.hole "_")
       (Term.hole "_")
       (Term.hole "_")
       (Term.hole "_")
       `g
       `f
       (Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `Y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `PresheafedSpaceCat.IsOpenImmersion.toScheme
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `PresheafedSpaceCat.IsOpenImmersion.toScheme
      [`Y
       (Term.proj
        (Term.paren
         "("
         (Term.app
          (Term.explicit "@" `pullback.fst)
          [`LocallyRingedSpaceCat
           (Term.hole "_")
           (Term.hole "_")
           (Term.hole "_")
           (Term.hole "_")
           `g
           `f
           (Term.hole "_")])
         ")")
        "."
        (fieldIdx "1"))])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `createsLimitOfFullyFaithfulOfIso
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app
       `CreatesLimit
       [(Term.app `cospan [`g `f])
        (AlgebraicGeometry.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget "forget")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (AlgebraicGeometry.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget "forget")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget', expected 'AlgebraicGeometry.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget._@.AlgebraicGeometry.OpenImmersion._hyg.695'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
instance
  forgetCreatesPullbackOfRight
  : CreatesLimit cospan g f forget
  :=
    createsLimitOfFullyFaithfulOfIso
      PresheafedSpaceCat.IsOpenImmersion.toScheme
          Y @ pullback.fst LocallyRingedSpaceCat _ _ _ _ g f _ . 1
        eqToIso by simp ≪≫ HasLimit.isoOfNatIso diagramIsoCospan _ . symm
#align
  algebraic_geometry.is_open_immersion.forget_creates_pullback_of_right AlgebraicGeometry.IsOpenImmersion.forgetCreatesPullbackOfRight

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.instance
      (Term.attrKind [])
      "instance"
      []
      [(Command.declId `forgetPreservesOfLeft [])]
      (Command.declSig
       []
       (Term.typeSpec
        ":"
        (Term.app
         `PreservesLimit
         [(Term.app `cospan [`f `g])
          (AlgebraicGeometry.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget
           "forget")])))
      (Command.declValSimple
       ":="
       (Term.app
        `CategoryTheory.preservesLimitOfCreatesLimitAndHasLimit
        [(Term.hole "_") (Term.hole "_")])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `CategoryTheory.preservesLimitOfCreatesLimitAndHasLimit
       [(Term.hole "_") (Term.hole "_")])
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
      `CategoryTheory.preservesLimitOfCreatesLimitAndHasLimit
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app
       `PreservesLimit
       [(Term.app `cospan [`f `g])
        (AlgebraicGeometry.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget "forget")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (AlgebraicGeometry.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget "forget")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget', expected 'AlgebraicGeometry.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget._@.AlgebraicGeometry.OpenImmersion._hyg.695'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
instance
  forgetPreservesOfLeft
  : PreservesLimit cospan f g forget
  := CategoryTheory.preservesLimitOfCreatesLimitAndHasLimit _ _
#align
  algebraic_geometry.is_open_immersion.forget_preserves_of_left AlgebraicGeometry.IsOpenImmersion.forgetPreservesOfLeft

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.instance
      (Term.attrKind [])
      "instance"
      []
      [(Command.declId `forgetPreservesOfRight [])]
      (Command.declSig
       []
       (Term.typeSpec
        ":"
        (Term.app
         `PreservesLimit
         [(Term.app `cospan [`g `f])
          (AlgebraicGeometry.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget
           "forget")])))
      (Command.declValSimple
       ":="
       (Term.app `preservesPullbackSymmetry [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `preservesPullbackSymmetry [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
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
      `preservesPullbackSymmetry
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app
       `PreservesLimit
       [(Term.app `cospan [`g `f])
        (AlgebraicGeometry.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget "forget")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (AlgebraicGeometry.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget "forget")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget', expected 'AlgebraicGeometry.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget._@.AlgebraicGeometry.OpenImmersion._hyg.695'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
instance
  forgetPreservesOfRight
  : PreservesLimit cospan g f forget
  := preservesPullbackSymmetry _ _ _
#align
  algebraic_geometry.is_open_immersion.forget_preserves_of_right AlgebraicGeometry.IsOpenImmersion.forgetPreservesOfRight

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.instance
      (Term.attrKind [])
      "instance"
      []
      [(Command.declId `has_pullback_of_left [])]
      (Command.declSig [] (Term.typeSpec ":" (Term.app `HasPullback [`f `g])))
      (Command.declValSimple
       ":="
       (Term.app
        `hasLimitOfCreated
        [(Term.app `cospan [`f `g])
         (AlgebraicGeometry.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget "forget")])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `hasLimitOfCreated
       [(Term.app `cospan [`f `g])
        (AlgebraicGeometry.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget "forget")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (AlgebraicGeometry.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget "forget")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget', expected 'AlgebraicGeometry.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget._@.AlgebraicGeometry.OpenImmersion._hyg.695'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
instance has_pullback_of_left : HasPullback f g := hasLimitOfCreated cospan f g forget
#align
  algebraic_geometry.is_open_immersion.has_pullback_of_left AlgebraicGeometry.IsOpenImmersion.has_pullback_of_left

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.instance
      (Term.attrKind [])
      "instance"
      []
      [(Command.declId `has_pullback_of_right [])]
      (Command.declSig [] (Term.typeSpec ":" (Term.app `HasPullback [`g `f])))
      (Command.declValSimple
       ":="
       (Term.app
        `hasLimitOfCreated
        [(Term.app `cospan [`g `f])
         (AlgebraicGeometry.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget "forget")])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `hasLimitOfCreated
       [(Term.app `cospan [`g `f])
        (AlgebraicGeometry.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget "forget")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (AlgebraicGeometry.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget "forget")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget', expected 'AlgebraicGeometry.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget._@.AlgebraicGeometry.OpenImmersion._hyg.695'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
instance has_pullback_of_right : HasPullback g f := hasLimitOfCreated cospan g f forget
#align
  algebraic_geometry.is_open_immersion.has_pullback_of_right AlgebraicGeometry.IsOpenImmersion.has_pullback_of_right

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.instance
      (Term.attrKind [])
      "instance"
      []
      [(Command.declId `pullback_snd_of_left [])]
      (Command.declSig
       []
       (Term.typeSpec
        ":"
        (Term.app
         `IsOpenImmersion
         [(Term.typeAscription
           "("
           `pullback.snd
           ":"
           [(Combinatorics.Quiver.Basic.«term_⟶_»
             (Term.app `pullback [`f `g])
             " ⟶ "
             (Term.hole "_"))]
           ")")])))
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
              []
              []
              ":="
              (Term.app
               `preserves_pullback.iso_hom_snd
               [(AlgebraicGeometry.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget
                 "forget")
                `f
                `g]))))
           []
           (Tactic.dsimp
            "dsimp"
            []
            []
            ["only"]
            ["["
             [(Tactic.simpLemma [] [] `Scheme.forget_to_LocallyRingedSpace)
              ","
              (Tactic.simpLemma [] [] `induced_functor_map)]
             "]"]
            [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq "[" [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `this)] "]")
            [])
           []
           (Tactic.change
            "change"
            (Term.app `LocallyRingedSpace.is_open_immersion [(Term.hole "_")])
            [])
           []
           (Tactic.tacticInfer_instance "infer_instance")])))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             []
             []
             ":="
             (Term.app
              `preserves_pullback.iso_hom_snd
              [(AlgebraicGeometry.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget
                "forget")
               `f
               `g]))))
          []
          (Tactic.dsimp
           "dsimp"
           []
           []
           ["only"]
           ["["
            [(Tactic.simpLemma [] [] `Scheme.forget_to_LocallyRingedSpace)
             ","
             (Tactic.simpLemma [] [] `induced_functor_map)]
            "]"]
           [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `this)] "]")
           [])
          []
          (Tactic.change
           "change"
           (Term.app `LocallyRingedSpace.is_open_immersion [(Term.hole "_")])
           [])
          []
          (Tactic.tacticInfer_instance "infer_instance")])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticInfer_instance "infer_instance")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.change "change" (Term.app `LocallyRingedSpace.is_open_immersion [(Term.hole "_")]) [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `LocallyRingedSpace.is_open_immersion [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `LocallyRingedSpace.is_open_immersion
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `this)] "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `this
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.dsimp
       "dsimp"
       []
       []
       ["only"]
       ["["
        [(Tactic.simpLemma [] [] `Scheme.forget_to_LocallyRingedSpace)
         ","
         (Tactic.simpLemma [] [] `induced_functor_map)]
        "]"]
       [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `this
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `induced_functor_map
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Scheme.forget_to_LocallyRingedSpace
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         []
         []
         ":="
         (Term.app
          `preserves_pullback.iso_hom_snd
          [(AlgebraicGeometry.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget "forget")
           `f
           `g]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `preserves_pullback.iso_hom_snd
       [(AlgebraicGeometry.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget "forget")
        `f
        `g])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (AlgebraicGeometry.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget "forget")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget', expected 'AlgebraicGeometry.IsOpenImmersion.AlgebraicGeometry.OpenImmersion.termforget._@.AlgebraicGeometry.OpenImmersion._hyg.695'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.letPatDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveEqnsDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
instance
  pullback_snd_of_left
  : IsOpenImmersion ( pullback.snd : pullback f g ⟶ _ )
  :=
    by
      have := preserves_pullback.iso_hom_snd forget f g
        dsimp only [ Scheme.forget_to_LocallyRingedSpace , induced_functor_map ] at this
        rw [ ← this ]
        change LocallyRingedSpace.is_open_immersion _
        infer_instance
#align
  algebraic_geometry.is_open_immersion.pullback_snd_of_left AlgebraicGeometry.IsOpenImmersion.pullback_snd_of_left

instance pullback_fst_of_right : IsOpenImmersion (pullback.fst : pullback g f ⟶ _) :=
  by
  rw [← pullback_symmetry_hom_comp_snd]
  infer_instance
#align
  algebraic_geometry.is_open_immersion.pullback_fst_of_right AlgebraicGeometry.IsOpenImmersion.pullback_fst_of_right

instance pullback_to_base [IsOpenImmersion g] :
    IsOpenImmersion (limit.π (cospan f g) WalkingCospan.one) :=
  by
  rw [← limit.w (cospan f g) walking_cospan.hom.inl]
  change is_open_immersion (_ ≫ f)
  infer_instance
#align
  algebraic_geometry.is_open_immersion.pullback_to_base AlgebraicGeometry.IsOpenImmersion.pullback_to_base

instance forgetToTopPreservesOfLeft : PreservesLimit (cospan f g) SchemeCat.forgetToTop :=
  by
  apply (config := { instances := false }) limits.comp_preserves_limit
  infer_instance
  apply preserves_limit_of_iso_diagram _ (diagramIsoCospan.{u} _).symm
  dsimp [LocallyRingedSpace.forget_to_Top]
  infer_instance
#align
  algebraic_geometry.is_open_immersion.forget_to_Top_preserves_of_left AlgebraicGeometry.IsOpenImmersion.forgetToTopPreservesOfLeft

instance forgetToTopPreservesOfRight : PreservesLimit (cospan g f) SchemeCat.forgetToTop :=
  preservesPullbackSymmetry _ _ _
#align
  algebraic_geometry.is_open_immersion.forget_to_Top_preserves_of_right AlgebraicGeometry.IsOpenImmersion.forgetToTopPreservesOfRight

theorem range_pullback_snd_of_left :
    Set.range (pullback.snd : pullback f g ⟶ Y).1.base =
      (Opens.map g.1.base).obj ⟨Set.range f.1.base, H.base_open.open_range⟩ :=
  by
  rw [←
    show _ = (pullback.snd : pullback f g ⟶ _).1.base from
      preserves_pullback.iso_hom_snd Scheme.forget_to_Top f g,
    coe_comp, Set.range_comp, set.range_iff_surjective.mpr, ←
    @Set.preimage_univ _ _ (pullback.fst : pullback f.1.base g.1.base ⟶ _),
    TopCat.pullback_snd_image_fst_preimage, Set.image_univ]
  rfl
  rw [← TopCat.epi_iff_surjective]
  infer_instance
#align
  algebraic_geometry.is_open_immersion.range_pullback_snd_of_left AlgebraicGeometry.IsOpenImmersion.range_pullback_snd_of_left

theorem range_pullback_fst_of_right :
    Set.range (pullback.fst : pullback g f ⟶ Y).1.base =
      (Opens.map g.1.base).obj ⟨Set.range f.1.base, H.base_open.open_range⟩ :=
  by
  rw [←
    show _ = (pullback.fst : pullback g f ⟶ _).1.base from
      preserves_pullback.iso_hom_fst Scheme.forget_to_Top g f,
    coe_comp, Set.range_comp, set.range_iff_surjective.mpr, ←
    @Set.preimage_univ _ _ (pullback.snd : pullback g.1.base f.1.base ⟶ _),
    TopCat.pullback_fst_image_snd_preimage, Set.image_univ]
  rfl
  rw [← TopCat.epi_iff_surjective]
  infer_instance
#align
  algebraic_geometry.is_open_immersion.range_pullback_fst_of_right AlgebraicGeometry.IsOpenImmersion.range_pullback_fst_of_right

theorem range_pullback_to_base_of_left :
    Set.range (pullback.fst ≫ f : pullback f g ⟶ Z).1.base =
      Set.range f.1.base ∩ Set.range g.1.base :=
  by
  rw [pullback.condition, Scheme.comp_val_base, coe_comp, Set.range_comp,
    range_pullback_snd_of_left, opens.map_obj, Subtype.coe_mk, Set.image_preimage_eq_inter_range,
    Set.inter_comm]
#align
  algebraic_geometry.is_open_immersion.range_pullback_to_base_of_left AlgebraicGeometry.IsOpenImmersion.range_pullback_to_base_of_left

theorem range_pullback_to_base_of_right :
    Set.range (pullback.fst ≫ g : pullback g f ⟶ Z).1.base =
      Set.range g.1.base ∩ Set.range f.1.base :=
  by
  rw [Scheme.comp_val_base, coe_comp, Set.range_comp, range_pullback_fst_of_right, opens.map_obj,
    Subtype.coe_mk, Set.image_preimage_eq_inter_range, Set.inter_comm]
#align
  algebraic_geometry.is_open_immersion.range_pullback_to_base_of_right AlgebraicGeometry.IsOpenImmersion.range_pullback_to_base_of_right

/-- The universal property of open immersions:
For an open immersion `f : X ⟶ Z`, given any morphism of schemes `g : Y ⟶ Z` whose topological
image is contained in the image of `f`, we can lift this morphism to a unique `Y ⟶ X` that
commutes with these maps.
-/
def lift (H' : Set.range g.1.base ⊆ Set.range f.1.base) : Y ⟶ X :=
  LocallyRingedSpaceCat.IsOpenImmersion.lift f g H'
#align algebraic_geometry.is_open_immersion.lift AlgebraicGeometry.IsOpenImmersion.lift

@[simp, reassoc.1]
theorem lift_fac (H' : Set.range g.1.base ⊆ Set.range f.1.base) : lift f g H' ≫ f = g :=
  LocallyRingedSpaceCat.IsOpenImmersion.lift_fac f g H'
#align algebraic_geometry.is_open_immersion.lift_fac AlgebraicGeometry.IsOpenImmersion.lift_fac

theorem lift_uniq (H' : Set.range g.1.base ⊆ Set.range f.1.base) (l : Y ⟶ X) (hl : l ≫ f = g) :
    l = lift f g H' :=
  LocallyRingedSpaceCat.IsOpenImmersion.lift_uniq f g H' l hl
#align algebraic_geometry.is_open_immersion.lift_uniq AlgebraicGeometry.IsOpenImmersion.lift_uniq

/-- Two open immersions with equal range are isomorphic. -/
@[simps]
def isoOfRangeEq [IsOpenImmersion g] (e : Set.range f.1.base = Set.range g.1.base) : X ≅ Y
    where
  Hom := lift g f (le_of_eq e)
  inv := lift f g (le_of_eq e.symm)
  hom_inv_id' := by
    rw [← cancel_mono f]
    simp
  inv_hom_id' := by
    rw [← cancel_mono g]
    simp
#align
  algebraic_geometry.is_open_immersion.iso_of_range_eq AlgebraicGeometry.IsOpenImmersion.isoOfRangeEq

/-- The functor `opens X ⥤ opens Y` associated with an open immersion `f : X ⟶ Y`. -/
abbrev AlgebraicGeometry.SchemeCat.Hom.opensFunctor {X Y : SchemeCat} (f : X ⟶ Y)
    [H : IsOpenImmersion f] : Opens X.carrier ⥤ Opens Y.carrier :=
  H.openFunctor
#align algebraic_geometry.Scheme.hom.opens_functor AlgebraicGeometry.SchemeCat.Hom.opensFunctor

/-- The isomorphism `Γ(X, U) ⟶ Γ(Y, f(U))` induced by an open immersion `f : X ⟶ Y`. -/
def AlgebraicGeometry.SchemeCat.Hom.invApp {X Y : SchemeCat} (f : X ⟶ Y) [H : IsOpenImmersion f]
    (U) : X.Presheaf.obj (op U) ⟶ Y.Presheaf.obj (op (f.opensFunctor.obj U)) :=
  H.invApp U
#align algebraic_geometry.Scheme.hom.inv_app AlgebraicGeometry.SchemeCat.Hom.invApp

theorem app_eq_inv_app_app_of_comp_eq_aux {X Y U : SchemeCat} (f : Y ⟶ U) (g : U ⟶ X) (fg : Y ⟶ X)
    (H : fg = f ≫ g) [h : IsOpenImmersion g] (V : Opens U.carrier) :
    (Opens.map f.1.base).obj V = (Opens.map fg.1.base).obj (g.opensFunctor.obj V) :=
  by
  subst H
  rw [Scheme.comp_val_base, opens.map_comp_obj]
  congr 1
  ext1
  exact (Set.preimage_image_eq _ h.base_open.inj).symm
#align
  algebraic_geometry.is_open_immersion.app_eq_inv_app_app_of_comp_eq_aux AlgebraicGeometry.IsOpenImmersion.app_eq_inv_app_app_of_comp_eq_aux

/-- The `fg` argument is to avoid nasty stuff about dependent types. -/
theorem app_eq_inv_app_app_of_comp_eq {X Y U : SchemeCat} (f : Y ⟶ U) (g : U ⟶ X) (fg : Y ⟶ X)
    (H : fg = f ≫ g) [h : IsOpenImmersion g] (V : Opens U.carrier) :
    f.1.c.app (op V) =
      g.invApp _ ≫
        fg.1.c.app _ ≫
          Y.Presheaf.map
            (eq_to_hom <| IsOpenImmersion.app_eq_inv_app_app_of_comp_eq_aux f g fg H V).op :=
  by
  subst H
  rw [Scheme.comp_val_c_app, category.assoc, Scheme.hom.inv_app,
    PresheafedSpace.is_open_immersion.inv_app_app_assoc, f.val.c.naturality_assoc,
    TopCat.Presheaf.pushforward_obj_map, ← functor.map_comp]
  convert (category.comp_id _).symm
  convert Y.presheaf.map_id _
#align
  algebraic_geometry.is_open_immersion.app_eq_inv_app_app_of_comp_eq AlgebraicGeometry.IsOpenImmersion.app_eq_inv_app_app_of_comp_eq

theorem lift_app {X Y U : SchemeCat} (f : U ⟶ Y) (g : X ⟶ Y) [h : IsOpenImmersion f] (H)
    (V : Opens U.carrier) :
    (IsOpenImmersion.lift f g H).1.c.app (op V) =
      f.invApp _ ≫
        g.1.c.app _ ≫
          X.Presheaf.map
            (eq_to_hom <|
                IsOpenImmersion.app_eq_inv_app_app_of_comp_eq_aux _ _ _
                  (IsOpenImmersion.lift_fac f g H).symm V).op :=
  IsOpenImmersion.app_eq_inv_app_app_of_comp_eq _ _ _ _ _
#align algebraic_geometry.is_open_immersion.lift_app AlgebraicGeometry.IsOpenImmersion.lift_app

end IsOpenImmersion

namespace SchemeCat

theorem image_basic_open {X Y : SchemeCat} (f : X ⟶ Y) [H : IsOpenImmersion f] {U : Opens X.carrier}
    (r : X.Presheaf.obj (op U)) : f.opensFunctor.obj (X.basicOpen r) = Y.basicOpen (f.invApp U r) :=
  by
  have e := Scheme.preimage_basic_open f (f.inv_app U r)
  rw [Scheme.hom.inv_app, PresheafedSpace.is_open_immersion.inv_app_app_apply,
    Scheme.basic_open_res, inf_eq_right.mpr _] at e
  rw [← e]
  ext1
  refine' set.image_preimage_eq_inter_range.trans _
  erw [Set.inter_eq_left_iff_subset]
  refine' Set.Subset.trans (Scheme.basic_open_le _ _) (Set.image_subset_range _ _)
  refine' le_trans (Scheme.basic_open_le _ _) (le_of_eq _)
  ext1
  exact (Set.preimage_image_eq _ H.base_open.inj).symm
#align algebraic_geometry.Scheme.image_basic_open AlgebraicGeometry.SchemeCat.image_basic_open

/-- The image of an open immersion as an open set. -/
@[simps]
def Hom.opensRange {X Y : SchemeCat} (f : X ⟶ Y) [H : IsOpenImmersion f] : Opens Y.carrier :=
  ⟨_, H.base_open.open_range⟩
#align algebraic_geometry.Scheme.hom.opens_range AlgebraicGeometry.SchemeCat.Hom.opensRange

end SchemeCat

section

variable (X : SchemeCat)

/-- The functor taking open subsets of `X` to open subschemes of `X`. -/
@[simps obj_left obj_hom mapLeft]
def SchemeCat.restrictFunctor : Opens X.carrier ⥤ Over X
    where
  obj U := Over.mk (X.of_restrict U.OpenEmbedding)
  map U V i :=
    Over.homMk
      (IsOpenImmersion.lift (X.of_restrict _) (X.of_restrict _)
        (by
          change Set.range coe ⊆ Set.range coe
          simp_rw [Subtype.range_coe]
          exact i.le))
      (IsOpenImmersion.lift_fac _ _ _)
  map_id' U := by
    ext1
    dsimp only [over.hom_mk_left, over.id_left]
    rw [← cancel_mono (X.of_restrict U.open_embedding), category.id_comp,
      is_open_immersion.lift_fac]
  map_comp' U V W i j := by
    ext1
    dsimp only [over.hom_mk_left, over.comp_left]
    rw [← cancel_mono (X.of_restrict W.open_embedding), category.assoc]
    iterate 3 rw [is_open_immersion.lift_fac]
#align algebraic_geometry.Scheme.restrict_functor AlgebraicGeometry.SchemeCat.restrictFunctor

@[reassoc.1]
theorem SchemeCat.restrict_functor_map_of_restrict {U V : Opens X.carrier} (i : U ⟶ V) :
    (X.restrictFunctor.map i).1 ≫ X.of_restrict _ = X.of_restrict _ :=
  IsOpenImmersion.lift_fac _ _ _
#align
  algebraic_geometry.Scheme.restrict_functor_map_of_restrict AlgebraicGeometry.SchemeCat.restrict_functor_map_of_restrict

theorem SchemeCat.restrict_functor_map_base {U V : Opens X.carrier} (i : U ⟶ V) :
    (X.restrictFunctor.map i).1.1.base = (Opens.toTop _).map i :=
  by
  ext a
  exact
    (congr_arg (fun f : X.restrict U.open_embedding ⟶ X => f.1.base a)
        (X.restrict_functor_map_of_restrict i) :
      _)
#align
  algebraic_geometry.Scheme.restrict_functor_map_base AlgebraicGeometry.SchemeCat.restrict_functor_map_base

theorem SchemeCat.restrict_functor_map_app_aux {U V : Opens X.carrier} (i : U ⟶ V) (W : Opens V) :
    U.OpenEmbedding.IsOpenMap.Functor.obj ((Opens.map (X.restrictFunctor.map i).1.val.base).obj W) ≤
      V.OpenEmbedding.IsOpenMap.Functor.obj W :=
  by
  simp only [Set.image_congr, Subtype.mk_le_mk, IsOpenMap.functor, Set.image_subset_iff,
    Scheme.restrict_functor_map_base, opens.map, Subtype.coe_mk, opens.inclusion_apply,
    Set.le_eq_subset]
  rintro _ h
  exact ⟨_, h, rfl⟩
#align
  algebraic_geometry.Scheme.restrict_functor_map_app_aux AlgebraicGeometry.SchemeCat.restrict_functor_map_app_aux

theorem SchemeCat.restrict_functor_map_app {U V : Opens X.carrier} (i : U ⟶ V) (W : Opens V) :
    (X.restrictFunctor.map i).1.1.c.app (op W) =
      X.Presheaf.map (hom_of_le <| X.restrict_functor_map_app_aux i W).op :=
  by
  have e₁ :=
    Scheme.congr_app (X.restrict_functor_map_of_restrict i)
      (op <| V.open_embedding.is_open_map.functor.obj W)
  rw [Scheme.comp_val_c_app] at e₁
  have e₂ := (X.restrict_functor.map i).1.val.c.naturality (eq_to_hom W.map_functor_eq).op
  rw [← is_iso.eq_inv_comp] at e₂
  dsimp at e₁ e₂⊢
  rw [e₂, W.adjunction_counit_map_functor, ← is_iso.eq_inv_comp, is_iso.inv_comp_eq, ←
    is_iso.eq_comp_inv] at e₁
  simp_rw [eq_to_hom_map (opens.map _), eq_to_hom_map (IsOpenMap.functor _), ← functor.map_inv, ←
    functor.map_comp] at e₁
  rw [e₁]
  congr 1
#align
  algebraic_geometry.Scheme.restrict_functor_map_app AlgebraicGeometry.SchemeCat.restrict_functor_map_app

/-- The functor that restricts to open subschemes and then takes global section is
isomorphic to the structure sheaf. -/
@[simps]
def SchemeCat.restrictFunctorΓ :
    X.restrictFunctor.op ⋙ (Over.forget X).op ⋙ Scheme.Γ ≅ X.Presheaf :=
  NatIso.ofComponents
    (fun U => X.Presheaf.mapIso ((eqToIso (unop U).open_embedding_obj_top).symm.op : _))
    (by
      intro U V i
      dsimp [-Subtype.val_eq_coe, -Scheme.restrict_functor_map_left]
      rw [X.restrict_functor_map_app, ← functor.map_comp, ← functor.map_comp]
      congr 1)
#align algebraic_geometry.Scheme.restrict_functor_Γ AlgebraicGeometry.SchemeCat.restrictFunctorΓ

end

/-- The restriction of an isomorphism onto an open set. -/
noncomputable abbrev SchemeCat.restrictMapIso {X Y : SchemeCat} (f : X ⟶ Y) [IsIso f]
    (U : Opens Y.carrier) :
    X.restrict ((Opens.map f.1.base).obj U).OpenEmbedding ≅ Y.restrict U.OpenEmbedding :=
  by
  refine' is_open_immersion.iso_of_range_eq (X.of_restrict _ ≫ f) (Y.of_restrict _) _
  dsimp [opens.inclusion]
  rw [coe_comp, Set.range_comp]
  dsimp
  rw [Subtype.range_coe, Subtype.range_coe]
  refine' @Set.image_preimage_eq _ _ f.1.base U.1 _
  rw [← TopCat.epi_iff_surjective]
  infer_instance
#align algebraic_geometry.Scheme.restrict_map_iso AlgebraicGeometry.SchemeCat.restrictMapIso

/-- Given an open cover on `X`, we may pull them back along a morphism `W ⟶ X` to obtain
an open cover of `W`. -/
@[simps]
def SchemeCat.OpenCover.pullbackCover {X : SchemeCat} (𝒰 : X.OpenCover) {W : SchemeCat}
    (f : W ⟶ X) : W.OpenCover where
  J := 𝒰.J
  obj x := pullback f (𝒰.map x)
  map x := pullback.fst
  f x := 𝒰.f (f.1.base x)
  Covers x :=
    by
    rw [←
      show _ = (pullback.fst : pullback f (𝒰.map (𝒰.f (f.1.base x))) ⟶ _).1.base from
        preserves_pullback.iso_hom_fst Scheme.forget_to_Top f (𝒰.map (𝒰.f (f.1.base x)))]
    rw [coe_comp, Set.range_comp, set.range_iff_surjective.mpr, Set.image_univ,
      TopCat.pullback_fst_range]
    obtain ⟨y, h⟩ := 𝒰.covers (f.1.base x)
    exact ⟨y, h.symm⟩
    · rw [← TopCat.epi_iff_surjective]
      infer_instance
#align
  algebraic_geometry.Scheme.open_cover.pullback_cover AlgebraicGeometry.SchemeCat.OpenCover.pullbackCover

theorem SchemeCat.OpenCover.Union_range {X : SchemeCat} (𝒰 : X.OpenCover) :
    (⋃ i, Set.range (𝒰.map i).1.base) = Set.univ :=
  by
  rw [Set.eq_univ_iff_forall]
  intro x
  rw [Set.mem_unionᵢ]
  exact ⟨𝒰.f x, 𝒰.covers x⟩
#align
  algebraic_geometry.Scheme.open_cover.Union_range AlgebraicGeometry.SchemeCat.OpenCover.Union_range

theorem SchemeCat.OpenCover.supr_opens_range {X : SchemeCat} (𝒰 : X.OpenCover) :
    (⨆ i, (𝒰.map i).opensRange) = ⊤ :=
  opens.ext <| by
    rw [opens.coe_supr]
    exact 𝒰.Union_range
#align
  algebraic_geometry.Scheme.open_cover.supr_opens_range AlgebraicGeometry.SchemeCat.OpenCover.supr_opens_range

theorem SchemeCat.OpenCover.compact_space {X : SchemeCat} (𝒰 : X.OpenCover) [Finite 𝒰.J]
    [H : ∀ i, CompactSpace (𝒰.obj i).carrier] : CompactSpace X.carrier :=
  by
  cases nonempty_fintype 𝒰.J
  rw [← is_compact_univ_iff, ← 𝒰.Union_range]
  apply is_compact_Union
  intro i
  rw [is_compact_iff_compact_space]
  exact
    @Homeomorph.compact_space _ _ (H i)
      (TopCat.homeoOfIso
        (as_iso
          (is_open_immersion.iso_of_range_eq (𝒰.map i)
                  (X.of_restrict (opens.open_embedding ⟨_, (𝒰.is_open i).base_open.open_range⟩))
                  subtype.range_coe.symm).Hom.1.base))
#align
  algebraic_geometry.Scheme.open_cover.compact_space AlgebraicGeometry.SchemeCat.OpenCover.compact_space

/-- Given open covers `{ Uᵢ }` and `{ Uⱼ }`, we may form the open cover `{ Uᵢ ∩ Uⱼ }`. -/
def SchemeCat.OpenCover.inter {X : SchemeCat.{u}} (𝒰₁ : SchemeCat.OpenCover.{v₁} X)
    (𝒰₂ : SchemeCat.OpenCover.{v₂} X) : X.OpenCover
    where
  J := 𝒰₁.J × 𝒰₂.J
  obj ij := pullback (𝒰₁.map ij.1) (𝒰₂.map ij.2)
  map ij := pullback.fst ≫ 𝒰₁.map ij.1
  f x := ⟨𝒰₁.f x, 𝒰₂.f x⟩
  Covers x := by
    rw [is_open_immersion.range_pullback_to_base_of_left]
    exact ⟨𝒰₁.covers x, 𝒰₂.covers x⟩
#align algebraic_geometry.Scheme.open_cover.inter AlgebraicGeometry.SchemeCat.OpenCover.inter

/-- If `U` is a family of open sets that covers `X`, then `X.restrict U` forms an `X.open_cover`. -/
@[simps J obj map]
def SchemeCat.openCoverOfSuprEqTop {s : Type _} (X : SchemeCat) (U : s → Opens X.carrier)
    (hU : (⨆ i, U i) = ⊤) : X.OpenCover where
  J := s
  obj i := X.restrict (U i).OpenEmbedding
  map i := X.of_restrict (U i).OpenEmbedding
  f x :=
    haveI : x ∈ ⨆ i, U i := hU.symm ▸ show x ∈ (⊤ : opens X.carrier) by triv
    (opens.mem_supr.mp this).some
  Covers x := by
    erw [Subtype.range_coe]
    have : x ∈ ⨆ i, U i := hU.symm ▸ show x ∈ (⊤ : opens X.carrier) by triv
    exact (opens.mem_supr.mp this).some_spec
#align
  algebraic_geometry.Scheme.open_cover_of_supr_eq_top AlgebraicGeometry.SchemeCat.openCoverOfSuprEqTop

section MorphismRestrict

/-- Given a morphism `f : X ⟶ Y` and an open set `U ⊆ Y`, we have `X ×[Y] U ≅ X |_{f ⁻¹ U}` -/
def pullbackRestrictIsoRestrict {X Y : SchemeCat} (f : X ⟶ Y) (U : Opens Y.carrier) :
    pullback f (Y.of_restrict U.OpenEmbedding) ≅
      X.restrict ((Opens.map f.1.base).obj U).OpenEmbedding :=
  by
  refine' is_open_immersion.iso_of_range_eq pullback.fst (X.of_restrict _) _
  rw [is_open_immersion.range_pullback_fst_of_right]
  dsimp [opens.inclusion]
  rw [Subtype.range_coe, Subtype.range_coe]
  rfl
#align
  algebraic_geometry.pullback_restrict_iso_restrict AlgebraicGeometry.pullbackRestrictIsoRestrict

@[simp, reassoc.1]
theorem pullback_restrict_iso_restrict_inv_fst {X Y : SchemeCat} (f : X ⟶ Y) (U : Opens Y.carrier) :
    (pullbackRestrictIsoRestrict f U).inv ≫ pullback.fst = X.of_restrict _ :=
  by
  delta pullback_restrict_iso_restrict
  simp
#align
  algebraic_geometry.pullback_restrict_iso_restrict_inv_fst AlgebraicGeometry.pullback_restrict_iso_restrict_inv_fst

@[simp, reassoc.1]
theorem pullback_restrict_iso_restrict_hom_restrict {X Y : SchemeCat} (f : X ⟶ Y)
    (U : Opens Y.carrier) :
    (pullbackRestrictIsoRestrict f U).Hom ≫ X.of_restrict _ = pullback.fst :=
  by
  delta pullback_restrict_iso_restrict
  simp
#align
  algebraic_geometry.pullback_restrict_iso_restrict_hom_restrict AlgebraicGeometry.pullback_restrict_iso_restrict_hom_restrict

/-- The restriction of a morphism `X ⟶ Y` onto `X |_{f ⁻¹ U} ⟶ Y |_ U`. -/
def morphismRestrict {X Y : SchemeCat} (f : X ⟶ Y) (U : Opens Y.carrier) :
    X.restrict ((Opens.map f.1.base).obj U).OpenEmbedding ⟶ Y.restrict U.OpenEmbedding :=
  (pullbackRestrictIsoRestrict f U).inv ≫ pullback.snd
#align algebraic_geometry.morphism_restrict AlgebraicGeometry.morphismRestrict

-- mathport name: «expr ∣_ »
infixl:80 " ∣_ " => morphismRestrict

@[simp, reassoc.1]
theorem pullback_restrict_iso_restrict_hom_morphism_restrict {X Y : SchemeCat} (f : X ⟶ Y)
    (U : Opens Y.carrier) : (pullbackRestrictIsoRestrict f U).Hom ≫ f ∣_ U = pullback.snd :=
  Iso.hom_inv_id_assoc _ _
#align
  algebraic_geometry.pullback_restrict_iso_restrict_hom_morphism_restrict AlgebraicGeometry.pullback_restrict_iso_restrict_hom_morphism_restrict

@[simp, reassoc.1]
theorem morphism_restrict_ι {X Y : SchemeCat} (f : X ⟶ Y) (U : Opens Y.carrier) :
    (f ∣_ U) ≫ Y.of_restrict U.OpenEmbedding = X.of_restrict _ ≫ f :=
  by
  delta morphism_restrict
  rw [category.assoc, pullback.condition.symm, pullback_restrict_iso_restrict_inv_fst_assoc]
#align algebraic_geometry.morphism_restrict_ι AlgebraicGeometry.morphism_restrict_ι

theorem isPullbackMorphismRestrict {X Y : SchemeCat} (f : X ⟶ Y) (U : Opens Y.carrier) :
    IsPullback (f ∣_ U) (X.of_restrict _) (Y.of_restrict _) f :=
  by
  delta morphism_restrict
  nth_rw 1 [← category.id_comp f]
  refine'
    (is_pullback.of_horiz_is_iso ⟨_⟩).pasteHoriz
      (is_pullback.of_has_pullback f (Y.of_restrict U.open_embedding)).flip
  rw [pullback_restrict_iso_restrict_inv_fst, category.comp_id]
#align algebraic_geometry.is_pullback_morphism_restrict AlgebraicGeometry.isPullbackMorphismRestrict

theorem morphism_restrict_comp {X Y Z : SchemeCat} (f : X ⟶ Y) (g : Y ⟶ Z) (U : Opens Z.carrier) :
    (f ≫ g) ∣_ U = ((f ∣_ (Opens.map g.val.base).obj U) ≫ g ∣_ U : _) :=
  by
  delta morphism_restrict
  rw [← pullback_right_pullback_fst_iso_inv_snd_snd]
  simp_rw [← category.assoc]
  congr 1
  rw [← cancel_mono pullback.fst]
  simp_rw [category.assoc]
  rw [pullback_restrict_iso_restrict_inv_fst, pullback_right_pullback_fst_iso_inv_snd_fst, ←
    pullback.condition, pullback_restrict_iso_restrict_inv_fst_assoc,
    pullback_restrict_iso_restrict_inv_fst_assoc]
  rfl
  infer_instance
#align algebraic_geometry.morphism_restrict_comp AlgebraicGeometry.morphism_restrict_comp

instance {X Y : SchemeCat} (f : X ⟶ Y) [IsIso f] (U : Opens Y.carrier) : IsIso (f ∣_ U) :=
  by
  delta morphism_restrict
  infer_instance

theorem morphism_restrict_base_coe {X Y : SchemeCat} (f : X ⟶ Y) (U : Opens Y.carrier) (x) :
    @coe U Y.carrier _ ((f ∣_ U).1.base x) = f.1.base x.1 :=
  congr_arg (fun f => PresheafedSpaceCat.Hom.base (LocallyRingedSpaceCat.Hom.val f) x)
    (morphism_restrict_ι f U)
#align algebraic_geometry.morphism_restrict_base_coe AlgebraicGeometry.morphism_restrict_base_coe

theorem morphism_restrict_val_base {X Y : SchemeCat} (f : X ⟶ Y) (U : Opens Y.carrier) :
    ⇑(f ∣_ U).1.base = U.1.restrictPreimage f.1.base :=
  funext fun x => Subtype.ext (morphism_restrict_base_coe f U x)
#align algebraic_geometry.morphism_restrict_val_base AlgebraicGeometry.morphism_restrict_val_base

theorem image_morphism_restrict_preimage {X Y : SchemeCat} (f : X ⟶ Y) (U : Opens Y.carrier)
    (V : Opens U) :
    ((Opens.map f.val.base).obj U).OpenEmbedding.IsOpenMap.Functor.obj
        ((Opens.map (f ∣_ U).val.base).obj V) =
      (Opens.map f.val.base).obj (U.OpenEmbedding.IsOpenMap.Functor.obj V) :=
  by
  ext1
  ext x
  constructor
  · rintro ⟨⟨x, hx⟩, hx' : (f ∣_ U).1.base _ ∈ _, rfl⟩
    refine' ⟨⟨_, hx⟩, _, rfl⟩
    convert hx'
    ext1
    exact (morphism_restrict_base_coe f U ⟨x, hx⟩).symm
  · rintro ⟨⟨x, hx⟩, hx', rfl : x = _⟩
    refine' ⟨⟨_, hx⟩, (_ : (f ∣_ U).1.base ⟨x, hx⟩ ∈ V.1), rfl⟩
    convert hx'
    ext1
    exact morphism_restrict_base_coe f U ⟨x, hx⟩
#align
  algebraic_geometry.image_morphism_restrict_preimage AlgebraicGeometry.image_morphism_restrict_preimage

theorem morphism_restrict_c_app {X Y : SchemeCat} (f : X ⟶ Y) (U : Opens Y.carrier) (V : Opens U) :
    (f ∣_ U).1.c.app (op V) =
      f.1.c.app (op (U.OpenEmbedding.IsOpenMap.Functor.obj V)) ≫
        X.Presheaf.map (eqToHom (image_morphism_restrict_preimage f U V)).op :=
  by
  have :=
    Scheme.congr_app (morphism_restrict_ι f U) (op (U.open_embedding.is_open_map.functor.obj V))
  rw [Scheme.comp_val_c_app, Scheme.comp_val_c_app_assoc] at this
  have e : (opens.map U.inclusion).obj (U.open_embedding.is_open_map.functor.obj V) = V :=
    by
    ext1
    exact Set.preimage_image_eq _ Subtype.coe_injective
  have : _ ≫ X.presheaf.map _ = _ :=
    (((f ∣_ U).1.c.naturality (eq_to_hom e).op).symm.trans _).trans this
  swap
  · change Y.presheaf.map _ ≫ _ = Y.presheaf.map _ ≫ _
    congr
  rw [← is_iso.eq_comp_inv, ← functor.map_inv, category.assoc] at this
  rw [this]
  congr 1
  erw [← X.presheaf.map_comp, ← X.presheaf.map_comp]
  congr 1
#align algebraic_geometry.morphism_restrict_c_app AlgebraicGeometry.morphism_restrict_c_app

theorem Γ_map_morphism_restrict {X Y : SchemeCat} (f : X ⟶ Y) (U : Opens Y.carrier) :
    SchemeCat.Γ.map (f ∣_ U).op =
      Y.Presheaf.map (eq_to_hom <| U.open_embedding_obj_top.symm).op ≫
        f.1.c.app (op U) ≫
          X.Presheaf.map (eq_to_hom <| ((Opens.map f.val.base).obj U).open_embedding_obj_top).op :=
  by
  rw [Scheme.Γ_map_op, morphism_restrict_c_app f U ⊤, f.val.c.naturality_assoc]
  erw [← X.presheaf.map_comp]
  congr
#align algebraic_geometry.Γ_map_morphism_restrict AlgebraicGeometry.Γ_map_morphism_restrict

/-- Restricting a morphism onto the the image of an open immersion is isomorphic to the base change
along the immersion. -/
def morphismRestrictOpensRange {X Y U : SchemeCat} (f : X ⟶ Y) (g : U ⟶ Y)
    [hg : IsOpenImmersion g] :
    Arrow.mk (f ∣_ g.opensRange) ≅ Arrow.mk (pullback.snd : pullback f g ⟶ _) :=
  by
  let V : opens Y.carrier := g.opens_range
  let e :=
    is_open_immersion.iso_of_range_eq g (Y.of_restrict V.open_embedding) subtype.range_coe.symm
  let t : pullback f g ⟶ pullback f (Y.of_restrict V.open_embedding) :=
    pullback.map _ _ _ _ (𝟙 _) e.hom (𝟙 _) (by rw [category.comp_id, category.id_comp])
      (by rw [category.comp_id, is_open_immersion.iso_of_range_eq_hom, is_open_immersion.lift_fac])
  symm
  refine' arrow.iso_mk (as_iso t ≪≫ pullback_restrict_iso_restrict f V) e _
  rw [iso.trans_hom, as_iso_hom, ← iso.comp_inv_eq, ← cancel_mono g, arrow.mk_hom, arrow.mk_hom,
    is_open_immersion.iso_of_range_eq_inv, category.assoc, category.assoc, category.assoc,
    is_open_immersion.lift_fac, ← pullback.condition, morphism_restrict_ι,
    pullback_restrict_iso_restrict_hom_restrict_assoc, pullback.lift_fst_assoc, category.comp_id]
#align algebraic_geometry.morphism_restrict_opens_range AlgebraicGeometry.morphismRestrictOpensRange

/-- The restrictions onto two equal open sets are isomorphic. This currently has bad defeqs when
unfolded, but it should not matter for now. Replace this definition if better defeqs are needed. -/
def morphismRestrictEq {X Y : SchemeCat} (f : X ⟶ Y) {U V : Opens Y.carrier} (e : U = V) :
    Arrow.mk (f ∣_ U) ≅ Arrow.mk (f ∣_ V) :=
  eqToIso (by subst e)
#align algebraic_geometry.morphism_restrict_eq AlgebraicGeometry.morphismRestrictEq

/-- Restricting a morphism twice is isomorpic to one restriction. -/
def morphismRestrictRestrict {X Y : SchemeCat} (f : X ⟶ Y) (U : Opens Y.carrier) (V : Opens U) :
    Arrow.mk (f ∣_ U ∣_ V) ≅ Arrow.mk (f ∣_ U.OpenEmbedding.IsOpenMap.Functor.obj V) :=
  by
  have :
    (f ∣_ U ∣_ V) ≫ (iso.refl _).Hom =
      (as_iso <|
            (pullback_restrict_iso_restrict (f ∣_ U) V).inv ≫
              (pullback_symmetry _ _).Hom ≫
                pullback.map _ _ _ _ (𝟙 _)
                    ((pullback_restrict_iso_restrict f U).inv ≫ (pullback_symmetry _ _).Hom) (𝟙 _)
                    ((category.comp_id _).trans (category.id_comp _).symm) (by simpa) ≫
                  (pullback_right_pullback_fst_iso _ _ _).Hom ≫ (pullback_symmetry _ _).Hom).Hom ≫
        pullback.snd :=
    by
    simpa only [category.comp_id, pullback_right_pullback_fst_iso_hom_fst, iso.refl_hom,
      category.assoc, pullback_symmetry_hom_comp_snd, as_iso_hom, pullback.lift_fst,
      pullback_symmetry_hom_comp_fst]
  refine'
    arrow.iso_mk' _ _ _ _ this.symm ≪≫
      (morphism_restrict_opens_range _ _).symm ≪≫ morphism_restrict_eq _ _
  ext1
  dsimp
  rw [coe_comp, Set.range_comp]
  congr
  exact Subtype.range_coe
#align algebraic_geometry.morphism_restrict_restrict AlgebraicGeometry.morphismRestrictRestrict

/-- Restricting a morphism twice onto a basic open set is isomorphic to one restriction.  -/
def morphismRestrictRestrictBasicOpen {X Y : SchemeCat} (f : X ⟶ Y) (U : Opens Y.carrier)
    (r : Y.Presheaf.obj (op U)) :
    Arrow.mk
        (f ∣_ U ∣_
          (Y.restrict _).basicOpen (Y.Presheaf.map (eqToHom U.open_embedding_obj_top).op r)) ≅
      Arrow.mk (f ∣_ Y.basicOpen r) :=
  by
  refine' morphism_restrict_restrict _ _ _ ≪≫ morphism_restrict_eq _ _
  have e := Scheme.preimage_basic_open (Y.of_restrict U.open_embedding) r
  erw [Scheme.of_restrict_val_c_app, opens.adjunction_counit_app_self, eq_to_hom_op] at e
  rw [← (Y.restrict U.open_embedding).basic_open_res_eq _ (eq_to_hom U.inclusion_map_eq_top).op, ←
    comp_apply]
  erw [← Y.presheaf.map_comp]
  rw [eq_to_hom_op, eq_to_hom_op, eq_to_hom_map, eq_to_hom_trans]
  erw [← e]
  ext1; dsimp [opens.map, opens.inclusion]
  rw [Set.image_preimage_eq_inter_range, Set.inter_eq_left_iff_subset, Subtype.range_coe]
  exact Y.basic_open_le r
#align
  algebraic_geometry.morphism_restrict_restrict_basic_open AlgebraicGeometry.morphismRestrictRestrictBasicOpen

/-- The stalk map of a restriction of a morphism is isomorphic to the stalk map of the original map.
-/
def morphismRestrictStalkMap {X Y : SchemeCat} (f : X ⟶ Y) (U : Opens Y.carrier) (x) :
    Arrow.mk (PresheafedSpaceCat.stalkMap (f ∣_ U).1 x) ≅
      Arrow.mk (PresheafedSpaceCat.stalkMap f.1 x.1) :=
  by
  fapply arrow.iso_mk'
  · refine' Y.restrict_stalk_iso U.open_embedding ((f ∣_ U).1 x) ≪≫ TopCat.Presheaf.stalkCongr _ _
    apply Inseparable.of_eq
    exact morphism_restrict_base_coe f U x
  · exact X.restrict_stalk_iso _ _
  · apply TopCat.Presheaf.stalk_hom_ext
    intro V hxV
    simp only [TopCat.Presheaf.stalk_congr_hom, CategoryTheory.Category.assoc,
      CategoryTheory.Iso.trans_hom]
    erw [PresheafedSpace.restrict_stalk_iso_hom_eq_germ_assoc]
    erw [PresheafedSpace.stalk_map_germ_assoc _ _ ⟨_, _⟩]
    rw [TopCat.Presheaf.germ_stalk_specializes'_assoc]
    erw [PresheafedSpace.stalk_map_germ _ _ ⟨_, _⟩]
    erw [PresheafedSpace.restrict_stalk_iso_hom_eq_germ]
    rw [morphism_restrict_c_app, category.assoc, TopCat.Presheaf.germ_res]
    rfl
#align algebraic_geometry.morphism_restrict_stalk_map AlgebraicGeometry.morphismRestrictStalkMap

instance {X Y : SchemeCat} (f : X ⟶ Y) (U : Opens Y.carrier) [IsOpenImmersion f] :
    IsOpenImmersion (f ∣_ U) := by
  delta morphism_restrict
  infer_instance

end MorphismRestrict

end AlgebraicGeometry

